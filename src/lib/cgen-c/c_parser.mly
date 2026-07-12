%{
  module T = Type

  let loc = Parse_state.loc

  (* A declarator is a declared name (absent for abstract declarators)
     plus a function that wraps the declaration's base type into the full
     type, threading the pointer/array/function layers outward-to-inward
     (the C "spiral rule"). *)
  type 'a dcl = string option * ('a T.t -> 'a T.t)

  let did name : 'a dcl = Some name, Fun.id

  type qual = [
    | `const
    | `volatile
    | `restrict
  ]

  let cv_of_quals qs =
    List.fold_left
      (fun acc -> function
        | `const -> T.Cv.combine acc T.Cv.const
        | `volatile -> T.Cv.combine acc T.Cv.volatile
        | `restrict -> acc)
      T.Cv.empty qs

  let restrict_of_quals qs = List.exists (fun q -> q = `restrict) qs

  let ptr_of_quals qs t =
    T.ptr ~cv:(cv_of_quals qs) ~restrict:(restrict_of_quals qs) t

  (* Arithmetic type-specifier keywords, collected and then resolved into
     a single base type (§6.7.2 ¶2). *)
  type akw =
    | AKvoid
    | AKchar
    | AKshort
    | AKint
    | AKlong
    | AKfloat
    | AKdouble
    | AKsigned
    | AKunsigned
    | AKbool

  let make_arith atoms =
    let count x = List.length (List.filter (fun a -> a = x) atoms) in
    let has x = List.exists (fun a -> a = x) atoms in
    let sign = if has AKunsigned then T.Sunsigned else T.Ssigned in
    if has AKvoid then T.void ()
    else if has AKbool then T.bool_ ()
    else if has AKdouble then T.double_ ()
    else if has AKfloat then T.float_ ()
    else if has AKchar then
      if has AKsigned then T.char_ T.Ssigned
      else if has AKunsigned then T.char_ T.Sunsigned
      else T.plain_char_ ()
    else if has AKshort then T.short_ ~sign ()
    else if count AKlong >= 2 then T.longlong_ ~sign ()
    else if has AKlong then T.long_ ~sign ()
    else T.int_ ~sign ()

  (* Declaration modifiers: everything in a declaration-specifier list
     that isn't the type specifier itself. *)

  type raw_attrs = Cgen_utils.Location.t Attr.raws

  type modat =
    | Mstore of Stmt.storagecls
    | Mtypedef
    | Minline
    | Mtls
    | Mqual of qual
    | Mattrs of raw_attrs

  type mods = {
    storage    : Stmt.storagecls;
    is_typedef : bool;
    is_inline  : bool;
    is_tls     : bool;
    cv         : T.cv;
    attrs      : raw_attrs;
  }

  let default_mods = {
    storage = Stmt.SCdefault;
    is_typedef = false;
    is_inline = false;
    is_tls = false;
    cv = T.Cv.empty;
    attrs = [];
  }

  let resolve_mods ms =
    List.fold_left
      (fun m -> function
        | Mstore s -> {m with storage = s}
        | Mtypedef -> {m with is_typedef = true}
        | Minline -> {m with is_inline = true}
        | Mtls -> {m with is_tls = true}
        | Mattrs a -> {m with attrs = m.attrs @ a}
        | Mqual `const -> {m with cv = T.Cv.combine m.cv T.Cv.const}
        | Mqual `volatile -> {m with cv = T.Cv.combine m.cv T.Cv.volatile}
        | Mqual `restrict -> m)
      default_mods ms

  let apply_base_cv cv base = T.with_cv (T.Cv.combine cv (T.cv_of base)) base

  (* `(void)` denotes a zero-parameter prototype, distinct from a single
     parameter of type void. *)
  let normalize_params ps = match ps with
    | [({T.pname = None; ptype} : _ T.param)] when T.is_void ptype -> []
    | _ -> ps

  let params_to_decl ps =
    List.map (fun (p : _ T.param) -> Decl.param ?name:p.pname ~ty:p.ptype ()) ps

  (* Build the top-level declarations of one C declaration: the base type
     applied through each init-declarator. A declarator whose full type is
     a function (and isn't a typedef) becomes a function prototype. *)
  let make_decls ~ann mods base extra idecls =
    let base = apply_base_cv mods.cv base in
    let one ((nameopt, dty), init, dattrs) =
      let attrs = mods.attrs @ dattrs in
      let ty = dty base in
      let name = match nameopt with
        | Some n -> n
        | None -> "" in
      if mods.is_typedef then Decl.of_tydecl (Tydecl.typedef ~name ~ty ~ann)
      else match ty with
        | T.Tfun {result; params; variadic} ->
          let params = match params with
            | Some ps -> params_to_decl ps
            | None -> [] in
          Decl.fun_ ~name ~params ~variadic ~ret:result
            ~storage:mods.storage ~inline:mods.is_inline
            ~attrs ~ann ()
        | _ ->
          Decl.var ~name ~ty ?init ~storage:mods.storage
            ~tls:mods.is_tls ~attrs ~ann () in
    List.map Decl.of_tydecl extra @ List.map one idecls

  (* Build a struct/union definition from its body and attributes (shared by
     the leading- and trailing-attribute forms of the specifier). *)
  let make_compound ~su ~name ~body ~attrs ~ann =
    let fields, nested = body in
    let tag = match name with
      | Some n -> n
      | None -> Parse_state.fresh_anon_tag @@ match su with
        | `struct_ -> "struct"
        | `union -> "union" in
    let ty = match su with
      | `struct_ -> T.struct_ tag
      | `union -> T.union_ tag in
    let def = Tydecl.compound ~kind:su ~tag ~fields:(Some fields) ~attrs ~ann () in
    ty, nested @ [def]

  (* A bare `struct S;` or `union U;` (a specifier with a tag but no body and
     no declarator) forward-declares the tag as an incomplete type. *)
  let incomplete_tag ~ann t = match (t : _ T.t) with
    | T.Tnamed {kind = #T.compound as kind; name; _} ->
      [Tydecl.compound ~kind ~tag:name ~fields:None ~ann ()]
    | _ -> []

  (* Register a declared name with the lexer hack at the moment its
     declarator is reduced (before the terminating `;`), so a following
     use of a freshly-introduced typedef name is lexed correctly. *)
  let register_name nameopt = match nameopt with
    | None -> ()
    | Some n ->
      if !Parse_state.cur_typedef
      then Lexer_hack.define_typedef n
      else Lexer_hack.define_var n

  (* Abbreviations for the `%type` declarations below. The whole grammar
     is uniformly annotated with `Cgen_utils.Location.t`; array sizes and other
     type-embedded expressions therefore carry `Cgen_utils.Location.t Expr.t`.

     `Cgen_utils.Location.t` is spelled out rather than aliased so that the type
     menhir infers for the start symbol (the only one leaking into the
     generated `.mli`) stays a fully-qualified `Cgen_utils.Location.t Cunit.t`
  *)

  type expr = Cgen_utils.Location.t Expr.t

  (* A parsed type *)
  type ty = Cgen_utils.Location.t Expr.ty

  type decl = Cgen_utils.Location.t Decl.t
  type tydecl = Cgen_utils.Location.t Tydecl.t
  type stmt = Cgen_utils.Location.t Stmt.t
  type field = Cgen_utils.Location.t Tydecl.field
  type eitem = Cgen_utils.Location.t Tydecl.eitem
  type param = Cgen_utils.Location.t Expr.t T.param
  type init = Cgen_utils.Location.t Expr.init
  type designator = Cgen_utils.Location.t Expr.designator
  type blkitem = Cgen_utils.Location.t Stmt.blkitem
  type forinit = Cgen_utils.Location.t Stmt.forinit

  (* A (possibly named) declarator *)
  type declr = Cgen_utils.Location.t Expr.t dcl

  (* An abstract declarator *)
  type adeclr = ty -> ty
%}

%token <string> IDENT TYPEDEF_NAME STRING
%token <Expr.const> CONSTANT
(* `BUILTIN` carries the full `__builtin_*` spelling of a builtin call. *)
%token <string> BUILTIN

%token AUTO BREAK CASE CHAR CONST CONTINUE DEFAULT DO DOUBLE ELSE ENUM
%token EXTERN FLOAT FOR GOTO IF INLINE INT LONG REGISTER RESTRICT RETURN
%token SHORT SIGNED SIZEOF STATIC STRUCT SWITCH TYPEDEF UNION UNSIGNED
%token VOID VOLATILE WHILE BOOL NORETURN THREAD_LOCAL
%token ATTRIBUTE ALIGNOF ALIGNAS

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token SEMI COMMA DOT ARROW ELLIPSIS COLON QUESTION
%token ASSIGN ADD_ASSIGN SUB_ASSIGN MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN
%token AND_ASSIGN OR_ASSIGN XOR_ASSIGN SHL_ASSIGN SHR_ASSIGN
%token PLUS MINUS STAR SLASH PERCENT AMP PIPE CARET TILDE SHL SHR
%token ANDAND OROR BANG EQ NE LT GT LE GE INCR DECR
%token EOF

(* Resolve the dangling-else ambiguity by binding `else` to the nearest
   `if` (shift over reduce). *)
%nonassoc below_ELSE
%nonassoc ELSE

(* Resolve the C parameter-declaration ambiguity in `T ( U ... )`.

   When `U` is a typedef name, `(U ...)` is an abstract declarator in which `U`
   is a type (C11 §6.7.6.3 ¶11 says an identifier that could be a typedef name
   or a parameter name is taken as the typedef name), not a parenthesized
   declarator naming a parameter `U`.

   The choice surfaces as a shift/reduce conflict on TYPEDEF_NAME between
   shifting it as a `declared_name` and reducing the (empty) modifier list that
   begins the nested type.

   Giving that reduction higher precedence than the shift selects the type
   interpretation. This is the grammar's only conflict, so the precedence is
   inert everywhere else.
*)
%nonassoc TYPEDEF_NAME
%nonassoc prec_abstract_param

%start <Cgen_utils.Location.t Cunit.t> translation_unit

(* Nonterminal types. *)

%type <decl list> external_declaration
%type <(declr * init option * raw_attrs) list> init_declarator_list
%type <declr * init option * raw_attrs> init_declarator

%type <Lexing.position * modat list * ty * tydecl list> declaration_specifiers
%type <modat> declaration_modifier storage_class
%type <qual> type_qualifier
%type <ty * tydecl list> type_part struct_or_union_specifier enum_specifier specifier_qualifier_list
%type <akw> arith_keyword

%type <Type.compound> struct_or_union
%type <string> tag_name declared_name field_name
%type <field list * tydecl list> struct_declaration_list struct_declaration
%type <declr * expr option * raw_attrs> struct_declarator
%type <eitem list> enumerator_list
%type <eitem> enumerator

%type <declr> declarator direct_declarator
%type <adeclr> pointer abstract_declarator direct_abstract_declarator
%type <param list * bool> parameter_type_list parameter_list
%type <param> parameter_declaration
%type <ty> type_name

%type <init> c_initializer
%type <(designator list * init) list> initializer_item_list
%type <designator list * init> initializer_item
%type <designator> designator

%type <stmt> statement
%type <stmt> labeled_statement
%type <stmt> compound_statement
%type <stmt> expression_statement
%type <stmt> selection_statement
%type <stmt> iteration_statement
%type <stmt> jump_statement

%type <unit> enter_scope
%type <blkitem list> block_item block_declaration
%type <forinit option> for_init

%type <expr> primary_expression
%type <expr> postfix_expression
%type <expr> unary_expression
%type <expr> cast_expression
%type <expr> multiplicative_expression
%type <expr> additive_expression
%type <expr> shift_expression
%type <expr> relational_expression
%type <expr> equality_expression
%type <expr> and_expression
%type <expr> xor_expression
%type <expr> or_expression
%type <expr> logical_and_expression
%type <expr> logical_or_expression
%type <expr> conditional_expression
%type <expr> assignment_expression
%type <expr> expression
%type <expr> constant_expression

%type <Expr.uop> unary_operator
%type <Expr.bop> mul_op add_op shift_op rel_op eq_op assignment_operator

%%

translation_unit:
  | eds = list(external_declaration) EOF { Cunit.create (List.concat eds) }

(* {1 External declarations} *)

external_declaration:
  | ds = declaration_specifiers SEMI
    {
      let _, mods, base, extra = ds in
      let _ = resolve_mods mods in
      let items =
        if List.is_empty extra
        then incomplete_tag ~ann:(loc $symbolstartpos $endpos) base
        else extra in
      List.map Decl.of_tydecl items
    }
  | ds = declaration_specifiers d = declarator dattrs = attribute_specifier_list body = compound_statement
    {
      let sp, mods, base, extra = ds in
      let m = resolve_mods mods in
      let attrs = m.attrs @ dattrs in
      let base = apply_base_cv m.cv base in
      let nameopt, dty = d in
      let name = match nameopt with
        | Some n -> n
        | None -> "" in
      let ann = loc sp $endpos in
      let decl = match dty base with
        | T.Tfun {result; params; variadic} ->
           let params = match params with
             | Some ps -> params_to_decl ps
             | None -> [] in
           Decl.fun_
             ~name ~params ~variadic ~ret:result ~body
             ~storage:m.storage ~inline:m.is_inline
             ~attrs ~ann ()
        | _ ->
           (* A non-function declarator with a brace body is ill-formed.
              Surface it as a zero-arg function so elaboration reports a
              sensible type error rather than the parser crashing. *)
           Decl.fun_
             ~name ~params:[] ~ret:(dty base) ~body
             ~storage:m.storage ~ann
             () in
      List.map Decl.of_tydecl extra @ [decl]
    }
  | ds = declaration_specifiers idecls = init_declarator_list SEMI
    {
      let sp, mods, base, extra = ds in
      make_decls ~ann:(loc sp $endpos) (resolve_mods mods) base extra idecls
    }

init_declarator_list:
  | l = separated_nonempty_list(COMMA, init_declarator) { l }

init_declarator:
  | d = declarator attrs = attribute_specifier_list
    { register_name (fst d); (d, None, attrs) }
  | d = declarator attrs = attribute_specifier_list ASSIGN i = c_initializer
    { register_name (fst d); (d, Some i, attrs) }

(* {1 Declaration specifiers} *)

(* `cur_typedef` must be visible before the init-declarators are reduced,
   so set it as soon as the specifiers are complete. *)
declaration_specifiers:
  | pre = declaration_modifiers tp = type_part post = declaration_modifiers
    {
      let mods = pre @ post in
      Parse_state.cur_typedef :=
        List.exists (function Mtypedef -> true | _ -> false) mods;
      (* `$symbolstartpos` here skips a possibly-empty leading modifier
         list and anchors at the first specifier token, so callers get
         a faithful start position for the declaration (rather than the
        inter-token point that `$startpos` yields after an empty list). *)
      ($symbolstartpos, mods, fst tp, snd tp)
    }

(* An explicit modifier list (rather than `list(declaration_modifier)`) so its
   empty production can carry `%prec prec_abstract_param`, which resolves the
   `T ( U ... )` typedef-name ambiguity in favour of the type interpretation
   (see the precedence declarations above). *)
declaration_modifiers:
  | (* empty *) %prec prec_abstract_param { [] }
  | m = declaration_modifier ms = declaration_modifiers { m :: ms }

declaration_modifier:
  | s = storage_class       { s }
  | TYPEDEF                 { Mtypedef }
  | INLINE                  { Minline }
  | NORETURN                { Mattrs [Attr.raw "noreturn" []] }
  | THREAD_LOCAL            { Mtls }
  | q = type_qualifier      { Mqual q }
  | a = attribute_specifier { Mattrs a }
  (* The C11 alignment specifier `_Alignas(...)` sets the declared object's
     alignment; model it as an `aligned` attribute. `_Alignas(type-name)`
     means the alignment of that type (§6.7.5). *)
  | ALIGNAS LPAREN t = type_name RPAREN
    { Mattrs [Attr.raw "aligned" [Expr.alignof_t t ~ann:(loc $symbolstartpos $endpos)]] }
  | ALIGNAS LPAREN e = constant_expression RPAREN
    { Mattrs [Attr.raw "aligned" [e]] }

(* {1 GNU attributes}

   The basic form is: `__attribute__ (( a1, a2(args), … ))`.

   The doubled parens are part of the syntax. Attribute names may be
   identifiers or keywords (e.g. `const`), and an empty list `(())` is legal.

   Arguments are kept as their C expressions; elaboration folds each to a
   constant.
*)

attribute_specifier_list:
  | l = list(attribute_specifier) { List.concat l }

attribute_specifier:
  | ATTRIBUTE LPAREN LPAREN l = attribute_list RPAREN RPAREN { l }

attribute_list:
  | (* empty *) { [] }
  | l = separated_nonempty_list(COMMA, attribute) { l }

attribute:
  | name = attribute_name { Attr.raw name [] }
  | name = attribute_name LPAREN args = separated_list(COMMA, attribute_arg) RPAREN
    { Attr.raw name args }

attribute_name:
  | id = IDENT        { id }
  | id = TYPEDEF_NAME { id }
  | CONST             { "const" }

attribute_arg:
  | e = assignment_expression { e }

storage_class:
  | AUTO     { Mstore Stmt.SCauto }
  | STATIC   { Mstore Stmt.SCstatic }
  | EXTERN   { Mstore Stmt.SCextern }
  | REGISTER { Mstore Stmt.SCregister }

type_qualifier:
  | CONST    { `const }
  | VOLATILE { `volatile }
  | RESTRICT { `restrict }

(* A type qualifier or `static` inside an array parameter's brackets (C99
   §6.7.6.2): `int a[restrict]`, `char *v[static 3]`, `int m[const 4]`. Both
   are recorded on the array type; the type qualifiers additionally move onto
   the pointer it decays to. *)
array_qualifier:
  | q = type_qualifier { `Qual q }
  | STATIC             { `Static }

(* A type specifier is either a run of arithmetic keywords, a tagged
   type, or a single typedef name.

   Limiting the typedef-name and tag forms to one occurrence resolves
   the typedef/identifier ambiguity.
*)
type_part:
  | l = nonempty_list(arith_keyword) { (make_arith l, []) }
  | s = struct_or_union_specifier    { s }
  | e = enum_specifier               { e }
  | t = TYPEDEF_NAME                 { (T.typedef_ t, []) }

arith_keyword:
  | VOID     { AKvoid }
  | CHAR     { AKchar }
  | SHORT    { AKshort }
  | INT      { AKint }
  | LONG     { AKlong }
  | FLOAT    { AKfloat }
  | DOUBLE   { AKdouble }
  | SIGNED   { AKsigned }
  | UNSIGNED { AKunsigned }
  | BOOL     { AKbool }

(* {1 Struct, union, enum} *)

struct_or_union:
  | STRUCT { `struct_ }
  | UNION  { `union }

struct_or_union_specifier:
  (* GCC accepts a type attribute both immediately after the keyword (its
     preferred form) and after the closing brace. The leading list must be
     non-empty and thus a separate production, since a nullable list before
     the tag would collide with the tag-only reference form. *)
  | su = struct_or_union name = ioption(tag_name)
    LBRACE body = struct_declaration_list RBRACE attrs = attribute_specifier_list
    { make_compound ~su ~name ~body ~attrs ~ann:(loc $symbolstartpos $endpos) }
  | su = struct_or_union pre = nonempty_list(attribute_specifier) name = ioption(tag_name)
    LBRACE body = struct_declaration_list RBRACE post = attribute_specifier_list
    { make_compound ~su ~name ~body ~attrs:(List.concat pre @ post)
        ~ann:(loc $symbolstartpos $endpos) }
  | su = struct_or_union name = tag_name
    {
      let ty = match su with
        | `struct_ -> T.struct_ name
        | `union -> T.union_ name in
      ty, []
    }

tag_name:
  | n = IDENT         { n }
  | n = TYPEDEF_NAME  { n }

struct_declaration_list:
  | l = nonempty_list(struct_declaration)
    {
      let fields = List.concat_map fst l in
      let nested = List.concat_map snd l in
      fields, nested
    }

struct_declaration:
  | sq = specifier_qualifier_list ds = separated_nonempty_list(COMMA, struct_declarator) SEMI
    {
      let base, nested = sq in
      let fields =
        List.map
          (fun ((nameopt, dty), bits, attrs) ->
            let ty = dty base in
            let name = match nameopt with
              | Some n -> n
              | None -> "" in
            Tydecl.field ?bits ~attrs ~name ~ty ())
          ds in
      fields, nested
    }

struct_declarator:
  | d = declarator attrs = attribute_specifier_list
    { d, None, attrs }
  | d = declarator attrs = attribute_specifier_list COLON e = constant_expression
    { d, Some e, attrs }
  | COLON e = constant_expression
    { (None, Fun.id), Some e, [] }

enum_specifier:
  | ENUM name = ioption(tag_name) LBRACE items = enumerator_list RBRACE
    {
      let tag = match name with
        | Some n -> n
        | None -> Parse_state.fresh_anon_tag "enum" in
      let e = T.enum_ tag in
      let ed =
        Tydecl.enum
          ~tag ~items
          ~ann:(loc $symbolstartpos $endpos) in
      e, [ed]
    }
  | ENUM name = tag_name
    { T.enum_ name, [] }

enumerator_list:
  | e = enumerator
    { [e] }
  | e = enumerator COMMA
    { [e] }
  | e = enumerator COMMA rest = enumerator_list
    { e :: rest }

enumerator:
  | n = IDENT
    { Tydecl.eitem ~name:n () }
  | n = IDENT ASSIGN e = constant_expression
    { Tydecl.eitem ~name:n ~value:e () }

specifier_qualifier_list:
  | pre = list(type_qualifier) tp = type_part post = list(type_qualifier)
    {
      let cv = cv_of_quals (pre @ post) in
      apply_base_cv cv (fst tp), snd tp
    }

(* {1 Declarators} *)

declarator:
  | p = ioption(pointer) d = direct_declarator
    {
      match p with
      | None -> d
      | Some (pf : adeclr) ->
         let n, f = d in
         n, (fun t -> f (pf t))
    }

pointer:
  | STAR q = list(type_qualifier)
    { fun t -> ptr_of_quals q t }
  | STAR q = list(type_qualifier) p = pointer
    { fun t -> p (ptr_of_quals q t) }

direct_declarator:
  | id = declared_name { did id }
  | LPAREN d = declarator RPAREN { d }
  | d = direct_declarator LBRACKET qs = list(array_qualifier) e = ioption(assignment_expression) RBRACKET
    {
      let quals = List.filter_map (function `Qual q -> Some q | `Static -> None) qs in
      let static_ = List.exists (function `Static -> true | `Qual _ -> false) qs in
      let cv = cv_of_quals quals and restrict = restrict_of_quals quals in
      let n, f = d in
      let f' t =
        let t' = match e with
          | Some sz -> T.array ~cv ~restrict ~static_ ~size:sz t
          | None -> T.array ~cv ~restrict ~static_ t in
        f t' in
      n, f'
    }
  | d = direct_declarator LPAREN saved = save_cur_typedef ps = parameter_type_list_opt RPAREN
    {
      Parse_state.cur_typedef := saved;
      let n, f = d in
      let params, variadic = ps in
      n, (fun t -> f (T.fun_ ~result:t ~params ~variadic ()))
    }

declared_name:
  | n = IDENT        { n }
  | n = TYPEDEF_NAME { n }

(* Snapshot `cur_typedef` at the start of a parameter list.

   Each parameter's `declaration_specifiers` overwrites the global flag, so
   without this hack, the enclosing declarator (e.g. `typedef int f(void)`)
   would register its name as a variable rather than a type name.

   The enclosing rule restores the snapshot after the parameters.
*)
save_cur_typedef:
  | (* empty *) { !Parse_state.cur_typedef }

(* Empty parens are an (unspecified-argument) function declarator with no
   parameters, folded in here so the function-declarator rule has a single
   form and no empty-params shift/reduce conflict. *)
parameter_type_list_opt:
  | (* empty *)              { [], false }
  | ps = parameter_type_list { ps }

parameter_type_list:
  | l = parameter_list { normalize_params (fst l), snd l }

parameter_list:
  | p = parameter_declaration { [p], false }
  | p = parameter_declaration COMMA ELLIPSIS { [p], true }
  | p = parameter_declaration COMMA rest = parameter_list
    {
      let ps, v = rest in
      p :: ps, v
    }

parameter_declaration:
  | ds = declaration_specifiers d = declarator
    {
      let _, mods, base, _ = ds in
      let base = apply_base_cv (resolve_mods mods).cv base in
      let n, f = d in
      {T.pname = n; ptype = f base}
    }
  | ds = declaration_specifiers ad = ioption(abstract_declarator)
    { let _, mods, base, _ = ds in
      let base = apply_base_cv (resolve_mods mods).cv base in
      let ptype = match ad with
        | Some (f : adeclr) -> f base
        | None -> base in
      {T.pname = None; ptype}
    }

abstract_declarator:
  | p = pointer { p }
  | p = ioption(pointer) d = direct_abstract_declarator
    {
      match p with
      | None -> d
      | Some (pf : adeclr) -> fun t -> d (pf t)
    }

direct_abstract_declarator:
  | LPAREN d = abstract_declarator RPAREN { d }
  | d = ioption(direct_abstract_declarator) LBRACKET qs = list(array_qualifier) e = ioption(assignment_expression) RBRACKET
    {
      let quals = List.filter_map (function `Qual q -> Some q | `Static -> None) qs in
      let static_ = List.exists (function `Static -> true | `Qual _ -> false) qs in
      let cv = cv_of_quals quals and restrict = restrict_of_quals quals in
      let inner = match d with
        | Some f -> f
        | None -> (fun t -> t) in
      let f' t =
        let t' = match e with
          | Some sz -> T.array ~cv ~restrict ~static_ ~size:sz t
          | None -> T.array ~cv ~restrict ~static_ t in
        inner t' in
      f'
    }
  | d = ioption(direct_abstract_declarator) LPAREN ps = ioption(parameter_type_list) RPAREN
    {
      let inner = match d with
        | Some f -> f
        | None -> Fun.id in
      let params, variadic = match ps with
        | Some pv -> pv
        | None -> [], false in
      fun t -> inner (T.fun_ ~result:t ~params ~variadic ())
    }

type_name:
  | sq = specifier_qualifier_list ad = ioption(abstract_declarator)
    {
      let base, _ = sq in
      match ad with
      | Some (f : adeclr) -> f base
      | None -> base
    }

(* {1 Initializers} *)

c_initializer:
  | e = assignment_expression { Expr.Isingle e }
  | LBRACE l = initializer_item_list RBRACE { Expr.Icompound l }

(* Hand-rolled to tolerate a trailing comma without conflicting with the
   item separator. *)
initializer_item_list:
  | i = initializer_item { [i] }
  | i = initializer_item COMMA { [i] }
  | i = initializer_item COMMA rest = initializer_item_list { i :: rest }

initializer_item:
  | dl = nonempty_list(designator) ASSIGN i = c_initializer { (dl, i) }
  | i = c_initializer { ([], i) }

designator:
  | LBRACKET e = constant_expression RBRACKET { Expr.Dindex e }
  | DOT f = field_name { Expr.Dfield f }

field_name:
  | n = IDENT        { n }
  | n = TYPEDEF_NAME { n }

(* {1 Statements} *)

statement:
  | s = labeled_statement     { s }
  | s = compound_statement    { s }
  | s = expression_statement  { s }
  | s = selection_statement   { s }
  | s = iteration_statement   { s }
  | s = jump_statement        { s }

labeled_statement:
  | n = IDENT COLON s = statement
    { Stmt.label ~name:n ~body:s ~ann:(loc $symbolstartpos $endpos) }
  | CASE e = constant_expression COLON s = statement
    { Stmt.case ~value:e ~body:s ~ann:(loc $symbolstartpos $endpos) }
  | DEFAULT COLON s = statement
    { Stmt.default s ~ann:(loc $symbolstartpos $endpos) }

compound_statement:
  | LBRACE enter_scope items = list(block_item) RBRACE
    {
      Lexer_hack.pop_scope ();
      Stmt.block (List.concat items) ~ann:(loc $symbolstartpos $endpos)
    }

enter_scope:
  | (* empty *) { Lexer_hack.push_scope () }

block_item:
  | s = statement { [Stmt.Bstmt s] }
  | d = block_declaration { d }

(* A block-scope declaration becomes block items: variable declarations,
   and any block-scope type declarations (struct/union/enum definitions in
   the specifier, and typedefs) that must be registered before them. *)
block_declaration:
  | ds = declaration_specifiers idecls = init_declarator_list SEMI
    {
      let _, mods, base, extra = ds in
      let m = resolve_mods mods in
      let base = apply_base_cv m.cv base in
      let ann = loc $symbolstartpos $endpos in
      let extra_items =
        if List.is_empty extra then [] else [Stmt.Btype extra] in
      if m.is_typedef then
        (* Each declarator introduces a block-scope typedef. *)
        let tds =
          List.filter_map
            (fun ((nameopt, dty), _init, _dattrs) ->
              match nameopt with
              | None -> None
              | Some name -> Some (Tydecl.typedef ~name ~ty:(dty base) ~ann))
            idecls in
        extra_items @ (if List.is_empty tds then [] else [Stmt.Btype tds])
      else
        extra_items @
        List.filter_map
          (fun ((nameopt, dty), init, dattrs) ->
            match nameopt with
            | None -> None
            | Some name ->
               let ty = dty base in
               let ld =
                 Stmt.localdecl
                   ~name ~ty ?init
                   ~storage:m.storage
                   ~attrs:(m.attrs @ dattrs)
                   ~ann () in
               Some (Stmt.Bdecl [ld]))
          idecls
    }
  | ds = declaration_specifiers SEMI
    {
      let _, _mods, base, extra = ds in
      let items =
        if List.is_empty extra
        then incomplete_tag ~ann:(loc $symbolstartpos $endpos) base
        else extra in
      if List.is_empty items then [] else [Stmt.Btype items]
    }

expression_statement:
  | SEMI { Stmt.null ~ann:(loc $symbolstartpos $endpos) }
  | e = expression SEMI { Stmt.expr e ~ann:(loc $symbolstartpos $endpos) }

selection_statement:
  | IF LPAREN c = expression RPAREN t = statement %prec below_ELSE
    { Stmt.if_ ~cond:c ~then_:t ~ann:(loc $symbolstartpos $endpos) () }
  | IF LPAREN c = expression RPAREN t = statement ELSE e = statement
    { Stmt.if_ ~cond:c ~then_:t ~else_:e ~ann:(loc $symbolstartpos $endpos) () }
  | SWITCH LPAREN e = expression RPAREN s = statement
    { Stmt.switch ~expr:e ~body:s ~ann:(loc $symbolstartpos $endpos) }

iteration_statement:
  | WHILE LPAREN c = expression RPAREN s = statement
    { Stmt.while_ ~cond:c ~body:s ~ann:(loc $symbolstartpos $endpos) }
  | DO s = statement WHILE LPAREN c = expression RPAREN SEMI
    { Stmt.dowhile ~body:s ~cond:c ~ann:(loc $symbolstartpos $endpos) }
  | FOR LPAREN init = for_init c = ioption(expression) SEMI step = ioption(expression) RPAREN s = statement
    { Stmt.for_ ?init ?cond:c ?step ~body:s ~ann:(loc $symbolstartpos $endpos) () }

for_init:
  | SEMI { None }
  | e = expression SEMI { Some (Stmt.FIexpr e) }
  | ds = declaration_specifiers idecls = init_declarator_list SEMI
    {
      let (_, mods, base, _) = ds in
      let m = resolve_mods mods in
      let base = apply_base_cv m.cv base in
      let ld =
        List.filter_map
          (fun ((nameopt, dty), init, dattrs) ->
            match nameopt with
            | None -> None
            | Some name ->
               let ld =
                 Stmt.localdecl
                   ~name ~ty:(dty base) ?init
                   ~storage:m.storage
                   ~attrs:(m.attrs @ dattrs)
                   ~ann:(loc $symbolstartpos $endpos) () in
               Some ld)
          idecls in
      Some (Stmt.FIdecl ld)
    }

jump_statement:
  | GOTO n = IDENT SEMI
    { Stmt.goto n ~ann:(loc $symbolstartpos $endpos) }
  (* GNU computed goto. *)
  | GOTO STAR e = expression SEMI
    { Stmt.gotoind e ~ann:(loc $symbolstartpos $endpos) }
  | CONTINUE SEMI
    { Stmt.continue ~ann:(loc $symbolstartpos $endpos) }
  | BREAK SEMI
    { Stmt.break ~ann:(loc $symbolstartpos $endpos) }
  | RETURN e = ioption(expression) SEMI
    { Stmt.return ?value:e ~ann:(loc $symbolstartpos $endpos) () }

(* {1 Expressions} *)

primary_expression:
  | n = IDENT { Expr.name n ~ann:(loc $symbolstartpos $endpos) }
  (* GNU label-as-value: the address of a label. *)
  | ANDAND n = IDENT { Expr.labaddr n ~ann:(loc $symbolstartpos $endpos) }
  | c = CONSTANT { Expr.const c ~ann:(loc $symbolstartpos $endpos) }
  | s = nonempty_list(STRING)
    { Expr.str (String.concat "" s) ~ann:(loc $symbolstartpos $endpos) }
  | LPAREN e = expression RPAREN { e }
  | name = BUILTIN LPAREN args = separated_list(COMMA, builtin_argument) RPAREN
    {
      Expr.builtin
        ~name
        ~args
        ~ann:(loc $symbolstartpos $endpos)
    }

(* A builtin-call argument: a type name or an ordinary expression. Their
   leading tokens are disjoint (type specifiers/qualifiers and typedef names
   never begin an expression), so no ambiguity arises. *)
builtin_argument:
  | t = type_name { Expr.BAtype t }
  | e = assignment_expression { Expr.BAexpr e }

postfix_expression:
  | e = primary_expression { e }
  | a = postfix_expression LBRACKET i = expression RBRACKET
    { Expr.index ~arr:a ~idx:i ~ann:(loc $symbolstartpos $endpos) }
  | f = postfix_expression LPAREN args = separated_list(COMMA, assignment_expression) RPAREN
    { Expr.call ~callee:f ~args ~ann:(loc $symbolstartpos $endpos) }
  | o = postfix_expression DOT f = field_name
    { Expr.member ~obj:o ~field:f ~ann:(loc $symbolstartpos $endpos) }
  | o = postfix_expression ARROW f = field_name
    { Expr.arrow ~obj:o ~field:f ~ann:(loc $symbolstartpos $endpos) }
  | a = postfix_expression INCR
    { Expr.unary ~op:`postinc ~arg:a ~ann:(loc $symbolstartpos $endpos) }
  | a = postfix_expression DECR
    { Expr.unary ~op:`postdec ~arg:a ~ann:(loc $symbolstartpos $endpos) }
  | LPAREN t = type_name RPAREN LBRACE l = initializer_item_list RBRACE
    { Expr.compound ~ty:t ~init:(Expr.Icompound l) ~ann:(loc $symbolstartpos $endpos) }

unary_expression:
  | e = postfix_expression { e }
  | INCR e = unary_expression
    { Expr.unary ~op:`preinc ~arg:e ~ann:(loc $symbolstartpos $endpos) }
  | DECR e = unary_expression
    { Expr.unary ~op:`predec ~arg:e ~ann:(loc $symbolstartpos $endpos) }
  | op = unary_operator e = cast_expression
    { Expr.unary ~op ~arg:e ~ann:(loc $symbolstartpos $endpos) }
  | SIZEOF e = unary_expression
    { Expr.sizeof_e e ~ann:(loc $symbolstartpos $endpos) }
  | SIZEOF LPAREN t = type_name RPAREN
    { Expr.sizeof_t t ~ann:(loc $symbolstartpos $endpos) }
  | ALIGNOF e = unary_expression
    { Expr.alignof_e e ~ann:(loc $symbolstartpos $endpos) }
  | ALIGNOF LPAREN t = type_name RPAREN
    { Expr.alignof_t t ~ann:(loc $symbolstartpos $endpos) }

unary_operator:
  | AMP   { `addr }
  | STAR  { `deref }
  | PLUS  { `plus }
  | MINUS { `minus }
  | TILDE { `not_ }
  | BANG  { `lnot_ }

cast_expression:
  | e = unary_expression { e }
  | LPAREN t = type_name RPAREN e = cast_expression
    { Expr.cast ~dst:t ~arg:e ~ann:(loc $symbolstartpos $endpos) }

multiplicative_expression:
  | e = cast_expression { e }
  | l = multiplicative_expression op = mul_op r = cast_expression
    { Expr.binary ~op ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

mul_op:
  | STAR    { `mul }
  | SLASH   { `div }
  | PERCENT { `mod_ }

additive_expression:
  | e = multiplicative_expression { e }
  | l = additive_expression op = add_op r = multiplicative_expression
    { Expr.binary ~op ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

add_op:
  | PLUS  { `add }
  | MINUS { `sub }

shift_expression:
  | e = additive_expression { e }
  | l = shift_expression op = shift_op r = additive_expression
    { Expr.binary ~op ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

shift_op:
  | SHL { `shl }
  | SHR { `shr }

relational_expression:
  | e = shift_expression { e }
  | l = relational_expression op = rel_op r = shift_expression
    { Expr.binary ~op ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

rel_op:
  | LT { `lt }
  | GT { `gt }
  | LE { `le }
  | GE { `ge }

equality_expression:
  | e = relational_expression { e }
  | l = equality_expression op = eq_op r = relational_expression
    { Expr.binary ~op ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

eq_op:
  | EQ { `eq }
  | NE { `ne }

and_expression:
  | e = equality_expression { e }
  | l = and_expression AMP r = equality_expression
    { Expr.binary ~op:`and_ ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

xor_expression:
  | e = and_expression { e }
  | l = xor_expression CARET r = and_expression
    { Expr.binary ~op:`xor ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

or_expression:
  | e = xor_expression { e }
  | l = or_expression PIPE r = xor_expression
    { Expr.binary ~op:`or_ ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

logical_and_expression:
  | e = or_expression { e }
  | l = logical_and_expression ANDAND r = or_expression
    { Expr.binary ~op:`land_ ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

logical_or_expression:
  | e = logical_and_expression { e }
  | l = logical_or_expression OROR r = logical_and_expression
    { Expr.binary ~op:`lor_ ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

conditional_expression:
  | e = logical_or_expression { e }
  | c = logical_or_expression QUESTION t = expression COLON e = conditional_expression
    { Expr.cond ~cond:c ~then_:t ~else_:e ~ann:(loc $symbolstartpos $endpos) }

assignment_expression:
  | e = conditional_expression { e }
  | l = unary_expression op = assignment_operator r = assignment_expression
    { Expr.binary ~op ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

assignment_operator:
  | ASSIGN     { `assign }
  | ADD_ASSIGN { `assign_arith `add }
  | SUB_ASSIGN { `assign_arith `sub }
  | MUL_ASSIGN { `assign_arith `mul }
  | DIV_ASSIGN { `assign_arith `div }
  | MOD_ASSIGN { `assign_arith `mod_ }
  | AND_ASSIGN { `assign_bitwise `and_ }
  | OR_ASSIGN  { `assign_bitwise `or_ }
  | XOR_ASSIGN { `assign_bitwise `xor }
  | SHL_ASSIGN { `assign_bitwise `shl }
  | SHR_ASSIGN { `assign_bitwise `shr }

expression:
  | e = assignment_expression { e }
  | l = expression COMMA r = assignment_expression
    { Expr.comma ~lhs:l ~rhs:r ~ann:(loc $symbolstartpos $endpos) }

constant_expression:
  | e = conditional_expression { e }
