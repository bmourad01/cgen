%{
    type elt =
      | Func of Structured.func
      | Typ  of Type.compound
      | Data of Virtual.data

    type call_arg =
      | Arg  of Virtual.operand
      | Varg of Virtual.operand

    type swcase =
      | Case    of Bv.t * Type.imm * Structured.stmt
      | Default of Structured.stmt

    module Env = struct
      (* Since we allow a nicer surface syntax over the internal
         representation of the IR, we need to do some bookkeeping.

         This mostly applies when using human-readable names in
         place of uniquely identified data.
       *)
      type t = {
        labels : Label.t Core.String.Map.t;
        temps : Var.t Core.String.Map.t;
      } [@@deriving bin_io, compare, sexp]

      let empty = {
        labels = Core.String.Map.empty;
        temps = Core.String.Map.empty;
      }

      (* Not needed. *)
      let pp _ppf _t = ()
    end

    let tag = Dict.register
        ~uuid:"c487156f-eec6-47bc-83ec-daf3b838dba2"
        "structured-parser-env" (module Env)

    open Context.Syntax

    let setenv v = Context.Local.set tag v
    let curenv = Context.Local.get' tag ~default:Env.empty

    (* Each time parse a new function, reset the context, since
       labels do not have scope outside of a function body. *)
    let reset = setenv Env.empty
    
    let label_of_name name =
      let* env = curenv in
      match Core.Map.find env.labels name with
      | Some l -> !!l
      | None ->
         let* l = Context.Label.fresh in
         let labels = Core.Map.set env.labels ~key:name ~data:l in
         let+ () = setenv {env with labels} in
         l

    let temp_of_name ?index name =
      let* env = curenv in
      let+ v = match Core.Map.find env.temps name with
        | Some v -> !!v
        | None ->
          let* v = Context.Var.fresh in
          let temps = Core.Map.set env.temps ~key:name ~data:v in
          let+ () = setenv {env with temps} in
          v in
      match index with
      | Some i -> Var.with_index v i
      | None -> v

    let make_data l align c name elts =
      let module Tag = Virtual.Data.Tag in
      let dict = Dict.empty in
      let dict = match l with
        | Some linkage -> Dict.set dict Tag.linkage linkage
        | None -> dict in
      let dict = match align with
        | Some align -> Dict.set dict Tag.align align
        | None -> dict in
      let dict = match c with
        | Some k -> Dict.set dict Tag.const k
        | None -> dict in
      match Virtual.Data.create () ~name ~elts ~dict with
      | Error err -> Context.fail err
      | Ok d -> !!d

    let make_fn slots body args l name return noreturn =
      let* slots = Context.List.all slots in
      let* body = body in
      let+ args, variadic = match args with
        | None -> !!([], false)
        | Some a -> a in
      let linkage = Core.Option.value l ~default:Linkage.default_static in
      let module Tag = Virtual.Func.Tag in
      let dict = Dict.empty in
      let dict = if noreturn then Dict.set dict Tag.noreturn () else dict in
      let dict = if variadic then Dict.set dict Tag.variadic () else dict in
      let dict = match return with
        | Some t -> Dict.set dict Tag.return t
        | None -> dict in
      let dict = Dict.set dict Tag.linkage linkage in
      Structured.Func.create () ~name ~body ~args ~slots ~dict
%}

%token EOF
%token PLUS
%token MINUS
%token <string> TYPENAME
%token <string> SYM
%token <string> LABEL
%token COLON
%token SEMI
%token ALIGN
%token <unit> CONST
%token TYPE
%token LBRACE
%token RBRACE
%token LPAREN
%token RPAREN
%token COMMA
%token EQUALS
%token ELLIPSIS
%token SB SH SW W L B H S D Z
%token <Type.basic> ADD DIV MUL SUB NEG
%token NOP
%token <Type.imm> REM MULH UMULH UDIV UREM AND OR ASR LSL LSR ROL ROR XOR NOT
%token SLOT
%token <Type.arg> LOAD STORE
%token <Type.basic> EQ GE GT LE LT NE
%token <Type.imm> SGE SGT SLE SLT
%token <Type.fp> O UO
%token <Type.fp * Type.imm> FTOSI FTOUI
%token <Type.fp> FEXT FIBITS FTRUNC
%token <Type.imm> CLZ CTZ FLAG ITRUNC POPCNT SEXT ZEXT
%token <Type.imm_base> IFBITS
%token <Type.imm * Type.fp> SITOF UITOF
%token <Type.basic> COPY SEL
%token <Type.ret> ACALL
%token CALL
%token <Type.arg> VAARG
%token VASTART
%token START
%token HLT
%token GOTO
%token IF ELSE
%token WHEN UNLESS
%token LOOP
%token WHILE
%token DO
%token BREAK
%token RET
%token <Type.imm> SWITCH
%token CASE DEFAULT
%token <string> MODULE
%token FUNCTION
%token DATA
%token EXPORT
%token SECTION
%token NORETURN
%token <string> STRING
%token <Bv.t * Type.imm> INT
%token <Bv.t> NUM
%token <float> DOUBLE
%token <Float32.t> SINGLE
%token <bool> BOOL
%token <string * int> VAR
%token <string> IDENT
%token <string> TEMP
%token <string * int> TEMPI

%start module_

%type<Structured.module_ Context.t> module_
%type <elt Context.t> module_elt
%type <Virtual.Data.elt> data_elt
%type <Type.compound> typ
%type <[`opaque of int | `fields of Type.field list]> typ_fields_or_opaque
%type <Type.field> typ_field
%type <Structured.func Context.t> func
%type <((Var.t * Type.arg) list * bool) Context.t> func_args
%type <Type.basic> type_basic
%type <Type.arg> type_arg
%type <Type.ret> type_ret
%type <Linkage.t> linkage
%type <string> section
%type <Virtual.slot Context.t> slot
%type <swcase Context.t> switch_case
%type <(Label.t * Structured.stmt) Context.t> label_stmt
%type <Structured.stmt Context.t> label_stmt_full
%type <Structured.stmt Context.t> stmt
%type <Structured.stmt Context.t> non_label_stmt
%type <call_arg list Context.t> call_args
%type <Structured.Stmt.cond Context.t> stmt_cond
%type <Virtual.Insn.binop> insn_binop
%type <Virtual.Insn.unop> insn_unop
%type <Virtual.Insn.arith_binop> insn_arith_binop
%type <Virtual.Insn.bitwise_binop> insn_bitwise_binop
%type <Virtual.Insn.cmp> insn_cmp
%type <Virtual.Insn.arith_unop> insn_arith_unop
%type <Virtual.Insn.bitwise_unop> insn_bitwise_unop
%type <Virtual.Insn.cast> insn_cast
%type <Virtual.Insn.copy> insn_copy
%type <Structured.Stmt.goto Context.t> goto
%type <Virtual.global Context.t> global
%type <Virtual.operand Context.t> operand
%type <Virtual.const> const
%type <Var.t Context.t> var

%%

module_:
  | name = MODULE elts = list(module_elt) EOF
    {
      let* funs, typs, data =
        let init = [], [], [] in
        Context.List.fold elts ~init ~f:(fun (funs, typs, data) x ->
            reset >>= fun () -> x >>| function
            | Func f -> f :: funs, typs, data
            | Typ  t -> funs, t :: typs, data
            | Data d -> funs, typs, d :: data) in
      let+ () = Context.Local.erase tag in
      Structured.Module.create () ~name
        ~funs:(List.rev funs)
        ~typs:(List.rev typs)
        ~data:(List.rev data)
    }

module_elt:
  | f = func { let+ f = f in Func f }
  | t = typ { !!(Typ t) }
  | d = data { let+ d = d in Data d }

data:
  | l = option(linkage) c = option(CONST) DATA name = SYM EQUALS ALIGN align = NUM LBRACE elts = separated_nonempty_list(COMMA, data_elt) RBRACE
    {
      make_data l (Some (Bv.to_int align)) c name elts
    }
  | l = option(linkage) c = option(CONST) DATA name = SYM EQUALS LBRACE elts = separated_nonempty_list(COMMA, data_elt) RBRACE
    {
      make_data l None c name elts
    }

data_elt:
  | c = const { (c :> Virtual.Data.elt) }
  | s = STRING { `string s }
  | Z n = NUM { `zero (Bv.to_int n) }

typ:
  | TYPE name = TYPENAME EQUALS LBRACE fields = separated_list(COMMA, typ_field) RBRACE
    { `compound (name, None, fields) }
  | TYPE name = TYPENAME EQUALS ALIGN align = NUM LBRACE t = typ_fields_or_opaque RBRACE
    {
      let align = Bv.to_int align in
      match t with
      | `opaque n -> `opaque (name, align, n)
      | `fields f -> `compound (name, Some align, f)
    }

typ_fields_or_opaque:
  | n = NUM { `opaque (Bv.to_int n) }
  | fs = separated_list(COMMA, typ_field) { `fields fs }

typ_field:
  | b = type_basic n = option(NUM) { `elt (b, Core.Option.value_map n ~default:1 ~f:Bv.to_int) }
  | s = TYPENAME n = option(NUM) { `name (s, Core.Option.value_map n ~default:1 ~f:Bv.to_int) }

func:
  | l = option(linkage) FUNCTION return = option(type_ret) name = SYM LPAREN args = option(func_args) RPAREN LBRACE slots = list(slot) START COLON body = stmt RBRACE
    { make_fn slots body args l name return false }
  | l = option(linkage) NORETURN FUNCTION return = option(type_ret) name = SYM LPAREN args = option(func_args) RPAREN LBRACE slots = list(slot) START COLON body = stmt RBRACE
    { make_fn slots body args l name return true }

func_args:
  | ELLIPSIS { !!([], true) }
  | t = type_arg x = var { let+ x = x in [x, t], false }
  | t = type_arg x = var COMMA rest = func_args
    {
      let+ rest = rest and+ x = x in
      (x, t) :: fst rest, snd rest
    }

type_basic:
  | W { `i32 }
  | L { `i64 }
  | B { `i8 }
  | H { `i16 }
  | S { `f32 }
  | D { `f64 }

type_arg:
  | b = type_basic { (b :> Type.arg) }
  | n = TYPENAME { `name n }

type_ret:
  | a = type_arg { (a :> Type.ret) }
  | SB { `si8 }
  | SH { `si16 }
  | SW { `si32 }

linkage:
  | section = option(section) EXPORT { Linkage.create () ~section ~export:true }
  | s = section { Linkage.create () ~section:(Some s) ~export:false }

section:
  | SECTION s = STRING { s }

slot:
  | x = var EQUALS SLOT size = NUM COMMA ALIGN align = NUM
    {
      let* x = x in
      let size = Bv.to_int size in
      let align = Bv.to_int align in
      match Virtual.Slot.create x ~size ~align with
      | Error e -> Context.fail e
      | Ok s -> !!s
    }

switch_case:
  | CASE i = INT COLON b = option(stmt)
    {
      let+ b = match b with
        | None -> !!`nop
        | Some b -> b in
      Case (fst i, snd i, b)
    }
  | DEFAULT COLON d = option(stmt)
    {
      let+ d = match d with
        | None -> !!`nop
        | Some d -> d in
      Default d
    }

%inline label_stmt:
  | l = LABEL COLON s = stmt
    { let+ l = label_of_name l and+ s = s in l, s }

%inline label_stmt_full:
  | s = label_stmt
    {
      let+ l, s = s in
      `label (l, s)
    }

stmt:
  | s = non_label_stmt option(SEMI) { s }
  | s1 = non_label_stmt SEMI s2 = stmt
    {
      let+ s1 = s1 and+ s2 = s2 in
      `seq (s1, s2)
    }
  | lab = label_stmt_full { lab }

stmt_cond:
  | x = var { let+ x = x in `var x }
  | k = insn_cmp l = operand COMMA r = operand
    {
      let+ l = l and+ r = r in
      `cmp (k, l, r)
    }

non_label_stmt:
  | NOP { !!`nop }
  | BREAK { !!`break }
  | IF x = stmt_cond LBRACE t = stmt RBRACE ELSE LBRACE e = stmt RBRACE
    {
      let+ x = x and+ t = t and+ e = e in
      `ite (x, t, e)
    }
  | WHEN x = stmt_cond LBRACE b = stmt RBRACE
    { let+ x = x and+ b = b in Structured.Stmt.when_ x b }
  | UNLESS x = stmt_cond LBRACE b = stmt RBRACE
    { let+ x = x and+ b = b in Structured.Stmt.unless x b }
  | LOOP LBRACE b = stmt RBRACE { let+ b = b in `loop b }
  | WHILE x = stmt_cond LBRACE b = stmt RBRACE
    {
      let+ x = x and+ b = b in
      Structured.Stmt.while_ x b
    }
  | DO LBRACE b = stmt RBRACE WHILE x = stmt_cond
    {
      let+ b = b and+ x = x in
      Structured.Stmt.dowhile b x
    }
  | GOTO g = goto { let+ g = g in `goto g }
  | t = SWITCH i = var LBRACE cs = list(switch_case) RBRACE
    {
      let* i = i and* cs = Context.List.all cs in
      let+ cs = Context.List.map cs ~f:(function
          | Default d -> !!(`default d)
          | Case (i, t', b) when Type.equal_imm t t' ->
            !!(`case (i, b))
          | Case (i, t', _) ->
            Context.failf
              "Invalid switch value %a_%a, expected size %a"
              Bv.pp i Type.pp_imm t' Type.pp_imm t ()) in
      `sw (i, t, cs)
    }
  | HLT { !!`hlt }
  | RET a = option(operand)
    {
      match a with
      | None -> !!(`ret None)
      | Some a -> let+ a = a in `ret (Some a)
    }
  | x = var EQUALS b = insn_binop l = operand COMMA r = operand
    {
      let+ x = x and+ l = l and+ r = r in
      `bop (x, b, l, r)
    }
  | x = var EQUALS u = insn_unop a = operand
    {
      let+ x = x and+ a = a in
      `uop (x, u, a)
    }
  | x = var EQUALS t = SEL c = var COMMA l = operand COMMA r = operand
    {
      let+ x = x and+ c = c and+ l = l and+ r = r in
      `sel (x, t, c, l, r)
    }
  | x = var EQUALS t = ACALL f = global LPAREN args = call_args RPAREN
    {
      let+ x = x and+ f = f and+ args = args in
      let args, vargs =
        Core.List.partition_map args ~f:(function
            | Arg a -> First a
            | Varg a -> Second a) in
      `call (Some (x, t), f, args, vargs)
    }
  | CALL f = global LPAREN args = call_args RPAREN
    {
      let+ f = f and+ args = args in
      let args, vargs =
        Core.List.partition_map args ~f:(function
            | Arg a -> First a
            | Varg a -> Second a) in
      `call (None, f, args, vargs)
    }
  | x = var EQUALS t = VAARG y = var
    {
      let+ x = x and+ y = y in
      `vaarg (x, t, `var y)
    }
  | x = var EQUALS t = VAARG y = NUM
    {
      let+ x = x in
      `vaarg (x, t, `addr y)
    }
  | x = var EQUALS t = VAARG y = SYM
    {
      let+ x = x in
      `vaarg (x, t, `sym (y, 0))
    }
  | x = var EQUALS t = VAARG y = SYM PLUS i = NUM
    {
      let+ x = x in
      `vaarg (x, t, `sym (y, Bv.to_int i))
    }
  | x = var EQUALS t = VAARG y = SYM MINUS i = NUM
    {
      let+ x = x in
      `vaarg (x, t, `sym (y, -(Bv.to_int i)))
    }
  | VASTART x = var { let+ x = x in `vastart (`var x) }
  | VASTART x = NUM { !!(`vastart (`addr x)) }
  | VASTART x = SYM { !!(`vastart (`sym (x, 0))) }
  | VASTART x = SYM PLUS i = NUM { !!(`vastart (`sym (x, Bv.to_int i))) }
  | VASTART x = SYM MINUS i = NUM { !!(`vastart (`sym (x, -(Bv.to_int i)))) }
  | x = var EQUALS t = LOAD a = operand
    {
      let+ x = x and+ a = a in
      `load (x, t, a)
    }
  | t = STORE v = operand COMMA a = operand
    {
      let+ v = v and+ a = a in
      `store (t, v, a)
    }

call_args:
  | a = option(operand)
    {
      match a with
      | None -> !![]
      | Some a -> let+ a = a in [Arg a]
    }
  | a = operand COMMA rest = call_args
    {
      let+ a = a and+ rest = rest in
      Arg a :: rest
    }
  | a = operand COMMA ELLIPSIS COMMA vargs = separated_nonempty_list(COMMA, operand)
    {
      let+ a = a and+ vargs = Context.List.all vargs in
      Arg a :: Core.List.map vargs ~f:(fun a -> Varg a)
    }

insn_binop:
  | a = insn_arith_binop { (a :> Virtual.Insn.binop) }
  | b = insn_bitwise_binop { (b :> Virtual.Insn.binop) }
  | c = insn_cmp { (c :> Virtual.Insn.binop) }

insn_unop:
  | a = insn_arith_unop { (a :> Virtual.Insn.unop) }
  | b = insn_bitwise_unop { (b :> Virtual.Insn.unop) }
  | c = insn_cast { (c :> Virtual.Insn.unop) }
  | c = insn_copy { (c :> Virtual.Insn.unop) }

insn_arith_binop:
  | t = ADD { `add t }
  | t = DIV { `div t }
  | t = MUL { `mul t }
  | t = MULH { `mulh t }
  | t = REM { `rem t }
  | t = SUB { `sub t }
  | t = UDIV { `udiv t }
  | t = UMULH { `umulh t }
  | t = UREM { `urem t }

insn_bitwise_binop:
  | t = AND { `and_ t }
  | t = OR { `or_ t }
  | t = ASR { `asr_ t }
  | t = LSL { `lsl_ t }
  | t = LSR { `lsr_ t }
  | t = ROL { `rol t }
  | t = ROR { `ror t }
  | t = XOR { `xor t }

insn_cmp:
  | t = EQ { `eq t }
  | t = GE { `ge t }
  | t = GT { `gt t }
  | t = LE { `le t }
  | t = LT { `lt t }
  | t = NE { `ne t }
  | t = O { `o t }
  | t = SGE { `sge t }
  | t = SGT { `sgt t }
  | t = SLE { `sle t }
  | t = SLT { `slt t }
  | t = UO { `uo t }

insn_arith_unop:
  | t = NEG { `neg t }

insn_bitwise_unop:
  | t = CLZ { `clz t }
  | t = CTZ { `ctz t }
  | t = NOT { `not_ t }
  | t = POPCNT { `popcnt t }

insn_cast:
  | t = FEXT { `fext t }
  | t = FIBITS { `fibits t }
  | t = FLAG { `flag t }
  | t = FTOSI { `ftosi (fst t, snd t) }
  | t = FTOUI { `ftoui (fst t, snd t) }
  | t = FTRUNC { `ftrunc t }
  | t = IFBITS { `ifbits t }
  | t = ITRUNC { `itrunc t }
  | t = SEXT { `sext t }
  | t = SITOF { `sitof (fst t, snd t) }
  | t = UITOF { `uitof (fst t, snd t) }
  | t = ZEXT { `zext t }

insn_copy:
  | t = COPY { `copy t }

goto:
  | g = global { let+ g = g in (g :> Structured.Stmt.goto) }
  | l = LABEL { let+ l = label_of_name l in `label l }

global:
  | i = NUM { !!(`addr i) }
  | s = SYM { !!(`sym (s, 0)) }
  | s = SYM PLUS i = NUM { !!(`sym (s, Bv.to_int i)) }
  | s = SYM MINUS i = NUM { !!(`sym (s, -(Bv.to_int i))) }
  | x = var { let+ x = x in `var x }

operand:
  | c = const { !!(c :> Virtual.operand) }
  | x = var { let+ x = x in `var x }

const:
  | b = BOOL { `bool b }
  | i = INT { `int i }
  | s = SINGLE { `float s }
  | d = DOUBLE { `double d }
  | s = SYM { `sym (s, 0) }
  | s = SYM PLUS i = NUM { `sym (s, Bv.to_int i) }
  | s = SYM MINUS i = NUM { `sym (s, -(Bv.to_int i)) }

var:
  | x = VAR { !!Var.(with_index (create (fst x)) (snd x)) }
  | x = IDENT { !!(Var.create x) }
  | x = TEMP { temp_of_name x }
  | x = TEMPI { temp_of_name (fst x) ~index:(snd x) }
