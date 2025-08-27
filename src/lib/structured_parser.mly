%{
    (*
    type elt =
      | Func of Virtual.func
      | Typ  of Type.compound
      | Data of Virtual.data

    type call_arg =
      | Arg  of Virtual.operand
      | Varg of Virtual.operand
     *)
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
    let _reset = setenv Env.empty
    
    let _label_of_name name =
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
%token ALIGN
%token <unit> CONST
%token TYPE
%token LBRACE
%token RBRACE
%token LPAREN
%token RPAREN
%token LSQUARE
%token RSQUARE
%token COMMA
%token EQUALS
%token ARROW
%token ELIPSIS
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
%token HLT
%token GOTO
%token IF
%token WHILE
%token DO
%token RET
%token <Type.imm> SWITCH
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

%type<unit> module_

%%

module_:
  | name = MODULE elts = list(module_elt) EOF
    {
      let _ = name in
      let _ = elts in
      ()
    }

module_elt:
  | f = func { f }

func:
  | l = option(linkage) FUNCTION return = option(type_ret) name = SYM LPAREN args = option(func_args) RPAREN LBRACE slots = list(slot) body = stmt RBRACE
    { make_fn slots body args l name return false }
  | l = option(linkage) NORETURN FUNCTION return = option(type_ret) name = SYM LPAREN args = option(func_args) RPAREN LBRACE slots = list(slot) body = stmt RBRACE
    { make_fn slots body args l name return true }

func_args:
  | ELIPSIS { !!([], true) }
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

stmt:
  | NOP { !!(`nop) }

var:
  | x = VAR { !!Var.(with_index (create (fst x)) (snd x)) }
  | x = IDENT { !!(Var.create x) }
  | x = TEMP { temp_of_name x }
  | x = TEMPI { temp_of_name (fst x) ~index:(snd x) }
