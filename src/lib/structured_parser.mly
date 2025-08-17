%{
    type elt =
      | Func of Virtual.func
      | Typ  of Type.compound
      | Data of Virtual.data

    type call_arg =
      | Arg  of Virtual.operand
      | Varg of Virtual.operand

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
  | EOF
    {
      ()
    }
