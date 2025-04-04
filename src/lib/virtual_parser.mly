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
        ~uuid:"98ff53de-6779-494c-81d6-1d3dd6f71e5e"
        "virtual-parser-env" (module Env)

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

    let make_fn slots blks args l name return noreturn =
      let* slots = Context.List.all slots in
      let* blks = Context.List.all blks in
      let* args, variadic = match args with
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
      match Virtual.Func.create () ~name ~blks ~args ~slots ~dict with
      | Error err -> Context.fail err
      | Ok fn -> !!fn
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
%token JMP
%token BR
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

%type <Virtual.module_ Context.t> module_
%type <elt Context.t> module_elt
%type <Virtual.data Context.t> data
%type <Virtual.Data.elt> data_elt
%type <Type.compound> typ
%type <[`opaque of int | `fields of Type.field list]> typ_fields_or_opaque
%type <Type.field> typ_field
%type <Virtual.func Context.t> func
%type <((Var.t * Type.arg) list * bool) Context.t> func_args
%type <Type.basic> type_basic
%type <Type.arg> type_arg
%type <Type.ret> type_ret
%type <Linkage.t> linkage
%type <string> section
%type <Virtual.slot Context.t> slot
%type <Virtual.blk Context.t> blk
%type <Var.t Context.t> blk_arg
%type <Virtual.Ctrl.t Context.t> ctrl
%type <Virtual.Ctrl.swindex Context.t> ctrl_index
%type <((Bv.t * Type.imm) * Virtual.local) Context.t> ctrl_table_entry
%type <Virtual.Insn.op Context.t> insn
%type <call_arg list Context.t> call_args
%type <Virtual.Insn.binop> insn_binop
%type <Virtual.Insn.unop> insn_unop
%type <Virtual.Insn.arith_binop> insn_arith_binop
%type <Virtual.Insn.bitwise_binop> insn_bitwise_binop
%type <Virtual.Insn.cmp> insn_cmp
%type <Virtual.Insn.arith_unop> insn_arith_unop
%type <Virtual.Insn.bitwise_unop> insn_bitwise_unop
%type <Virtual.Insn.cast> insn_cast
%type <Virtual.Insn.copy> insn_copy
%type <Virtual.dst Context.t> dst
%type <Virtual.local Context.t> local
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
      (* Our state is local to the parser, so we should avoid a
         potential memory leak. *)
      let+ () = Context.Local.erase tag in
      Virtual.Module.create () ~name
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
  | l = option(linkage) FUNCTION return = option(type_ret) name = SYM LPAREN args = option(func_args) RPAREN LBRACE slots = list(slot) blks = nonempty_list(blk) RBRACE
    { make_fn slots blks args l name return false }
  | l = option(linkage) NORETURN FUNCTION return = option(type_ret) name = SYM LPAREN args = option(func_args) RPAREN LBRACE slots = list(slot) blks = nonempty_list(blk) RBRACE
    { make_fn slots blks args l name return true }

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

blk:
  | ln = LABEL COLON insns = list(insn) ctrl = ctrl
    {
      let* l = label_of_name ln
      and* insns = Context.List.all insns
      and* ctrl = ctrl in
      Context.Virtual.blk' () ~label:(Some l) ~insns ~ctrl
    }
  | ln = LABEL LPAREN args = separated_nonempty_list(COMMA, blk_arg) RPAREN COLON insns = list(insn) ctrl = ctrl
    {
      let* l = label_of_name ln
      and* args = Context.List.all args
      and* insns = Context.List.all insns
      and* ctrl = ctrl in
      Context.Virtual.blk' () ~label:(Some l) ~args ~insns ~ctrl
    }

blk_arg:
  | v = var { v }

ctrl:
  | HLT { !!`hlt }
  | JMP d = dst { let+ d = d in `jmp d }
  | BR c = var COMMA t = dst COMMA f = dst
    {
      let+ c = c and+ t = t and+ f = f in
      `br (c, t, f)
    }
  | RET a = option(operand)
    {
      match a with
      | None -> !!(`ret None)
      | Some a -> let+ a = a in `ret (Some a)
    }
  | t = SWITCH i = ctrl_index COMMA def = local LSQUARE tbl = separated_nonempty_list(COMMA, ctrl_table_entry) RSQUARE
    {
      let* i = i and* d = def and* tbl = Context.List.all tbl in
      let* tbl = Context.List.map tbl ~f:(fun ((i, t'), l) ->
          if not @@ Type.equal_imm t t' then
            Context.failf
              "Invalid switch value %a_%a, expected size %a"
              Bv.pp i Type.pp_imm t' Type.pp_imm t ()
          else !!(i, l)) in
      match Virtual.Ctrl.Table.create tbl t with
      | Error err -> Context.fail err
      | Ok tbl -> !!(`sw (t, i, d, tbl))
    }

ctrl_index:
  | x = var { let+ x = x in `var x }
  | s = SYM { !!(`sym (s, 0)) }
  | s = SYM PLUS i = NUM { !!(`sym (s, Bv.to_int i)) }
  | s = SYM MINUS i = NUM { !!(`sym (s, -(Bv.to_int i))) }

ctrl_table_entry:
  | i = INT ARROW l = local { let+ l = l in i, l }

insn:
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
  | a = operand COMMA ELIPSIS COMMA vargs = separated_nonempty_list(COMMA, operand)
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

dst:
  | g = global { let+ g = g in (g :> Virtual.dst) }
  | l = local { let+ l = l in (l :> Virtual.dst) }

local:
  | l = LABEL
    {
      let+ l = label_of_name l in
      `label (l, [])
    }
  | l = LABEL LPAREN args = separated_nonempty_list(COMMA, operand) RPAREN
    {
      let+ args = Context.List.all args and+ l = label_of_name l in
      `label (l, args)
    }

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
