 %{
    open Monads.Std

    type elt = [
      | `func of Virtual.func
      | `typ  of Type.compound
      | `data of Virtual.data
    ]

    type call_arg = [
      | `arg  of Virtual.operand
      | `varg of Virtual.operand
    ]

    module Env = struct
      (* Since we allow a nicer surface syntax over the internal
         representation of the IR, we need to do some bookkeeping.

         This mostly applies when using human-readable names in
         place of uniquely identified data.
       *)
      type t = {
        labels : Label.t Core.String.Map.t;
        temps : Var.t Core.String.Map.t;
      }

      let empty = {
        labels = Core.String.Map.empty;
        temps = Core.String.Map.empty;
      }
    end

    module M = Monad.State.Make(Env)(Context)

    type 'a m = 'a Monad.State.T1(Env)(Context).t
    
    open M.Syntax
    open M.Let

    (* Each time parse a new function, reset the context, since
       labels do not have scope outside of a function body. *)
    let reset = M.put Env.empty
    
    let label_of_name name =
      let* env = M.get () in
      match Core.Map.find env.labels name with
      | Some l -> !!l
      | None ->
         let* l = M.lift @@ Context.Label.fresh in
         let labels = Core.Map.set env.labels ~key:name ~data:l in
         let+ () = M.put {env with labels} in
         l

    let temp_of_name ?index name =
      let* env = M.get () in
      let+ v = match Core.Map.find env.temps name with
        | Some v -> !!v
        | None ->
          let* v = M.lift @@ Context.Var.fresh in
          let temps = Core.Map.set env.temps ~key:name ~data:v in
          let+ () = M.put {env with temps} in
          v in
      match index with
      | Some i -> Var.with_index v i
      | None -> v

    let unwrap_list = M.List.map ~f:(fun x -> x >>| Core.Fn.id)

    let make_fn blks args l name return noreturn =
      let* blks = unwrap_list blks in
      let* args, variadic = match args with
        | None -> !!([], false)
        | Some a -> a in
      let linkage = Core.Option.value l ~default:Linkage.default_static in
      match Virtual.Func.create () ~name ~blks ~args ~return ~noreturn ~variadic ~linkage with
      | Error err -> M.lift @@ Context.fail err
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
%token W L B H S D Z F
%token <Type.basic> ADD DIV MUL REM SUB NEG
%token <Type.imm> MULH UDIV UREM AND OR ASR LSL LSR ROL ROR XOR NOT
%token ALLOC
%token <Type.basic> LOAD STORE EQ GE GT LE LT NE
%token <Type.imm> SGE SGT SLE SLT
%token <Type.fp> O UO
%token <Type.fp * Type.imm> FTOSI FTOUI
%token <Type.fp> FEXT FIBITS FTRUNC
%token <Type.imm> CLZ CTZ FLAG ITRUNC POPCNT SEXT ZEXT
%token <Type.imm_base> IFBITS
%token <Type.imm * Type.fp> SITOF UITOF
%token <Type.basic> COPY SEL ACALL
%token <Type.imm_base> REF
%token CALL
%token <Type.basic> VAARG
%token VASTART
%token HLT
%token JMP
%token BR
%token RET
%token <Type.imm> SW
%token <string> MODULE
%token FUNCTION
%token DATA
%token EXPORT
%token SECTION
%token NORETURN
%token <string> STRING
%token <Bv.t * Type.imm> INT
%token <int> NUM
%token <float> DOUBLE
%token <Float32.t> SINGLE
%token <bool> BOOL
%token <string * int> VAR
%token <string> IDENT
%token <string> TEMP
%token <string * int> TEMPI

%start module_

%type <Virtual.module_ Context.t> module_
%type <elt m> module_elt
%type <Virtual.data m> data
%type <Virtual.Data.elt> data_elt
%type <Type.compound> typ
%type <int> align
%type <[`opaque of int | `fields of Type.field list]> typ_fields_or_opaque
%type <Type.field> typ_field
%type <Virtual.func m> func
%type <((Var.t * Type.arg) list * bool) m> func_args
%type <Type.basic> type_basic
%type <Type.special> type_special
%type <Type.arg> type_arg
%type <Virtual.Blk.arg_typ> type_blk_arg
%type <Linkage.t> linkage
%type <string> section
%type <Virtual.blk m> blk
%type <(Var.t * Virtual.Blk.arg_typ) m> blk_arg
%type <Virtual.Ctrl.t m> ctrl
%type <Virtual.Ctrl.swindex m> ctrl_index
%type <((Bv.t * Type.imm) * Virtual.local) m> ctrl_table_entry
%type <Virtual.Insn.op m> insn
%type <call_arg list m> call_args
%type <Virtual.Insn.binop> insn_binop
%type <Virtual.Insn.unop> insn_unop
%type <Virtual.Insn.arith_binop> insn_arith_binop
%type <Virtual.Insn.bitwise_binop> insn_bitwise_binop
%type <Virtual.Insn.cmp> insn_cmp
%type <Virtual.Insn.arith_unop> insn_arith_unop
%type <Virtual.Insn.bitwise_unop> insn_bitwise_unop
%type <Virtual.Insn.cast> insn_cast
%type <Virtual.Insn.copy> insn_copy
%type <Virtual.dst m> dst
%type <Virtual.local m> local
%type <Virtual.global m> global
%type <Virtual.operand m> operand
%type <Virtual.const> const
%type <Var.t m> var

%%

module_:
  | name = MODULE elts = list(module_elt) EOF
    {
      M.run begin
        let+ funs, typs, data =
          let init = [], [], [] in
          M.List.fold_right elts ~init ~f:(fun x (funs, typs, data) ->
              reset >>= fun () -> x >>| function
              | `func f -> f :: funs, typs, data
              | `typ  t -> funs, t :: typs, data
              | `data d -> funs, typs, d :: data) in
        Virtual.Module.create ~funs ~typs ~data ~name ()
      end Env.empty |> Context.map ~f:fst
    }

module_elt:
  | f = func { let+ f = f in `func f }
  | t = typ { !!(`typ t) }
  | d = data { let+ d = d in `data d }

data:
  | l = option(linkage) DATA name = SYM EQUALS align = option(align) LBRACE elts = separated_nonempty_list(COMMA, data_elt) RBRACE
    {
      let linkage = Core.Option.value l ~default:Linkage.default_static in
      match Virtual.Data.create () ~name ~elts ~linkage ~align with
      | Error err -> M.lift @@ Context.fail err
      | Ok d -> !!d
    }

data_elt:
  | c = const { (c :> Virtual.Data.elt) }
  | B s = STRING { `string s }
  | Z n = NUM { `zero n }

typ:
  | TYPE name = TYPENAME EQUALS LBRACE fields = separated_nonempty_list(COMMA, typ_field) RBRACE
    { `compound (name, None, fields) }
  | TYPE name = TYPENAME EQUALS align = align LBRACE t = typ_fields_or_opaque RBRACE
    {
      match t with
      | `opaque n -> `opaque (name, align, n)
      | `fields f -> `compound (name, Some align, f)
    }

align:
  | ALIGN n = NUM { n }

typ_fields_or_opaque:
  | n = NUM { `opaque n }
  | fs = separated_nonempty_list(COMMA, typ_field) { `fields fs }

typ_field:
  | b = type_basic n = option(NUM) { `elt (b, Core.Option.value n ~default:1) }
  | s = TYPENAME n = option(NUM) { `name (s, Core.Option.value n ~default:1) }

func:
  | l = option(linkage) FUNCTION return = option(type_basic) name = SYM LPAREN args = option(func_args) RPAREN LBRACE blks = nonempty_list(blk) RBRACE
    { make_fn blks args l name return false }
  | l = option(linkage) NORETURN FUNCTION return = option(type_basic) name = SYM LPAREN args = option(func_args) RPAREN LBRACE blks = nonempty_list(blk) RBRACE
    { make_fn blks args l name return true }

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

type_special:
  | F { `flag }

type_arg:
  | b = type_basic { (b :> Type.arg) }
  | n = TYPENAME { `name n }

type_blk_arg:
  | b = type_basic { (b :> Virtual.Blk.arg_typ) }
  | s = type_special { (s :> Virtual.Blk.arg_typ) }

linkage:
  | section = option(section) EXPORT { Linkage.create () ~section ~export:true }
  | s = section { Linkage.create () ~section:(Some s) ~export:false }

section:
  | SECTION s = STRING { s }

blk:
  | ln = LABEL COLON insns = list(insn) ctrl = ctrl
    {
      let* l = label_of_name ln
      and* insns = unwrap_list insns
      and* ctrl = ctrl in
      M.lift @@ Context.Virtual.blk' () ~label:(Some l) ~insns ~ctrl
    }
  | ln = LABEL LPAREN args = separated_nonempty_list(COMMA, blk_arg) RPAREN COLON insns = list(insn) ctrl = ctrl
    {
      let* l = label_of_name ln
      and* args = unwrap_list args
      and* insns = unwrap_list insns
      and* ctrl = ctrl in
      M.lift @@ Context.Virtual.blk' () ~label:(Some l) ~args ~insns ~ctrl
    }

blk_arg:
  | t = type_blk_arg v = var { let+ v = v in v, t }

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
  | t = SW i = ctrl_index COMMA def = local LSQUARE tbl = separated_nonempty_list(COMMA, ctrl_table_entry) RSQUARE
    {
      let* i = i and* d = def and* tbl = unwrap_list tbl in
      let* tbl = M.List.map tbl ~f:(fun ((i, t'), l) ->
          if not @@ Type.equal_imm t t' then
            M.lift @@
            Context.fail @@
            Core.Error.of_string @@
            Format.asprintf "Invalid switch value %a_%a, expected size %a"
              Bv.pp i Type.pp_imm t' Type.pp_imm t
          else !!(i, l)) in
      match Virtual.Ctrl.Table.create tbl t with
      | Error err -> M.lift @@ Context.fail err
      | Ok tbl -> !!(`sw (t, i, d, tbl))
    }

ctrl_index:
  | x = var { let+ x = x in `var x }
  | s = SYM { !!(`sym (s, 0)) }
  | s = SYM PLUS i = NUM { !!(`sym (s, i)) }
  | s = SYM MINUS i = NUM { !!(`sym (s, -i)) }

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
  | x = var t = SEL c = var COMMA l = operand COMMA r = operand
    {
      let+ x = x and+ c = c and+ l = l and+ r = r in
      `sel (x, t, c, l, r)
    }
  | x = var t = ACALL f = global LPAREN args = call_args RPAREN
    {
      let+ x = x and+ f = f and+ args = args in
      let args, vargs = Core.List.partition_map args ~f:(function
        | `arg a -> First a | `varg a -> Second a) in
      `call (Some (x, t), f, args, vargs)
    }
  | CALL f = global LPAREN args = call_args RPAREN
    {
      let+ f = f and+ args = args in
      let args, vargs = Core.List.partition_map args ~f:(function
        | `arg a -> First a | `varg a -> Second a) in
      `call (None, f, args, vargs)
    }
  | x = var EQUALS t = VAARG y = var
    {
      let+ x = x and+ y = y in
      `vaarg (x, t, y)
    }
  | VASTART x = var { let+ x = x in `vastart x }
  | x = var EQUALS ALLOC i = NUM { let+ x = x in `alloc (x, i) }
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
      | Some a -> let+ a = a in [`arg a]
    }
  | a = operand COMMA rest = call_args
    {
      let+ a = a and+ rest = rest in
      `arg a :: rest
    }
  | a = operand COMMA ELIPSIS COMMA vargs = separated_nonempty_list(COMMA, operand)
    {
      let+ a = a and+ vargs = unwrap_list vargs in
      `arg a :: Core.List.map vargs ~f:(fun a -> `varg a)
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
  | t = REF { `ref t }

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
      let+ args = unwrap_list args and+ l = label_of_name l in
      `label (l, args)
    }

global:
  | i = INT { !!(`addr (fst i)) }
  | s = SYM { !!(`sym s) }
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
  | s = SYM PLUS i = NUM { `sym (s, i) }
  | s = SYM MINUS i = NUM { `sym (s, -i) }

var:
  | x = VAR { !!Var.(with_index (create (fst x)) (snd x)) }
  | x = IDENT { !!(Var.create x) }
  | x = TEMP { temp_of_name x }
  | x = TEMPI { temp_of_name (fst x) ~index:(snd x) }
