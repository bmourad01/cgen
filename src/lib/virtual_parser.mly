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

    let pp_pos ppf pos =
      let open Lexing in
      Format.fprintf ppf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

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
%token W L B H S D Z M F
%token <Type.basic> ADD DIV MUL REM SUB NEG
%token <Type.imm> UDIV UREM AND OR ASR LSL LSR ROL ROR XOR NOT
%token ALLOC
%token <Type.basic> LOAD STORE EQ GE GT LE LT NE
%token <Type.imm> SGE SGT SLE SLT
%token <Type.fp> O UO
%token <Type.basic> BITS
%token <Type.fp * Type.imm> FTOSI FTOUI
%token <Type.fp> FEXT FTRUNC
%token <Type.imm> ITRUNC SEXT ZEXT
%token <Type.imm * Type.fp> SITOF UITOF
%token <Type.basic> COPY SEL ACALL
%token CALL
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
%token <Bitvec.t> INT
%token <float> DOUBLE
%token <Float32.t> SINGLE
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
%type <(Bitvec.t * Virtual.local) m> ctrl_table_entry
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
%type <Virtual.Insn.mem m> insn_mem
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
  | f = func { f >>| fun f -> `func f }
  | t = typ { !!(`typ t) }
  | d = data { d >>| fun d -> `data d }

data:
  | l = option(linkage) DATA name = SYM EQUALS align = option(align) LBRACE elts = separated_nonempty_list(COMMA, data_elt) RBRACE
    {
      let linkage = Core.Option.value l ~default:Linkage.default_static in
      match Virtual.Data.create () ~name ~elts ~linkage ~align with
      | Error err -> M.lift @@ Context.fail err
      | Ok d -> !!d
    }

data_elt:
  | b = type_basic cs = nonempty_list(const) { `basic (b, cs) }
  | B s = STRING { `string s }
  | Z n = INT { `zero (Bitvec.to_int n) }
  | s = SYM { `sym (s, 0) }
  | s = SYM PLUS i = INT { `sym (s, Bitvec.to_int i) }
  | s = SYM MINUS i = INT { `sym (s, -(Bitvec.to_int i)) }

typ:
  | TYPE name = TYPENAME EQUALS align = option(align) LBRACE fields = separated_nonempty_list(COMMA, typ_field) RBRACE
    { `compound (name, align, fields) }

align:
  | ALIGN n = INT { Bitvec.to_int n }

typ_field:
  | b = type_basic n = option(INT)
    {
      let n = Core.Option.value_map n ~default:1 ~f:Bitvec.to_int in
      `elt (b, n)
    }
  | n = TYPENAME { `name n }

func:
  | l = option(linkage) FUNCTION return = option(type_basic) name = SYM LPAREN args = option(func_args) RPAREN LBRACE blks = nonempty_list(blk) RBRACE
    { make_fn blks args l name return false }
  | l = option(linkage) NORETURN FUNCTION return = option(type_basic) name = SYM LPAREN args = option(func_args) RPAREN LBRACE blks = nonempty_list(blk) RBRACE
    { make_fn blks args l name return true }

func_args:
  | ELIPSIS { !!([], true) }
  | t = type_arg x = var { x >>| fun x -> [x, t], false }
  | t = type_arg x = var COMMA rest = func_args
    {
      rest >>= fun rest ->
      x >>| fun x ->
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
  | M { `mem }
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
  | t = type_blk_arg v = var { v >>| fun v -> v, t }

ctrl:
  | HLT { !!`hlt }
  | JMP d = dst
    { d >>| fun d -> `jmp d }
  | BR c = var COMMA t = dst COMMA f = dst
    {
      c >>= fun c ->
      t >>= fun t ->
      f >>| fun f ->
      `br (c, t, f)
    }
  | RET a = option(operand)
    {
      match a with
      | None -> !!(`ret None)
      | Some a -> a >>| fun a -> `ret (Some a)
    }
  | t = SW i = var COMMA def = local LSQUARE tbl = separated_nonempty_list(COMMA, ctrl_table_entry) RSQUARE
    {
      let* i = i and* d = def and* tbl = unwrap_list tbl in
      match Virtual.Ctrl.Table.create tbl with
      | Error err -> M.lift @@ Context.fail err
      | Ok tbl -> !!(`sw (t, i, d, tbl))
    }

ctrl_table_entry:
  | i = INT ARROW l = local { l >>| fun l -> i, l }

insn:
  | x = var EQUALS b = insn_binop l = operand COMMA r = operand
    {
      x >>= fun x ->
      l >>= fun l ->
      r >>| fun r ->
      `bop (x, b, l, r)
    }
  | x = var EQUALS u = insn_unop a = operand
    {
      x >>= fun x ->
      a >>| fun a ->
      `uop (x, u, a)
    }
  | x = var EQUALS m = insn_mem
    {
      x >>= fun x ->
      m >>| fun m ->
      `mem (x, m)
    }
  | x = var t = SEL c = var COMMA l = operand COMMA r = operand
    {
      x >>= fun x ->
      c >>= fun c ->
      l >>= fun l ->
      r >>| fun r ->
      `sel (x, t, c, l, r)
    }
  | x = var t = ACALL f = global LPAREN args = call_args RPAREN
    {
      x >>= fun x ->
      f >>= fun f ->
      args >>| fun args ->
      let args, vargs = Core.List.partition_map args ~f:(function
        | `arg a -> First a | `varg a -> Second a) in
      `call (Some (x, t), f, args, vargs)
    }
  | CALL f = global LPAREN args = call_args RPAREN
    {
      f >>= fun f ->
      args >>| fun args ->
      let args, vargs = Core.List.partition_map args ~f:(function
        | `arg a -> First a | `varg a -> Second a) in
      `call (None, f, args, vargs)
    }
  | VASTART x = var
    { x >>| fun x -> `vastart x }

call_args:
  | a = option(operand)
    {
      match a with
      | None -> !![]
      | Some a -> a >>| fun a -> [`arg a]
    }
  | a = operand COMMA rest = call_args
    {
      a >>= fun a ->
      rest >>| fun rest ->
      `arg a :: rest
    }
  | a = operand COMMA ELIPSIS COMMA vargs = separated_nonempty_list(COMMA, operand)
    {
      a >>= fun a ->
      unwrap_list vargs >>| fun vargs ->
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
  | t = NOT { `not_ t }

insn_cast:
  | t = BITS { `bits t }
  | t = FEXT { `fext t }
  | t = FTOSI { `ftosi (fst t, snd t) }
  | t = FTOUI { `ftoui (fst t, snd t) }
  | t = FTRUNC { `ftrunc t }
  | t = ITRUNC { `itrunc t }
  | t = SEXT { `sext t }
  | t = SITOF { `sitof (fst t, snd t) }
  | t = UITOF { `uitof (fst t, snd t) }
  | t = ZEXT { `zext t }

insn_copy:
  | t = COPY { `copy t }

insn_mem:
  | ALLOC i = INT
    { !!(`alloc (Bitvec.to_int i)) }
  | t = LOAD m = var LSQUARE a = operand RSQUARE
    {
      m >>= fun m ->
      a >>| fun a ->
      `load (t, m, a)
    }
  | t = STORE m = var LSQUARE a = operand RSQUARE COMMA x = operand
    {
      m >>= fun m ->
      a >>= fun a ->
      x >>| fun x ->
      `store (t, m, a, x)
    }

dst:
  | g = global { g >>| fun g -> (g :> Virtual.dst) }
  | l = local { l >>| fun l -> (l :> Virtual.dst) }

local:
  | l = LABEL { label_of_name l >>| fun l -> `label (l, []) }
  | l = LABEL LPAREN args = separated_nonempty_list(COMMA, operand) RPAREN
    {
      unwrap_list args >>= fun args ->
      label_of_name l >>| fun l -> `label (l, args)
    }

global:
  | i = INT { !!(`addr i) }
  | s = SYM { !!(`sym s) }
  | x = var { x >>| fun x -> `var x }

operand:
  | c = const { !!(c :> Virtual.operand) }
  | x = var { x >>| fun x -> `var x }

const:
  | i = INT { `int i }
  | s = SINGLE { `float s }
  | d = DOUBLE { `double d }
  | s = SYM { `sym (s, 0) }
  | s = SYM PLUS i = INT { `sym (s, Bitvec.to_int i) }
  | s = SYM MINUS i = INT { `sym (s, -(Bitvec.to_int i)) }

var:
  | x = VAR { !!Var.(with_index (create (fst x)) (snd x)) }
  | x = IDENT { !!(Var.create x) }
  | x = TEMP { temp_of_name x }
  | x = TEMPI { temp_of_name (fst x) ~index:(snd x) }
