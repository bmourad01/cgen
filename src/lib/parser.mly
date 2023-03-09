 %{
    open Monads.Std

    type elt = [
      | `func of Virtual.func
      | `typ of Type.compound
      | `data of Virtual.data
    ]

    type call_arg = [
      | `arg of Virtual.Insn.arg
      | `varg of Virtual.Insn.arg
    ]

    module Env = struct
      (* Since we allow a nicer surface syntax over the internal
         representation of the IR, we need to do some bookkeeping.

         This mostly applies when using human-readable names in
         place of uniquely identified data.
       *)
      type t = {
        labels : Label.t Core.String.Map.t;
      }

      let empty = {labels = Core.String.Map.empty}
    end

    module M = Monad.State.Make(Env)(Context)

    type 'a m = 'a Monad.State.T1(Env)(Context).t
    
    open M.Syntax
    open M.Let

    (* Each time parse a new function, reset the context, since
       labels do not have scope outside of a function body. *)
    let reset = M.put {labels = Core.String.Map.empty}
    
    let label_of_name name =
      let* env = M.get () in
      match Core.Map.find env.labels name with
      | Some l -> !!l
      | None ->
         let* l = M.lift @@ Context.Label.fresh in
         let labels = Core.Map.set env.labels ~key:name ~data:l in
         let+ () = M.put {labels} in
         l

    let unwrap_list = M.List.map ~f:(fun x -> x >>| Core.Fn.id)

    let pp_pos ppf pos =
      let open Lexing in
      Format.fprintf ppf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

    let make_fn blks args l name return noreturn =
      let* blks = unwrap_list blks in
      let args, variadic = match args with
        | None -> [], false
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
%token <Type.imm> UDIV UREM AND OR SAR SHL SHR XOR NOT
%token ALLOC
%token <Type.basic> LOAD STORE EQ GE GT LE LT NE
%token <Type.imm> SGE SGT SLE SLT
%token <Type.fp> O UO
%token <Type.basic> BITS
%token <Type.fp * Type.imm> FTOSI FTOUI
%token <Type.fp> FTRUNC
%token <Type.imm> ITRUNC SEXT ZEXT
%token <Type.imm * Type.fp> SITOF UITOF
%token <Type.basic> COPY SELECT ACALL
%token CALL
%token VASTART
%token HLT
%token JMP
%token JNZ
%token RET
%token <Type.imm> SWITCH
%token MODULE
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

%start module_

%type <Virtual.module_ Context.t> module_
%type <elt m> module_elt
%type <Virtual.data m> data
%type <Virtual.Data.elt> data_elt
%type <Type.compound> typ
%type <int> align
%type <Type.field> typ_field
%type <Virtual.func m> func
%type <(Var.t * Type.arg) list * bool> func_args
%type <Type.basic> type_basic
%type <Type.special> type_special
%type <Type.arg> type_arg
%type <Virtual.Blk.arg_typ> type_blk_arg
%type <Linkage.t> linkage
%type <string> section
%type <Virtual.blk m> blk
%type <Var.t * Virtual.Blk.arg_typ> blk_arg
%type <Virtual.Insn.Ctrl.t m> insn_ctrl
%type <(Bitvec.t * Virtual.Insn.local) m> insn_ctrl_table_entry
%type <Virtual.Insn.Data.t> insn_data
%type <call_arg list> call_args
%type <Virtual.Insn.Data.binop> insn_data_binop
%type <Virtual.Insn.Data.unop> insn_data_unop
%type <Virtual.Insn.Data.arith_binop> insn_data_arith_binop
%type <Virtual.Insn.Data.bitwise_binop> insn_data_bitwise_binop
%type <Virtual.Insn.Data.cmp> insn_data_cmp
%type <Virtual.Insn.Data.arith_unop> insn_data_arith_unop
%type <Virtual.Insn.Data.bitwise_unop> insn_data_bitwise_unop
%type <Virtual.Insn.Data.cast> insn_data_cast
%type <Virtual.Insn.Data.copy> insn_data_copy
%type <Virtual.Insn.Data.mem> insn_data_mem
%type <Virtual.Insn.dst m> insn_dst
%type <Virtual.Insn.local m> insn_local
%type <Virtual.Insn.global> insn_global
%type <Virtual.Insn.arg> insn_arg
%type <Virtual.const> const
%type <Var.t> var
%type <string> ident

%%

module_:
  | MODULE name = ident elts = list(module_elt) EOF
    {
      M.run begin
        let+ funs, typs, data =
          let init = [], [], [] in
          M.List.fold_right elts ~init ~f:(fun x (funs, typs, data) ->
              reset >>= fun () -> x >>| function
              | `func f -> f :: funs, typs, data
              | `typ t -> funs, t :: typs, data
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
  | l = option(linkage) FUNCTION return = option(type_arg) name = SYM LPAREN args = option(func_args) RPAREN LBRACE blks = nonempty_list(blk) RBRACE
    { make_fn blks args l name return false }
  | l = option(linkage) NORETURN FUNCTION return = option(type_arg) name = SYM LPAREN args = option(func_args) RPAREN LBRACE blks = nonempty_list(blk) RBRACE
    { make_fn blks args l name return true }

func_args:
  | ELIPSIS { [], true }
  | t = type_arg x = var { [x, t], false }
  | t = type_arg x = var COMMA rest = func_args
    { (x, t) :: fst rest, snd rest }

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
  | ln = LABEL COLON data = list(insn_data) ctrl = insn_ctrl
    {
      let* l = label_of_name ln and* ctrl = ctrl in
      M.lift @@ Context.Virtual.blk' () ~label:(Some l) ~data ~ctrl
    }
  | ln = LABEL LPAREN args = separated_nonempty_list(COMMA, blk_arg) RPAREN COLON data = list(insn_data) ctrl = insn_ctrl
    {
      let* l = label_of_name ln and* ctrl = ctrl in
      M.lift @@ Context.Virtual.blk' () ~label:(Some l) ~args ~data ~ctrl
    }

blk_arg:
  | t = type_blk_arg v = var { v, t }

insn_ctrl:
  | HLT { !!`hlt }
  | JMP d = insn_dst
    { d >>| fun d -> `jmp d }
  | JNZ c = var COMMA t = insn_dst COMMA f = insn_dst
    { t >>= fun t -> f >>| fun f -> `jnz (c, t, f) }
  | RET a = option(insn_arg)
    { !!(`ret a) }
  | t = SWITCH i = var COMMA def = insn_local tbl = separated_nonempty_list(COMMA, insn_ctrl_table_entry)
    {
      let* d = def and* tbl = unwrap_list tbl in
      match Virtual.Insn.Ctrl.Table.create tbl with
      | Error err -> M.lift @@ Context.fail err
      | Ok tbl -> !!(`switch (t, i, d, tbl))
    }

insn_ctrl_table_entry:
  | i = INT ARROW l = insn_local { l >>| fun l -> i, l }

insn_data:
  | x = var EQUALS b = insn_data_binop l = insn_arg COMMA r = insn_arg
    { `binop (x, b, l, r) }
  | x = var EQUALS u = insn_data_unop a = insn_arg
    { `unop (x, u, a) }
  | x = var EQUALS m = insn_data_mem
    { `mem (x, m) }
  | x = var t = SELECT c = var COMMA l = insn_arg COMMA r = insn_arg
    { `select (x, t, c, l, r) }
  | x = var t = ACALL f = insn_global LPAREN args = call_args RPAREN
    {
      let args, vargs = Core.List.partition_map args ~f:(function
        | `arg a -> First a | `varg a -> Second a) in
      `acall (x, t, f, args, vargs)
    }
  | CALL f = insn_global LPAREN args = call_args RPAREN
    {
      let args, vargs = Core.List.partition_map args ~f:(function
        | `arg a -> First a | `varg a -> Second a) in
      `call (f, args, vargs)
    }
  | VASTART x = var
    { `vastart x }

call_args:
  | a = option(insn_arg)
    {
      match a with
      | None -> []
      | Some a -> [`arg a]
    }
  | a = insn_arg COMMA rest = call_args
    { `arg a :: rest }
  | a = insn_arg COMMA ELIPSIS COMMA vargs = separated_nonempty_list(COMMA, insn_arg)
    { `arg a :: Core.List.map vargs ~f:(fun a -> `varg a)  }

insn_data_binop:
  | a = insn_data_arith_binop { (a :> Virtual.Insn.Data.binop) }
  | b = insn_data_bitwise_binop { (b :> Virtual.Insn.Data.binop) }
  | c = insn_data_cmp { (c :> Virtual.Insn.Data.binop) }

insn_data_unop:
  | a = insn_data_arith_unop { (a :> Virtual.Insn.Data.unop) }
  | b = insn_data_bitwise_unop { (b :> Virtual.Insn.Data.unop) }
  | c = insn_data_cast { (c :> Virtual.Insn.Data.unop) }
  | c = insn_data_copy { (c :> Virtual.Insn.Data.unop) }

insn_data_arith_binop:
  | t = ADD { `add t }
  | t = DIV { `div t }
  | t = MUL { `mul t }
  | t = REM { `rem t }
  | t = SUB { `sub t }
  | t = UDIV { `udiv t }
  | t = UREM { `urem t }

insn_data_bitwise_binop:
  | t = AND { `and_ t }
  | t = OR { `or_ t }
  | t = SAR { `sar t }
  | t = SHL { `shl t }
  | t = SHR { `shr t }
  | t = XOR { `xor t }

insn_data_cmp:
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

insn_data_arith_unop:
  | t = NEG { `neg t }

insn_data_bitwise_unop:
  | t = NOT { `not_ t }

insn_data_cast:
  | t = BITS { `bits t }
  | t = FTOSI { `ftosi (fst t, snd t) }
  | t = FTOUI { `ftoui (fst t, snd t) }
  | t = FTRUNC { `ftrunc t }
  | t = ITRUNC { `itrunc t }
  | t = SEXT { `sext t }
  | t = SITOF { `sitof (fst t, snd t) }
  | t = UITOF { `uitof (fst t, snd t) }
  | t = ZEXT { `zext t }

insn_data_copy:
  | t = COPY { `copy t }

insn_data_mem:
  | ALLOC i = INT
    { `alloc (Bitvec.to_int i) }
  | t = LOAD m = var LSQUARE a = insn_arg RSQUARE
    { `load (t, m, a) }
  | t = STORE m = var LSQUARE a = insn_arg RSQUARE COMMA x = insn_arg
    { `store (t, m, a, x) }

insn_dst:
  | g = insn_global { !!(g :> Virtual.Insn.dst) }
  | l = insn_local { l >>| fun l -> (l :> Virtual.Insn.dst) }

insn_local:
  | l = LABEL { label_of_name l >>| fun l -> `label (l, None) }
  | l = LABEL LPAREN a = insn_arg RPAREN
    { label_of_name l >>| fun l -> `label (l, Some a) }

insn_global:
  | i = INT { `addr i }
  | s = SYM { `sym s }
  | x = var { `var x }

insn_arg:
  | c = const { (c :> Virtual.Insn.arg) }
  | x = var { `var x }

const:
  | i = INT { `int i }
  | s = SINGLE { `float s }
  | d = DOUBLE { `double d }
  | s = SYM { `sym (s, 0) }
  | s = SYM PLUS i = INT { `sym (s, Bitvec.to_int i) }
  | s = SYM MINUS i = INT { `sym (s, -(Bitvec.to_int i)) }

var:
  | x = VAR { Var.(with_index (create (fst x)) (snd x)) }
  | x = ident { Var.create x }

ident:
  | x = IDENT { x }
  | W { "w" }
  | L { "l" }
  | B { "b" }
  | H { "h" }
  | S { "s" }
  | D { "d" }
  | Z { "z" }
  | M { "m" }
  | F { "f" }
