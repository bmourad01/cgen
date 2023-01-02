open Core
open Graphlib.Std
open Monads.Std
open Regular.Std

module Bitvec = struct
  include Bitvec
  include Bitvec_binprot
  include Bitvec_order
  include Bitvec_sexp
end

let var_set_of_option = function
  | Some x -> Var.Set.singleton x
  | None -> Var.Set.empty

module Array = struct
  include Array

  let insert xs x i = length xs |> succ |> init ~f:(fun j ->
      if j < i then xs.(j) else if j = i then x else xs.(j - 1))

  let push_back xs x = insert xs x @@ length xs
  let push_front xs x = insert xs x 0

  let remove_if xs ~f =
    if exists xs ~f then filter xs ~f:(Fn.non f) else xs

  let update_if xs y ~f =
    if exists xs ~f then map xs ~f:(fun x -> if f x then y else x) else xs

  let pp ppx sep ppf xs =
    let last = length xs - 1 in
    iteri xs ~f:(fun i x ->
        Format.fprintf ppf "%a" ppx x;
        if i < last then sep ppf)

  let findi_label xs f l = findi xs ~f:(fun _ x -> Label.equal l @@ f x)

  let next xs f l =
    let open Monad.Option.Syntax in
    findi_label xs f l >>= fun (i, _) ->
    if i = length xs - 1 then None else Some xs.(i + 1)

  let prev xs f l =
    let open Monad.Option.Syntax in
    findi_label xs f l >>= fun (i, _) ->
    if i = 0 then None else Some xs.(i - 1)

  let enum ?(rev = false) xs =
    let n = length xs in
    if not rev then Seq.init n ~f:(unsafe_get xs)
    else Seq.init n ~f:(fun i -> unsafe_get xs (n - i - 1))
end

type const = [
  | `int    of Bitvec.t
  | `float  of Float32.t
  | `double of float
  | `sym    of string * int
] [@@deriving bin_io, compare, equal, sexp]

let pp_const ppf : const -> unit = function
  | `int n -> Format.fprintf ppf "%a" Bitvec.pp n
  | `float f -> Format.fprintf ppf "%s" @@ Float32.to_string f
  | `double d -> Format.fprintf ppf "%a" Float.pp d
  | `sym (s, 0) -> Format.fprintf ppf "@@%s" s
  | `sym (s, n) when n > 0 -> Format.fprintf ppf "@@%s+0x%x" s n
  | `sym (s, n) -> Format.fprintf ppf "@@%s-0x%x" s (lnot n + 1)

module Insn = struct
  type arg = [
    | const
    | `var of Var.t
  ] [@@deriving bin_io, compare, equal, sexp]

  let var_of_arg = function
    | `var v -> Some v
    | _ -> None

  let pp_arg ppf : arg -> unit = function
    | #const as c -> Format.fprintf ppf "%a" pp_const c
    | `var v -> Format.fprintf ppf "%a" Var.pp v

  type global = [
    | `addr of Bitvec.t
    | `sym  of string
    | `var  of Var.t
  ] [@@deriving bin_io, compare, equal, sexp]

  let pp_global ppf : global -> unit = function
    | `addr a -> Format.fprintf ppf "#%a" Bitvec.pp a
    | `sym s -> Format.fprintf ppf "@%s" s
    | `var v -> Format.fprintf ppf "%a" Var.pp v

  type local = [
    | `label of Label.t
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  let pp_local ppf : local -> unit = function
    | `label l -> Format.fprintf ppf "%a" Label.pp l

  let pp_local_hum ppf : local -> unit = function
    | `label l -> Format.fprintf ppf "%a" Label.pp_hum l

  type dst = [
    | global
    | local
  ] [@@deriving bin_io, compare, equal, sexp]

  let pp_dst ppf : dst -> unit = function
    | #global as g -> Format.fprintf ppf "%a" pp_global g
    | #local as l -> Format.fprintf ppf "%a" pp_local l

  let pp_dst_hum ppf : dst -> unit = function
    | #global as g -> Format.fprintf ppf "%a" pp_global g
    | #local as l -> Format.fprintf ppf "%a" pp_local_hum l

  module Phi = struct
    type t = {
      lhs : Var.t;
      typ : [Type.basic | Type.special];
      ins : arg Label.Map.t;
    } [@@deriving bin_io, compare, equal, sexp]

    let create_exn ?(ins = []) ~lhs ~typ () = try {
      lhs;
      typ;
      ins = Label.Map.of_alist_exn ins;
    } with exn -> invalid_argf "%s" (Exn.to_string exn) ()

    let create ?(ins = []) ~lhs ~typ () =
      Or_error.try_with @@ create_exn ~lhs ~typ ~ins

    let lhs p = p.lhs
    let typ p = p.typ
    let ins p = Map.to_sequence p.ins
    let has_lhs p v = Var.(p.lhs = v)
    let with_lhs p lhs = {p with lhs}
    let update p l a = {p with ins = Map.set p.ins ~key:l ~data:a}

    let free_vars p =
      let f = Fn.compose var_of_arg snd in
      ins p |> Seq.filter_map ~f |> Var.Set.of_sequence

    let pp_in ppl ppf (l, x) = Format.fprintf ppf "%a -> %a" ppl l pp_arg x

    let pp_self ppl ppf p =
      let pp_sep ppf () = Format.fprintf ppf ",@;" in
      Format.fprintf ppf "%a = phi.%a [@[<v 0>%a@]]"
        Var.pp p.lhs Type.pp (p.typ :> Type.t)
        (Format.pp_print_list ~pp_sep (pp_in ppl)) (Map.to_alist p.ins)

    let pp = pp_self Label.pp
    let pp_hum = pp_self Label.pp_hum
  end

  module Data = struct
    type arith = [
      | `add  of Type.basic * arg * arg
      | `div  of Type.basic * arg * arg
      | `mul  of Type.basic * arg * arg
      | `neg  of Type.basic * arg
      | `rem  of Type.basic * arg * arg
      | `sub  of Type.basic * arg * arg
      | `udiv of Type.imm   * arg * arg
      | `urem of Type.imm   * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_arith : arith -> Var.Set.t = function
      | `add  (_, l, r)
      | `div  (_, l, r)
      | `mul  (_, l, r)
      | `rem  (_, l, r)
      | `sub  (_, l, r)
      | `udiv (_, l, r)
      | `urem (_, l, r) ->
        List.filter_map [l; r] ~f:var_of_arg |> Var.Set.of_list
      | `neg  (_, a) -> var_set_of_option @@ var_of_arg a

    let pp_arith ppf : arith -> unit = function
      | `add (t, x, y) ->
        Format.fprintf ppf "add.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `div (t, x, y) ->
        Format.fprintf ppf "div.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `mul (t, x, y) ->
        Format.fprintf ppf "mul.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `neg (t, x) ->
        Format.fprintf ppf "neg.%a %a" Type.pp_basic t pp_arg x
      | `rem (t, x, y) ->
        Format.fprintf ppf "rem.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `sub (t, x, y) ->
        Format.fprintf ppf "sub.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `udiv (t, x, y) ->
        Format.fprintf ppf "urem.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `urem (t, x, y) ->
        Format.fprintf ppf "udiv.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y

    type bits = [
      | `and_ of Type.imm * arg * arg
      | `or_  of Type.imm * arg * arg
      | `sar  of Type.imm * arg * arg
      | `shl  of Type.imm * arg * arg
      | `shr  of Type.imm * arg * arg
      | `xor  of Type.imm * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_bits : bits -> Var.Set.t = function
      | `and_ (_, l, r)
      | `or_  (_, l, r)
      | `sar  (_, l, r)
      | `shl  (_, l, r)
      | `shr  (_, l, r)
      | `xor  (_, l, r) ->
        List.filter_map [l; r] ~f:var_of_arg |> Var.Set.of_list

    let pp_bits ppf : bits -> unit = function
      | `and_ (t, x, y) ->
        Format.fprintf ppf "and.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `or_ (t, x, y) ->
        Format.fprintf ppf "or.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `sar (t, x, y) ->
        Format.fprintf ppf "sar.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `shl (t, x, y) ->
        Format.fprintf ppf "shl.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `shr (t, x, y) ->
        Format.fprintf ppf "shr.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `xor (t, x, y) ->
        Format.fprintf ppf "xor.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y

    type mem = [
      | `alloc of int
      | `load  of Type.basic * Var.t * arg
      | `store of Type.basic * Var.t * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_mem : mem -> Var.Set.t = function
      | `load  (_, x, a) ->
        var_of_arg a |> Option.to_list |> List.cons x |> Var.Set.of_list
      | `store (_, x, a, v) ->
        List.filter_map [a; v] ~f:var_of_arg |> List.cons x |> Var.Set.of_list
      | `alloc _ -> Var.Set.empty

    let pp_mem ppf : mem -> unit = function
      | `alloc n ->
        Format.fprintf ppf "alloc %d" n
      | `load (t, m, p) ->
        Format.fprintf ppf "ld.%a %a[%a]" Type.pp_basic t Var.pp m pp_arg p
      | `store (t, m, p, x) ->
        Format.fprintf ppf "st.%a %a[%a], %a"
          Type.pp_basic t Var.pp m pp_arg p pp_arg x

    type cmp = [
      | `eq  of Type.basic * arg * arg
      | `ge  of Type.basic * arg * arg
      | `gt  of Type.basic * arg * arg
      | `le  of Type.basic * arg * arg
      | `lt  of Type.basic * arg * arg
      | `ne  of Type.basic * arg * arg
      | `o   of Type.imm   * arg * arg
      | `sge of Type.imm   * arg * arg
      | `sgt of Type.imm   * arg * arg
      | `sle of Type.imm   * arg * arg
      | `slt of Type.imm   * arg * arg
      | `uo  of Type.imm   * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_cmp : cmp -> Var.Set.t = function
      | `eq  (_, l, r)
      | `ge  (_, l, r)
      | `gt  (_, l, r)
      | `le  (_, l, r)
      | `lt  (_, l, r)
      | `ne  (_, l, r)
      | `o   (_, l, r)
      | `sge (_, l, r)
      | `sgt (_, l, r)
      | `sle (_, l, r)
      | `slt (_, l, r)
      | `uo  (_, l, r) ->
        List.filter_map [l; r] ~f:var_of_arg |> Var.Set.of_list

    let pp_cmp ppf : cmp -> unit = function
      | `eq (t, x, y) ->
        Format.fprintf ppf "eq.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `ge (t, x, y) ->
        Format.fprintf ppf "ge.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `gt (t, x, y) ->
        Format.fprintf ppf "gt.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `le (t, x, y) ->
        Format.fprintf ppf "le.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `lt (t, x, y) ->
        Format.fprintf ppf "lt.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `ne (t, x, y) ->
        Format.fprintf ppf "ne.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `o (t, x, y) ->
        Format.fprintf ppf "o.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `sge (t, x, y) ->
        Format.fprintf ppf "sge.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `sgt (t, x, y) ->
        Format.fprintf ppf "sgt.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `sle (t, x, y) ->
        Format.fprintf ppf "sle.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `slt (t, x, y) ->
        Format.fprintf ppf "slt.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y
      | `uo (t, x, y) ->
        Format.fprintf ppf "uo.%a %a, %a" Type.pp_imm t pp_arg x pp_arg y

    type cast = [
      | `bits   of Type.basic * arg
      | `ftosi  of Type.fp * Type.imm * arg
      | `ftoui  of Type.fp * Type.imm * arg
      | `ftrunc of Type.fp * arg
      | `itrunc of Type.imm * arg
      | `sext   of Type.imm * arg
      | `sitof  of Type.imm * Type.fp * arg
      | `uitof  of Type.imm * Type.fp * arg
      | `zext   of Type.imm * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_cast : cast -> Var.Set.t = function
      | `bits   (_, a)
      | `ftosi  (_, _, a)
      | `ftoui  (_, _, a)
      | `ftrunc (_, a)
      | `itrunc (_, a)
      | `sext   (_, a)
      | `sitof  (_, _, a)
      | `uitof  (_, _, a)
      | `zext   (_, a) -> var_set_of_option @@ var_of_arg a

    let pp_cast ppf : cast -> unit = function
      | `bits (t, x) ->
        Format.fprintf ppf "cast.%a %a" Type.pp_basic t pp_arg x
      | `ftosi (tf, ti, x) ->
        Format.fprintf ppf "ftosi.%a.%a %a" Type.pp_fp tf Type.pp_imm ti pp_arg x
      | `ftoui (tf, ti, x) ->
        Format.fprintf ppf "ftoui.%a.%a %a" Type.pp_fp tf Type.pp_imm ti pp_arg x
      | `ftrunc (t, x) ->
        Format.fprintf ppf "ftrunc.%a %a" Type.pp_fp t pp_arg x
      | `itrunc (t, x) ->
        Format.fprintf ppf "itrunc.%a %a" Type.pp_imm t pp_arg x
      | `sext (t, x) ->
        Format.fprintf ppf "sext.%a %a" Type.pp_imm t pp_arg x
      | `sitof (ti, tf, x) ->
        Format.fprintf ppf "sitof.%a.%a %a" Type.pp_imm ti Type.pp_fp tf pp_arg x
      | `uitof (ti, tf, x) ->
        Format.fprintf ppf "uitof.%a.%a %a" Type.pp_imm ti Type.pp_fp tf pp_arg x
      | `zext (t, x) ->
        Format.fprintf ppf "zext.%a %a" Type.pp_imm t pp_arg x

    type copy = [
      | `copy   of Type.basic * arg
      | `select of Type.basic * Var.t * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_copy : copy -> Var.Set.t = function
      | `copy (_, a) -> var_set_of_option @@ var_of_arg a
      | `select (_, x, t, f) ->
        List.filter_map [t; f] ~f:var_of_arg |> List.cons x |> Var.Set.of_list

    let pp_copy ppf : copy -> unit = function
      | `copy (t, x) ->
        Format.fprintf ppf "copy.%a %a" Type.pp_basic t pp_arg x
      | `select (t, c, x, y) ->
        Format.fprintf ppf "select.%a %a, %a, %a"
          Type.pp_basic t Var.pp c pp_arg x pp_arg y

    type op = [
      | arith
      | bits
      | mem
      | cmp
      | cast
      | copy
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_op : op -> Var.Set.t = function
      | #arith as a -> free_vars_of_arith a
      | #bits  as b -> free_vars_of_bits b
      | #mem   as m -> free_vars_of_mem m
      | #cmp   as c -> free_vars_of_cmp c
      | #cast  as c -> free_vars_of_cast c
      | #copy  as c -> free_vars_of_copy c

    let pp_op ppf : op -> unit = function
      | #arith as a -> Format.fprintf ppf "%a" pp_arith a
      | #bits  as b -> Format.fprintf ppf "%a" pp_bits b
      | #mem   as m -> Format.fprintf ppf "%a" pp_mem m
      | #cmp   as c -> Format.fprintf ppf "%a" pp_cmp c
      | #cast  as c -> Format.fprintf ppf "%a" pp_cast c
      | #copy  as c -> Format.fprintf ppf "%a" pp_copy c

    type void_call = [
      | `call  of global * arg list
      | `callv of global * arg list
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_void_call : void_call -> Var.Set.t = function
      | `call  (_, args)
      | `callv (_, args) ->
        List.filter_map args ~f:var_of_arg |> Var.Set.of_list

    type assign_call = [
      | `acall  of Var.t * Type.basic * global * arg list
      | `acallv of Var.t * Type.basic * global * arg list
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_assign_call : assign_call -> Var.Set.t = function
      | `acall  (x, _, _, args)
      | `acallv (x, _, _, args) ->
        List.filter_map args ~f:var_of_arg |> List.cons x |> Var.Set.of_list

    type call = [
      | void_call
      | assign_call
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_call : call -> Var.Set.t = function
      | #void_call   as v -> free_vars_of_void_call v
      | #assign_call as a -> free_vars_of_assign_call a

    let is_variadic : call -> bool = function
      | `acallv _ | `callv _ -> true
      | `acall _  | `call _  -> false

    let pp_call_args variadic ppf args =
      let pp_sep ppf () = Format.fprintf ppf ", " in
      Format.pp_print_list ~pp_sep pp_arg ppf args;
      match args, variadic with
      | _, false -> ()
      | [], true -> Format.fprintf ppf "..."
      | _, true  -> Format.fprintf ppf ", ..."

    let pp_call_res ppf = function
      | None -> Format.fprintf ppf "call "
      | Some (x, t) ->
        Format.fprintf ppf "%a = call.%a " Var.pp x Type.pp_basic t

    let pp_call ppf c =
      let res, dst, args, pp_args = match c with
        | `acall (v, t, d, a) -> Some (v, t), d, a, pp_call_args false
        | `acallv (v, t, d, a) -> Some (v, t), d, a, pp_call_args true
        | `call (d, a) -> None, d, a, pp_call_args false
        | `callv (d, a) -> None, d, a, pp_call_args true in
      Format.fprintf ppf "%a%a(%a)" pp_call_res res pp_global dst pp_args args

    type t = [
      | call
      | `op of Var.t * op
    ] [@@deriving bin_io, compare, equal, sexp]

    let lhs d = match d with
      | `op     (x, _)
      | `acall  (x, _, _, _)
      | `acallv (x, _, _, _) -> Some x
      | `call   _
      | `callv  _ -> None

    let has_lhs d v = match lhs d with
      | Some x -> Var.(x = v)
      | None -> false

    let free_vars : t -> Var.Set.t = function
      | #call as c -> free_vars_of_call c
      | `op (_, o) -> free_vars_of_op o

    let pp ppf = function
      | #call as c -> pp_call ppf c
      | `op (l, r) -> Format.fprintf ppf "%a = %a" Var.pp l pp_op r
  end

  module Ctrl = struct
    module Table = struct
      type t = Label.t Map.M(Bitvec).t [@@deriving bin_io, compare, equal, sexp]

      let create_exn l = try Map.of_alist_exn (module Bitvec) l with
        | exn -> invalid_argf "%s" (Exn.to_string exn) ()

      let create l = Or_error.try_with @@ fun () -> create_exn l
      let enum t = Map.to_sequence t
      let find t v = Map.find t v

      let pp_elt ppl ppf (v, l) =
        Format.fprintf ppf "%a -> %a" Bitvec.pp v ppl l

      let pp ppl ppf t =
        let pp_sep ppf () = Format.fprintf ppf ",@;" in
        Format.pp_print_list ~pp_sep (pp_elt ppl) ppf (Map.to_alist t)
    end

    type table = Table.t [@@deriving bin_io, compare, equal, sexp]

    type t = [
      | `jmp    of dst
      | `jnz    of Var.t * dst * dst
      | `ret    of arg option
      | `switch of Type.imm * Var.t * Label.t * table
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars : t -> Var.Set.t = function
      | `jmp _ -> Var.Set.empty
      | `jnz (x, _, _) -> Var.Set.singleton x
      | `ret None -> Var.Set.empty
      | `ret (Some a) -> var_set_of_option @@ var_of_arg a
      | `switch (_, x, _, _) -> Var.Set.singleton x

    let pp_self ppd ppl ppf : t -> unit = function
      | `jmp d ->
        Format.fprintf ppf "jmp %a" ppd d
      | `jnz (c, t, f) ->
        Format.fprintf ppf "jnz %a, %a, %a" Var.pp c ppd t ppd f
      | `ret (Some x) ->
        Format.fprintf ppf "ret %a" pp_arg x
      | `ret None ->
        Format.fprintf ppf "ret"
      | `switch (t, x, ld, tbl) ->
        Format.fprintf ppf "switch.%a %a, %a [@[<v 0>%a@]]"
          Type.pp_imm t Var.pp x Label.pp ld (Table.pp ppl) tbl

    let pp = pp_self pp_dst Label.pp
    let pp_hum = pp_self pp_dst_hum Label.pp_hum
  end

  type 'a t = {
    insn  : 'a;
    label : Label.t;
  } [@@deriving bin_io, compare, equal, sexp]

  type phi = Phi.t t [@@deriving bin_io, compare, equal, sexp]
  type data = Data.t t [@@deriving bin_io, compare, equal, sexp]
  type ctrl = Ctrl.t t [@@deriving bin_io, compare, equal, sexp]

  let phi insn ~label : phi = {insn; label}
  let data insn ~label : data = {insn; label}
  let ctrl insn ~label : ctrl = {insn; label}

  let insn i = i.insn
  let label i = i.label
  let has_label i l = Label.(i.label = l)
  let hash i = Label.hash i.label

  let lhs_of_phi i = Phi.lhs i.insn
  let lhs_of_data i = Data.lhs i.insn

  let map_phi (i : phi) ~f = {i with insn = f i.insn}
  let map_data (i : data) ~f = {i with insn = f i.insn}
  let map_ctrl (i : ctrl) ~f = {i with insn = f i.insn}

  let free_vars_of_phi i = Phi.free_vars i.insn
  let free_vars_of_data i = Data.free_vars i.insn
  let free_vars_of_ctrl i = Ctrl.free_vars i.insn

  let pp ppi ppf i = Format.fprintf ppf "%a: %a" Label.pp i.label ppi i.insn

  let pp_phi = pp Phi.pp
  let pp_data = pp Data.pp
  let pp_ctrl = pp Ctrl.pp

  let pp_phi_hum ppf p = Format.fprintf ppf "%a" Phi.pp_hum p.insn
  let pp_data_hum ppf p = Format.fprintf ppf "%a" Data.pp p.insn
  let pp_ctrl_hum ppf p = Format.fprintf ppf "%a" Ctrl.pp_hum p.insn
end

module Edge = struct
  module T = struct
    type t = [
      | `always
      | `true_ of Var.t
      | `false_ of Var.t
      | `switch of Var.t * Bitvec.t
      | `default of Var.t
    ] [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let pp ppf : t -> unit = function
    | `always -> Format.fprintf ppf "always"
    | `true_ x -> Format.fprintf ppf "%a" Var.pp x
    | `false_ x -> Format.fprintf ppf "~%a" Var.pp x
    | `switch (x, v) -> Format.fprintf ppf "%a = %a" Var.pp x Bitvec.pp v
    | `default x -> Format.fprintf ppf "default(%a)" Var.pp x

  include Regular.Make(struct
      include T
      let module_name = Some "Virtual.Edge"
      let version = "0.1"
      let pp = pp
      let hash e = String.hash @@ Format.asprintf "%a" pp e
    end)
end

type edge = Edge.t [@@deriving bin_io, compare, equal, sexp]

module Blk = struct
  module T = struct
    type t = {
      label : Label.t;
      phi   : Insn.phi array;
      data  : Insn.data array;
      ctrl  : Insn.ctrl;
    } [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let create ?(phi = []) ?(data = []) ~label ~ctrl () = {
    label;
    phi = Array.of_list phi;
    data = Array.of_list data;
    ctrl
  }

  let label b = b.label
  let phi ?(rev = false) b = Array.enum b.phi ~rev
  let data ?(rev = false) b = Array.enum b.data ~rev
  let ctrl b = b.ctrl
  let has_label b l = Label.(b.label = l)
  let hash b = Label.hash b.label

  let free_vars b =
    let (++) = Set.union and (--) = Set.diff in
    let init = Var.Set.(empty, empty) in
    let vars, kill = Array.fold b.data ~init ~f:(fun (vars, kill) d ->
        let kill' = match Insn.lhs_of_data d with
          | Some x -> Set.add kill x
          | None -> kill in
        Insn.free_vars_of_data d -- kill ++ vars, kill') in
    Insn.free_vars_of_ctrl b.ctrl -- kill ++ vars

  let uses_var b x = Set.mem (free_vars b) x

  let map_phi b ~f = {
    b with phi = Array.map b.phi ~f;
  }

  let map_phi' b ~f = {
    b with phi = Array.map b.phi ~f:(Insn.map_phi ~f);
  }

  let map_data b ~f = {
    b with data = Array.map b.data ~f;
  }

  let map_data' b ~f = {
    b with data = Array.map b.data ~f:(Insn.map_data ~f);
  }

  let map_ctrl b ~f = {
    b with ctrl = f b.ctrl;
  }

  let map_ctrl' b ~f = {
    b with ctrl = Insn.map_ctrl b.ctrl ~f;
  }

  let index_of xs l =
    Array.findi xs ~f:(fun _ x -> Insn.has_label x l) |> Option.map ~f:fst

  let prepend ?(before = None) xs x = match before with
    | None -> Array.push_front xs x
    | Some l -> index_of xs l |> function
      | Some i -> Array.insert xs x i
      | None -> xs

  let append ?(after = None) xs x = match after with
    | None -> Array.push_back xs x
    | Some l -> index_of xs l |> function
      | Some i -> Array.insert xs x (i + 1)
      | None -> xs

  let insert_phi b p = {
    b with phi = Array.push_front b.phi p;
  }

  let prepend_data ?(before = None) b d = {
    b with data = prepend b.data d ~before;
  }

  let append_data ?(after = None) b d = {
    b with data = append b.data d ~after;
  }

  let remove xs l = Array.remove_if xs ~f:(Fn.flip Insn.has_label l)
  let remove_phi b l = {b with phi = remove b.phi l}
  let remove_data b l = {b with data = remove b.data l}

  let has_lhs xs x f = Array.exists xs ~f:(Fn.compose (Fn.flip f x) Insn.insn)
  let has_lhs_phi b x = has_lhs b.phi x Insn.Phi.has_lhs
  let has_lhs_data b x = has_lhs b.data x Insn.Data.has_lhs
  let defines_var b x = has_lhs_phi b x || has_lhs_data b x

  let has xs l = Array.exists xs ~f:(Fn.flip Insn.has_label l)
  let has_phi b = has b.phi
  let has_data b = has b.data
  let has_ctrl b l = Insn.has_label b.ctrl l

  let find xs l = Array.find xs ~f:(Fn.flip Insn.has_label l)
  let find_phi b = find b.phi
  let find_data b = find b.data
  let find_ctrl b l = Option.some_if (Insn.has_label b.ctrl l) b.ctrl

  let next xs l = Array.next xs Insn.label l
  let next_phi b = next b.phi
  let next_data b = next b.data

  let prev xs l = Array.prev xs Insn.label l
  let prev_phi b = next b.phi
  let prev_data b = next b.data

  let pp ppf b =
    let sep ppf = Format.fprintf ppf "@;" in
    match b.phi, b.data with
    | [||], [||] ->
      Format.fprintf ppf "%a:@;%a"
        Label.pp b.label Insn.pp_ctrl b.ctrl
    | _, [||] ->
      Format.fprintf ppf "%a:@;%a@;%a"
        Label.pp b.label
        (Array.pp Insn.pp_phi sep) b.phi
        Insn.pp_ctrl b.ctrl
    | [||], _ ->
      Format.fprintf ppf "%a:@;%a@;%a"
        Label.pp b.label
        (Array.pp Insn.pp_data sep) b.data
        Insn.pp_ctrl b.ctrl
    | _ ->
      Format.fprintf ppf "%a:@;%a@;%a@;%a"
        Label.pp b.label
        (Array.pp Insn.pp_phi sep) b.phi
        (Array.pp Insn.pp_data sep) b.data
        Insn.pp_ctrl b.ctrl

  let pp_hum ppf b =
    let sep ppf = Format.fprintf ppf "@;" in
    match b.phi, b.data with
    | [||], [||] ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@]"
        Label.pp_hum b.label Insn.pp_ctrl_hum b.ctrl
    | _, [||] ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@;%a@]"
        Label.pp_hum b.label
        (Array.pp Insn.pp_phi_hum sep) b.phi
        Insn.pp_ctrl_hum b.ctrl
    | [||], _ ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@;%a@]"
        Label.pp_hum b.label
        (Array.pp Insn.pp_data_hum sep) b.data
        Insn.pp_ctrl_hum b.ctrl
    | _ ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@;%a@;%a@]"
        Label.pp_hum b.label
        (Array.pp Insn.pp_phi_hum sep) b.phi
        (Array.pp Insn.pp_data_hum sep) b.data
        Insn.pp_ctrl_hum b.ctrl

  include Regular.Make(struct
      include T
      let module_name = Some "Virtual.Blk"
      let version = "0.1"
      let pp = pp
      let hash = hash
    end)
end

type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]

module Fn = struct
  module T = struct
    type t = {
      name     : string;
      blks     : blk array;
      entry    : Label.t;
      args     : (Var.t * Type.arg) array;
      return   : Type.arg option;
      variadic : bool;
      linkage  : Linkage.t;
    } [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let create_exn
      ?(return = None)
      ?(variadic = false)
      ?(linkage = Linkage.default_export)
      ~name
      ~blks
      ~args
      () = match Array.of_list blks with
    | [||] -> invalid_argf "Cannot create empty function %s" name ()
    | blks -> {
        name;
        blks;
        entry = blks.(0).label;
        args = Array.of_list args;
        return;
        variadic;
        linkage;
      }

  let create
      ?(return = None)
      ?(variadic = false)
      ?(linkage = Linkage.default_export)
      ~name
      ~blks
      ~args
      () =
    Or_error.try_with @@
    create_exn ~name ~blks ~args ~return ~variadic ~linkage

  let name fn = fn.name
  let blks ?(rev = false) fn = Array.enum fn.blks ~rev
  let entry fn = fn.entry
  let args ?(rev = false) fn = Array.enum fn.args ~rev
  let return fn = fn.return
  let variadic fn = fn.variadic
  let linkage fn = fn.linkage
  let has_name fn name = String.(name = fn.name)
  let hash fn = String.hash fn.name

  let map_of_blks fn =
    Array.fold fn.blks ~init:Label.Map.empty ~f:(fun m b ->
        Map.set m ~key:(Blk.label b) ~data:b)

  let map_blks fn ~f =
    let entry = ref fn.entry in
    let is_entry b = Label.(Blk.label b = fn.entry) in
    let blks = Array.map fn.blks ~f:(fun b ->
        let b' = f b in
        if is_entry b then entry := Blk.label b';
        b') in
    {fn with blks; entry = !entry}

  let insert_blk fn b = {
    fn with blks = Array.push_back fn.blks b;
  }

  let remove_blk_exn fn l =
    if Label.(l = fn.entry)
    then invalid_argf "Cannot remove entry block of function %s" fn.name ()
    else {fn with blks = Array.remove_if fn.blks ~f:(Fn.flip Blk.has_label l)}

  let remove_blk fn l = Or_error.try_with @@ fun () -> remove_blk_exn fn l
  let has_blk fn l = Array.exists fn.blks ~f:(Fn.flip Blk.has_label l)
  let find_blk fn l = Array.find fn.blks ~f:(Fn.flip Blk.has_label l)
  let next_blk fn l = Array.next fn.blks Blk.label l
  let prev_blk fn l = Array.prev fn.blks Blk.label l

  let pp_arg ppf (v, t) = Format.fprintf ppf "%a %a" Type.pp_arg t Var.pp v

  let pp_args ppf fn =
    let sep ppf = Format.fprintf ppf ", " in
    Format.fprintf ppf "%a" (Array.pp pp_arg sep) fn.args;
    match fn.args, fn.variadic with
    | _, false -> ()
    | [||], true -> Format.fprintf ppf "..."
    | _, true -> Format.fprintf ppf ", ..."

  let pp ppf fn =
    let sep ppf = Format.fprintf ppf "@;" in
    Format.fprintf ppf "%a@;function " Linkage.pp fn.linkage;
    Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp_arg);
    Format.fprintf ppf "@@%s(%a):@;@[<v 0>%a@]"
      fn.name pp_args fn (Array.pp Blk.pp sep) fn.blks

  let pp_hum ppf fn =
    let sep ppf = Format.fprintf ppf "@;" in
    Format.fprintf ppf "%a@;function " Linkage.pp fn.linkage;
    Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp_arg);
    Format.fprintf ppf "@@%s(%a) {@;@[%a@]@;}"
      fn.name pp_args fn (Array.pp Blk.pp_hum sep) fn.blks

  (* XXX: name conflict *)
  include Fn

  include Regular.Make(struct
      include T
      let module_name = Some "Virtual.Fn"
      let version = "0.1"
      let pp = pp
      let hash = hash
    end)
end

type fn = Fn.t [@@deriving bin_io, compare, equal, sexp]

module Cfg = struct
  module G = Graphlib.Make(Label)(Edge)

  let connect_with_entry n =
    let e = Label.pseudoentry in
    if Label.(n = e) then Fn.id
    else G.Edge.(insert (create e n `always))

  let connect_with_exit n =
    let e = Label.pseudoexit in
    if Label.(n = e) then Fn.id
    else G.Edge.(insert (create n e `always))

  let if_unreachable ~from connect g n =
    if G.Node.degree ~dir:from n g = 0 then connect n else Fn.id

  let accum g b : Insn.Ctrl.t -> G.t = function
    | `jmp (`label l) -> G.Edge.(insert (create b l `always) g)
    | `jmp _ -> g
    | `jnz (x, `label t, `label f) ->
      let et = G.Edge.create b t @@ `true_ x in
      let ef = G.Edge.create b f @@ `false_ x in
      G.Edge.(insert ef (insert et g))
    | `jnz (x, `label l, _) -> G.Edge.(insert (create b l @@ `true_ x) g)
    | `jnz (x, _, `label l) -> G.Edge.(insert (create b l @@ `false_ x) g)
    | `jnz _ -> g
    | `ret _ -> g
    | `switch (_, x, d, t) ->
      let init = G.Edge.(insert (create b d @@ `default x) g) in
      Map.fold t ~init ~f:(fun ~key:v ~data:l g ->
          G.Edge.(insert (create b l @@ `switch (x, v)) g))

  let connect_unreachable g n =
    if_unreachable ~from:`Out connect_with_exit  g n @@
    if_unreachable ~from:`In  connect_with_entry g n @@
    g

  let create (fn : fn) =
    Array.fold fn.blks ~init:G.empty ~f:(fun g b ->
        accum (G.Node.insert b.label g) b.label b.ctrl.insn) |> fun g ->
    G.nodes g |> Seq.fold ~init:g ~f:connect_unreachable |> fun g ->
    Graphlib.depth_first_search (module G) g
      ~init:g ~start:Label.pseudoentry
      ~start_tree:connect_with_entry |> fun g ->
    Graphlib.depth_first_search (module G) g
      ~rev:true ~init:g ~start:Label.pseudoexit
      ~start_tree:connect_with_exit

  include G
end

type cfg = Cfg.t

module Live = struct
  type tran = {
    defs : Var.Set.t;
    uses : Var.Set.t;
  }

  let empty_tran = {
    defs = Var.Set.empty;
    uses = Var.Set.empty;
  }

  type t = {
    blks : tran Label.Map.t;
    outs : (Label.t, Var.Set.t) Solution.t;
  }

  let pp_vars ppf vars =
    Format.pp_print_list
      ~pp_sep:Format.pp_print_space
      Var.pp ppf (Set.to_list vars)

  let pp_transfer ppf {uses; defs} =
    Format.fprintf ppf "(%a) / (%a)" pp_vars uses pp_vars defs

  let blk_defs b =
    Blk.data b |> Seq.map ~f:Insn.insn |>
    Seq.fold ~init:Var.Set.empty ~f:(fun defs d ->
        Insn.Data.lhs d |> Option.value_map ~default:defs ~f:(Set.add defs))

  let update l trans ~f = Map.update trans l ~f:(function
      | None -> f empty_tran
      | Some had -> f had)

  let (++) = Set.union and (--) = Set.diff

  let block_transitions fn =
    Fn.blks fn |> Seq.fold ~init:Label.Map.empty ~f:(fun fs b ->
        Map.add_exn fs ~key:(Blk.label b) ~data:{
          defs = blk_defs b;
          uses = Blk.free_vars b;
        }) |> fun init ->
    Fn.blks fn |> Seq.fold ~init ~f:(fun init b ->
        Blk.phi b |> Seq.map ~f:Insn.insn |>
        Seq.fold ~init ~f:(fun fs p ->
            let lhs = Insn.Phi.lhs p in
            Insn.Phi.ins p |> Seq.fold ~init ~f:(fun fs (l, a) ->
                let vars = var_set_of_option @@ Insn.var_of_arg a in
                update l fs ~f:(fun {defs; uses} -> {
                      defs = Set.add defs lhs;
                      uses = uses ++ (vars -- defs);
                    }))))

  let lookup blks n = Map.find blks n |> Option.value ~default:empty_tran
  let apply {defs; uses} vars = vars -- defs ++ uses

  let transfer blks n vars =
    if Label.is_pseudo n then vars else apply (lookup blks n) vars

  let compute ?keep:(init = Var.Set.empty) fn =
    let g = Cfg.create fn in
    let init =
      Solution.create
        (Label.Map.singleton Label.pseudoexit Var.Set.empty)
        Var.Set.empty in
    let blks = block_transitions fn in {
      blks;
      outs = Graphlib.fixpoint (module Cfg) g ~init
          ~rev:true ~start:Label.pseudoexit
          ~merge:Set.union ~equal:Var.Set.equal
          ~f:(transfer blks);
    }

  let outs t l = Solution.get t.outs l
  let ins  t l = transfer t.blks l @@ outs t l
  let defs t l = (lookup t.blks l).defs
  let uses t l = (lookup t.blks l).uses

  let fold t ~init ~f =
    Map.fold t.blks ~init ~f:(fun ~key:l ~data:trans init ->
        f init l @@ apply trans @@ outs t l)

  let blks t x = fold t ~init:Label.Set.empty ~f:(fun blks l ins ->
      if Set.mem ins x then Set.add blks l else blks)

  let solution t = t.outs

  let pp ppf t =
    Format.pp_open_vbox ppf 0;
    fold t ~init:() ~f:(fun () l vars ->
        Format.fprintf ppf "@[<h>%a: @[<hov 2>(%a)@]@]@;"
          Label.pp l pp_vars vars);
    Format.pp_close_box ppf ()
end

type live = Live.t

module Data = struct
  type elt = [
    | `basic  of Type.basic * const list
    | `string of string
    | `zero   of int
  ] [@@deriving bin_io, compare, equal, sexp]

  let pp_elt ppf : elt -> unit = function
    | `basic (t, cs) ->
      let pp_sep ppf () = Format.fprintf ppf " " in
      Format.fprintf ppf "%a %a"
        Type.pp_basic t
        (Format.pp_print_list ~pp_sep pp_const) cs
    | `string s -> Format.fprintf ppf "%a \"%s\"" Type.pp_basic `i8 s
    | `zero n -> Format.fprintf ppf "z %d" n

  module T = struct
    type t = {
      name    : string;
      elts    : elt array;
      linkage : Linkage.t;
    } [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let create_exn ?(linkage = Linkage.default_export) ~name ~elts () =
    match Array.of_list elts with
    | [||] -> invalid_argf "Cannot create empty data %s" name ()
    | elts -> {name; elts; linkage}

  let create ?(linkage = Linkage.default_export) ~name ~elts () =
    Or_error.try_with @@ create_exn ~name ~elts ~linkage

  let name d = d.name
  let elts ?(rev = false) d = Array.enum d.elts ~rev
  let linkage d = d.linkage
  let has_name d name = String.(name = d.name)
  let hash d = String.hash d.name

  let prepend_elt d e = {
    d with elts = Array.push_front d.elts e;
  }

  let append_elt d e = {
    d with elts = Array.push_back d.elts e;
  }

  let map_elts d ~f = {
    d with elts = Array.map d.elts ~f;
  }

  let pp ppf d =
    let sep ppf = Format.fprintf ppf ",@;" in
    Format.fprintf ppf "%a@;data @@%s = {@;@[<v 2>%a@]@;}"
      Linkage.pp d.linkage d.name (Array.pp pp_elt sep) d.elts;

  include Regular.Make(struct
      include T
      let module_name = Some "Virtual.Data"
      let version = "0.1"
      let pp = pp
      let hash = hash
    end)
end

type data = Data.t [@@deriving bin_io, compare, equal, sexp]

module Module = struct
  module T = struct
    type t = {
      name : string;
      typs : Type.compound array;
      data : data array;
      funs : fn array;
    } [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let create ?(typs = []) ?(data = []) ?(funs = []) ~name () = {
    name;
    typs = Array.of_list typs;
    data = Array.of_list data;
    funs = Array.of_list funs;
  }

  let name m = m.name
  let typs ?(rev = false) m = Array.enum m.typs ~rev
  let data ?(rev = false) m = Array.enum m.data ~rev
  let funs ?(rev = false) m = Array.enum m.funs ~rev
  let has_name m name = String.(name = m.name)
  let hash m = String.hash m.name

  let insert_type m t = {
    m with typs = Array.push_back m.typs t;
  }

  let insert_data m d = {
    m with data = Array.push_back m.data d;
  }

  let insert_fn m fn = {
    m with funs = Array.push_back m.funs fn;
  }

  let remove_type m name = {
    m with typs = Array.remove_if m.typs ~f:(function
      | `compound (n, _, _) -> String.(n = name))
  }

  let remove_data m name = {
    m with data = Array.remove_if m.data ~f:(Fn.flip Data.has_name name);
  }

  let remove_fn m name = {
    m with funs = Array.remove_if m.funs ~f:(Fn.flip Fn.has_name name);
  }

  let map_typs m ~f = {
    m with typs = Array.map m.typs ~f;
  }

  let map_data m ~f = {
    m with data = Array.map m.data ~f;
  }

  let map_funs m ~f = {
    m with funs = Array.map m.funs ~f;
  }

  let pp ppf m =
    let sep ppf = Format.fprintf ppf "@;@;" in
    Format.fprintf ppf "%a@;%a@;%a"
      (Array.pp Type.pp_compound_decl sep) m.typs
      (Array.pp Data.pp sep) m.data
      (Array.pp Fn.pp sep) m.funs

  include Regular.Make(struct
      include T
      let module_name = Some "Virtual.Module"
      let version = "0.1"
      let pp = pp
      let hash = hash
    end)
end

type module_ = Module.t
