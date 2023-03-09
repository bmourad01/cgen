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
  | `float f -> Format.fprintf ppf "%sf" @@ Float32.to_string f
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

  let var_of_global : global -> Var.t option = function
    | `var x -> Some x
    | `addr _ | `sym _ -> None

  let pp_global ppf : global -> unit = function
    | `addr a -> Format.fprintf ppf "%a" Bitvec.pp a
    | `sym s  -> Format.fprintf ppf "@%s" s
    | `var v  -> Format.fprintf ppf "%a" Var.pp v

  type local = [
    | `label of Label.t * arg option
  ] [@@deriving bin_io, compare, equal, sexp]

  let pp_local ppf : local -> unit = function
    | `label (l, None) -> Format.fprintf ppf "%a" Label.pp l
    | `label (l, Some a) -> Format.fprintf ppf "%a(%a)" Label.pp l pp_arg a

  let pp_local_hum ppf : local -> unit = function
    | `label (l, None) -> Format.fprintf ppf "%a" Label.pp_hum l
    | `label (l, Some a) -> Format.fprintf ppf "%a(%a)" Label.pp_hum l pp_arg a

  type dst = [
    | global
    | local
  ] [@@deriving bin_io, compare, equal, sexp]

  let var_of_dst : dst -> Var.t option = function
    | #global as g -> var_of_global g
    | #local -> None

  let pp_dst ppf : dst -> unit = function
    | #global as g -> Format.fprintf ppf "%a" pp_global g
    | #local  as l -> Format.fprintf ppf "%a" pp_local l

  let pp_dst_hum ppf : dst -> unit = function
    | #global as g -> Format.fprintf ppf "%a" pp_global g
    | #local  as l -> Format.fprintf ppf "%a" pp_local_hum l

  module Data = struct
    type arith_binop = [
      | `add  of Type.basic
      | `div  of Type.basic
      | `mul  of Type.basic
      | `rem  of Type.basic
      | `sub  of Type.basic
      | `udiv of Type.imm
      | `urem of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_arith_binop ppf : arith_binop -> unit = function
      | `add  t -> Format.fprintf ppf "add.%a"  Type.pp_basic t
      | `div  t -> Format.fprintf ppf "div.%a"  Type.pp_basic t
      | `mul  t -> Format.fprintf ppf "mul.%a"  Type.pp_basic t
      | `rem  t -> Format.fprintf ppf "rem.%a"  Type.pp_basic t
      | `sub  t -> Format.fprintf ppf "sub.%a"  Type.pp_basic t
      | `udiv t -> Format.fprintf ppf "udiv.%a" Type.pp_imm t
      | `urem t -> Format.fprintf ppf "urem.%a" Type.pp_imm t

    type arith_unop = [
      | `neg of Type.basic
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_arith_unop ppf : arith_unop -> unit = function
      | `neg t -> Format.fprintf ppf "neg.%a" Type.pp_basic t

    type bitwise_binop = [
      | `and_ of Type.imm
      | `or_  of Type.imm
      | `sar  of Type.imm
      | `shl  of Type.imm
      | `shr  of Type.imm
      | `xor  of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_bitwise_binop ppf : bitwise_binop -> unit = function
      | `and_ t -> Format.fprintf ppf "and.%a" Type.pp_imm t
      | `or_  t -> Format.fprintf ppf  "or.%a" Type.pp_imm t
      | `sar  t -> Format.fprintf ppf "sar.%a" Type.pp_imm t
      | `shl  t -> Format.fprintf ppf "shl.%a" Type.pp_imm t
      | `shr  t -> Format.fprintf ppf "shr.%a" Type.pp_imm t
      | `xor  t -> Format.fprintf ppf "xor.%a" Type.pp_imm t

    type bitwise_unop = [
      | `not_ of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_bitwise_unop ppf : bitwise_unop -> unit = function
      | `not_ t -> Format.fprintf ppf "not.%a" Type.pp_imm t

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
      | `load (t, m, a) ->
        Format.fprintf ppf "ld.%a %a[%a]" Type.pp_basic t Var.pp m pp_arg a
      | `store (t, m, a, x) ->
        Format.fprintf ppf "st.%a %a[%a], %a"
          Type.pp_basic t Var.pp m pp_arg a pp_arg x

    type cmp = [
      | `eq  of Type.basic
      | `ge  of Type.basic
      | `gt  of Type.basic
      | `le  of Type.basic
      | `lt  of Type.basic
      | `ne  of Type.basic
      | `o   of Type.fp
      | `sge of Type.imm
      | `sgt of Type.imm
      | `sle of Type.imm
      | `slt of Type.imm
      | `uo  of Type.fp
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_cmp ppf : cmp -> unit = function
      | `eq  t -> Format.fprintf ppf "eq.%a"  Type.pp_basic t
      | `ge  t -> Format.fprintf ppf "ge.%a"  Type.pp_basic t
      | `gt  t -> Format.fprintf ppf "gt.%a"  Type.pp_basic t
      | `le  t -> Format.fprintf ppf "le.%a"  Type.pp_basic t
      | `lt  t -> Format.fprintf ppf "lt.%a"  Type.pp_basic t
      | `ne  t -> Format.fprintf ppf "ne.%a"  Type.pp_basic t
      | `o   t -> Format.fprintf ppf "o.%a"   Type.pp_fp    t
      | `sge t -> Format.fprintf ppf "sge.%a" Type.pp_imm   t
      | `sgt t -> Format.fprintf ppf "sgt.%a" Type.pp_imm   t
      | `sle t -> Format.fprintf ppf "sle.%a" Type.pp_imm   t
      | `slt t -> Format.fprintf ppf "slt.%a" Type.pp_imm   t
      | `uo  t -> Format.fprintf ppf "uo.%a"  Type.pp_fp    t

    type cast = [
      | `bits   of Type.basic
      | `ftosi  of Type.fp * Type.imm
      | `ftoui  of Type.fp * Type.imm
      | `ftrunc of Type.fp
      | `itrunc of Type.imm
      | `sext   of Type.imm
      | `sitof  of Type.imm * Type.fp
      | `uitof  of Type.imm * Type.fp
      | `zext   of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_cast ppf : cast -> unit = function
      | `bits t ->
        Format.fprintf ppf "bits.%a" Type.pp_basic t
      | `ftosi (tf, ti) ->
        Format.fprintf ppf "ftosi.%a.%a" Type.pp_fp tf Type.pp_imm ti
      | `ftoui (tf, ti) ->
        Format.fprintf ppf "ftoui.%a.%a" Type.pp_fp tf Type.pp_imm ti
      | `ftrunc t ->
        Format.fprintf ppf "ftrunc.%a" Type.pp_fp t
      | `itrunc t ->
        Format.fprintf ppf "itrunc.%a" Type.pp_imm t
      | `sext t ->
        Format.fprintf ppf "sext.%a" Type.pp_imm t
      | `sitof (ti, tf) ->
        Format.fprintf ppf "sitof.%a.%a" Type.pp_imm ti Type.pp_fp tf
      | `uitof (ti, tf) ->
        Format.fprintf ppf "uitof.%a.%a" Type.pp_imm ti Type.pp_fp tf
      | `zext t ->
        Format.fprintf ppf "zext.%a" Type.pp_imm t

    type copy = [
      | `copy of Type.basic
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_copy ppf : copy -> unit = function
      | `copy t -> Format.fprintf ppf "copy.%a" Type.pp_basic t

    type binop = [
      | arith_binop
      | bitwise_binop
      | cmp
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_binop ppf : binop -> unit = function
      | #arith_binop as a -> Format.fprintf ppf "%a" pp_arith_binop a
      | #bitwise_binop as b -> Format.fprintf ppf "%a" pp_bitwise_binop b
      | #cmp as c -> Format.fprintf ppf "%a" pp_cmp c

    type unop = [
      | arith_unop
      | bitwise_unop
      | cast
      | copy
    ] [@@deriving bin_io, compare, equal, sexp]

    let pp_unop ppf : unop -> unit = function
      | #arith_unop as a -> Format.fprintf ppf "%a" pp_arith_unop a
      | #bitwise_unop as b -> Format.fprintf ppf "%a" pp_bitwise_unop b
      | #cast as c -> Format.fprintf ppf "%a" pp_cast c
      | #copy as c -> Format.fprintf ppf "%a" pp_copy c

    type op = [
      | `binop  of Var.t * binop * arg * arg
      | `unop   of Var.t * unop  * arg
      | `mem    of Var.t * mem
      | `select of Var.t * Type.basic * Var.t * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_op : op -> Var.Set.t = function
      | `binop (_, _, l, r) ->
        List.filter_map [l; r] ~f:var_of_arg |> Var.Set.of_list
      | `unop (_, _, a) -> var_set_of_option @@ var_of_arg a
      | `mem (_, m) -> free_vars_of_mem m
      | `select (_, _, x, t, f) ->
        List.filter_map [t; f] ~f:var_of_arg |> List.cons x |> Var.Set.of_list

    let pp_op ppf : op -> unit = function
      | `binop (x, b, l, r) ->
        Format.fprintf ppf "%a = %a %a, %a"  Var.pp x pp_binop b pp_arg l pp_arg r
      | `unop (x, u, a) ->
        Format.fprintf ppf "%a = %a %a" Var.pp x pp_unop u pp_arg a
      | `mem (x, m) ->
        Format.fprintf ppf "%a = %a" Var.pp x pp_mem m
      | `select (x, t, c, l, r) ->
        Format.fprintf ppf "%a = select.%a %a, %a, %a"
          Var.pp x Type.pp_basic t Var.pp c pp_arg l pp_arg r

    type call = [
      | `acall of Var.t * Type.basic * global * arg list * arg list
      | `call  of global * arg list * arg list
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_call : call -> Var.Set.t = function
      | `acall (_, _, f, args, vargs)
      | `call (f, args, vargs) ->
        let f = var_of_global f |> Option.to_list |> Var.Set.of_list in
        let args = List.filter_map args ~f:var_of_arg |> Var.Set.of_list in
        let vargs = List.filter_map vargs ~f:var_of_arg |> Var.Set.of_list in
        Var.Set.union_list [f; args; vargs]

    let is_variadic : call -> bool = function
      | `acall (_, _, _, _, []) | `call (_, _, []) -> false
      | `acall _  | `call _  -> true

    let pp_call_args ppf args =
      let pp_sep ppf () = Format.fprintf ppf ", " in
      Format.pp_print_list ~pp_sep pp_arg ppf args

    let pp_call_vargs args ppf = function
      | [] -> ()
      | vargs ->
        if not (List.is_empty args) then Format.fprintf ppf ", ";
        Format.fprintf ppf "..., %a" pp_call_args vargs

    let pp_call_res ppf = function
      | None -> Format.fprintf ppf "call "
      | Some (x, t) ->
        Format.fprintf ppf "%a = call.%a " Var.pp x Type.pp_basic t

    let pp_call ppf c =
      let res, dst, args, vargs = match c with
        | `acall (v, t, d, a, va) -> Some (v, t), d, a, va
        | `call (d, a, va) -> None, d, a, va in
      Format.fprintf ppf "%a%a(%a%a)"
        pp_call_res res
        pp_global dst
        pp_call_args args
        (pp_call_vargs args) vargs

    type variadic = [
      | `vastart of Var.t
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars_of_variadic : variadic -> Var.Set.t = function
      | `vastart x -> Var.Set.singleton x

    let pp_variadic ppf : variadic -> unit = function
      | `vastart x -> Format.fprintf ppf "vastart %a" Var.pp x

    type t = [
      | call
      | op
      | variadic
    ] [@@deriving bin_io, compare, equal, sexp]

    let lhs : t -> Var.t option = function
      | `binop   (x, _, _, _)
      | `unop    (x, _, _)
      | `mem     (x, _)
      | `select  (x, _, _, _, _)
      | `acall   (x, _, _, _, _) -> Some x
      | `call    _ -> None
      | `vastart _ -> None

    let has_lhs d v = match lhs d with
      | Some x -> Var.(x = v)
      | None -> false

    let free_vars : t -> Var.Set.t = function
      | #call as c     -> free_vars_of_call c
      | #op   as o     -> free_vars_of_op o
      | #variadic as v -> free_vars_of_variadic v

    let pp ppf : t -> unit = function
      | #call     as c -> pp_call     ppf c
      | #op       as o -> pp_op       ppf o
      | #variadic as v -> pp_variadic ppf v
  end

  module Ctrl = struct
    module Table = struct
      type t = local Map.M(Bitvec).t [@@deriving bin_io, compare, equal, sexp]

      let create_exn l = try Map.of_alist_exn (module Bitvec) l with
        | exn -> invalid_argf "%s" (Exn.to_string exn) ()

      let create l = Or_error.try_with @@ fun () -> create_exn l
      let enum t = Map.to_sequence t
      let find t v = Map.find t v

      let map_exn t ~f = try
          Map.to_sequence t |>
          Seq.map ~f:(fun (v, l) -> f v l) |>
          Map.of_sequence_exn (module Bitvec)
        with exn -> invalid_argf "%s" (Exn.to_string exn) ()

      let map t ~f = Or_error.try_with @@ fun () -> map_exn t ~f

      let pp_elt ppl ppf (v, l) =
        Format.fprintf ppf "%a -> %a" Bitvec.pp v ppl l

      let pp ppl ppf t =
        let pp_sep ppf () = Format.fprintf ppf ",@;" in
        Format.pp_print_list ~pp_sep (pp_elt ppl) ppf (Map.to_alist t)
    end

    type table = Table.t [@@deriving bin_io, compare, equal, sexp]

    type t = [
      | `hlt
      | `jmp    of dst
      | `jnz    of Var.t * dst * dst
      | `ret    of arg option
      | `switch of Type.imm * Var.t * local * table
    ] [@@deriving bin_io, compare, equal, sexp]

    let free_vars : t -> Var.Set.t = function
      | `hlt -> Var.Set.empty
      | `jmp _ -> Var.Set.empty
      | `jnz (x, _, _) -> Var.Set.singleton x
      | `ret None -> Var.Set.empty
      | `ret (Some a) -> var_set_of_option @@ var_of_arg a
      | `switch (_, x, _, _) -> Var.Set.singleton x

    let pp_self ppd ppl ppf : t -> unit = function
      | `hlt -> Format.fprintf ppf "hlt"
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
          Type.pp_imm t Var.pp x ppl ld (Table.pp ppl) tbl

    let pp = pp_self pp_dst pp_local
    let pp_hum = pp_self pp_dst_hum pp_local_hum
  end

  type 'a t = {
    insn  : 'a;
    label : Label.t;
  } [@@deriving bin_io, compare, equal, sexp]

  type data = Data.t t [@@deriving bin_io, compare, equal, sexp]
  type ctrl = Ctrl.t t [@@deriving bin_io, compare, equal, sexp]

  let data insn ~label : data = {insn; label}
  let ctrl insn ~label : ctrl = {insn; label}

  let insn i = i.insn
  let label i = i.label
  let has_label i l = Label.(i.label = l)
  let hash i = Label.hash i.label

  let lhs_of_data i = Data.lhs i.insn

  let map_data (i : data) ~f = {i with insn = f i.insn}
  let map_ctrl (i : ctrl) ~f = {i with insn = f i.insn}

  let free_vars_of_data i = Data.free_vars i.insn
  let free_vars_of_ctrl i = Ctrl.free_vars i.insn

  let pp ppi ppf i = Format.fprintf ppf "%a: %a" Label.pp i.label ppi i.insn

  let pp_data = pp Data.pp
  let pp_ctrl = pp Ctrl.pp

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
  type arg_typ = [
    | Type.basic
    | Type.special
  ] [@@deriving bin_io, compare, equal, sexp]

  let pp_arg_typ ppf t =
    Format.fprintf ppf "%a" Type.pp (t :> Type.t)

  module T = struct
    type t = {
      label : Label.t;
      args  : arg_typ Var.Map.t;
      data  : Insn.data array;
      ctrl  : Insn.ctrl;
    } [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let create_exn ?(args = []) ?(data = []) ~label ~ctrl () = try {
    label;
    args = Var.Map.of_alist_exn args;
    data = Array.of_list data;
    ctrl
  } with exn -> invalid_argf "%s" (Exn.to_string exn) ()

  let create ?(args = []) ?(data = []) ~label ~ctrl () =
    Or_error.try_with @@ create_exn ~args ~data ~label ~ctrl

  let label b = b.label

  let args ?(rev = false) b =
    let order = if rev then `Increasing_key else `Decreasing_key in
    Map.to_sequence b.args ~order

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

  let map_args_exn b ~f = try
      Map.to_sequence b.args |>
      Seq.map ~f:(fun (x, t) -> f x t) |>
      Var.Map.of_sequence_exn |> fun args ->
      {b with args}
    with exn -> invalid_argf "%s" (Exn.to_string exn) ()

  let map_args b ~f =
    Or_error.try_with @@ fun () -> map_args_exn b ~f

  let map_data b ~f = {
    b with data = Array.map b.data ~f:(fun i ->
      Insn.map_data i ~f:(f i.label));
  }

  let map_ctrl b ~f = {
    b with ctrl = Insn.map_ctrl b.ctrl ~f:(f b.ctrl.label);
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

  let add_arg b x t = {
    b with args = Map.set b.args ~key:x ~data:t;
  }

  let prepend_data ?(before = None) b d = {
    b with data = prepend b.data d ~before;
  }

  let append_data ?(after = None) b d = {
    b with data = append b.data d ~after;
  }

  let remove xs l = Array.remove_if xs ~f:(Fn.flip Insn.has_label l)

  let remove_arg b x = {b with args = Map.remove b.args x}
  let remove_data b l = {b with data = remove b.data l}

  let has_arg b x = Map.mem b.args x
  let typeof_arg b x = Map.find b.args x

  let has_lhs b x = Array.exists b.data ~f:(fun i ->
      Insn.Data.has_lhs (Insn.insn i) x)

  let defines_var b x = has_arg b x || has_lhs b x

  let has xs l = Array.exists xs ~f:(Fn.flip Insn.has_label l)
  let has_data b = has b.data
  let has_ctrl b l = Insn.has_label b.ctrl l

  let find xs l = Array.find xs ~f:(Fn.flip Insn.has_label l)
  let find_data b = find b.data
  let find_ctrl b l = Option.some_if (Insn.has_label b.ctrl l) b.ctrl

  let next xs l = Array.next xs Insn.label l
  let next_data b = next b.data

  let prev xs l = Array.prev xs Insn.label l
  let prev_data b = next b.data

  let pp_arg ppf (x, t) =
    Format.fprintf ppf "%a %a" pp_arg_typ t Var.pp x

  let pp_args ppf args =
    let pp_sep ppf () = Format.fprintf ppf ", " in
    Format.pp_print_list ~pp_sep pp_arg ppf @@ Map.to_alist args

  let pp_args ppf args =
    if not @@ Map.is_empty args then
      Format.fprintf ppf "(%a)" pp_args args

  let pp ppf b =
    let sep ppf = Format.fprintf ppf "@;" in
    match b.data with
    | [||] ->
      Format.fprintf ppf "%a%a:@;%a"
        Label.pp b.label
        pp_args b.args
        Insn.pp_ctrl b.ctrl
    | _ ->
      Format.fprintf ppf "%a%a:@;%a@;%a"
        Label.pp b.label
        pp_args b.args
        (Array.pp Insn.pp_data sep) b.data
        Insn.pp_ctrl b.ctrl

  let pp_hum ppf b =
    let sep ppf = Format.fprintf ppf "@;" in
    match b.data with
    | [||] ->
      Format.fprintf ppf "%a%a:@;  %a"
        Label.pp_hum b.label
        pp_args b.args
        Insn.pp_ctrl_hum b.ctrl
    | _ ->
      Format.fprintf ppf "%a%a:@;@[<v 2>  %a@;%a@]"
        Label.pp_hum b.label
        pp_args b.args
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

module Func = struct
  module T = struct
    type t = {
      name     : string;
      blks     : blk array;
      entry    : Label.t;
      args     : (Var.t * Type.arg) array;
      return   : Type.arg option;
      variadic : bool;
      noreturn : bool;
      linkage  : Linkage.t;
    } [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let create_exn
      ?(return = None)
      ?(variadic = false)
      ?(noreturn = false)
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
        noreturn;
        linkage;
      }

  let create
      ?(return = None)
      ?(variadic = false)
      ?(noreturn = false)
      ?(linkage = Linkage.default_export)
      ~name
      ~blks
      ~args
      () =
    Or_error.try_with @@
    create_exn ~name ~blks ~args ~return ~variadic ~noreturn ~linkage

  let name fn = fn.name
  let blks ?(rev = false) fn = Array.enum fn.blks ~rev
  let entry fn = fn.entry
  let args ?(rev = false) fn = Array.enum fn.args ~rev
  let return fn = fn.return
  let variadic fn = fn.variadic
  let noreturn fn = fn.noreturn
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

  let update_blk fn b =
    let l = Blk.label b in {
      fn with blks = Array.update_if fn.blks b ~f:(Fn.flip Blk.has_label l);
    }

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
    if Linkage.export fn.linkage
    || Linkage.section fn.linkage |> Option.is_some then
      Format.fprintf ppf "%a " Linkage.pp fn.linkage;
    if fn.noreturn then Format.fprintf ppf "noreturn ";
    Format.fprintf ppf "function ";
    Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp_arg);
    Format.fprintf ppf "@@%s(%a):@;@[<v 0>%a@]"
      fn.name pp_args fn (Array.pp Blk.pp sep) fn.blks

  let pp_hum ppf fn =
    let sep ppf = Format.fprintf ppf "@;" in
    if Linkage.export fn.linkage
    || Linkage.section fn.linkage |> Option.is_some then
      Format.fprintf ppf "%a " Linkage.pp fn.linkage;
    if fn.noreturn then Format.fprintf ppf "noreturn ";
    Format.fprintf ppf "function ";
    Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp_arg);
    Format.fprintf ppf "@@%s(%a) {@;@[<v 0>%a@]@;}"
      fn.name pp_args fn (Array.pp Blk.pp_hum sep) fn.blks

  include Regular.Make(struct
      include T
      let module_name = Some "Virtual.Fn"
      let version = "0.1"
      let pp = pp
      let hash = hash
    end)
end

type func = Func.t [@@deriving bin_io, compare, equal, sexp]

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
    | `hlt -> g
    | `jmp (`label (l, _)) -> G.Edge.(insert (create b l `always) g)
    | `jmp _ -> g
    | `jnz (x, `label (t, _), `label (f, _)) ->
      let et = G.Edge.create b t @@  `true_ x in
      let ef = G.Edge.create b f @@ `false_ x in
      G.Edge.(insert ef (insert et g))
    | `jnz (x, `label (l, _), _) -> G.Edge.(insert (create b l @@  `true_ x) g)
    | `jnz (x, _, `label (l, _)) -> G.Edge.(insert (create b l @@ `false_ x) g)
    | `jnz _ -> g
    | `ret _ -> g
    | `switch (_, x, `label (d, _), t) ->
      let init = G.Edge.(insert (create b d @@ `default x) g) in
      Map.fold t ~init ~f:(fun ~key:v ~data:(`label (l, _)) g ->
          G.Edge.(insert (create b l @@ `switch (x, v)) g))

  let connect_unreachable g n =
    if_unreachable ~from:`Out connect_with_exit  g n @@
    if_unreachable ~from:`In  connect_with_entry g n @@
    g

  let create (fn : func) =
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
        match Insn.Data.lhs d with
        | Some x -> Set.add defs x
        | None -> defs) |> fun init ->
    Blk.args b |> Seq.fold ~init ~f:(fun defs (x, _) ->
        Set.add defs x)

  let update l trans ~f = Map.update trans l ~f:(function
      | None -> f empty_tran
      | Some had -> f had)

  let (++) = Set.union and (--) = Set.diff

  let block_transitions fn =
    Func.blks fn |> Seq.fold ~init:Label.Map.empty ~f:(fun fs b ->
        Map.add_exn fs ~key:(Blk.label b) ~data:{
          defs = blk_defs b;
          uses = Blk.free_vars b;
        })

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
      align   : int option;
    } [@@deriving bin_io, compare, equal, sexp]
  end

  include T

  let create_exn
      ?(align = None)
      ?(linkage = Linkage.default_export)
      ~name
      ~elts
      () =
    match Array.of_list elts with
    | [||] -> invalid_argf "Cannot create empty data %s" name ()
    | elts ->
      Array.iter elts ~f:(function
          | `basic (t, []) -> invalid_arg @@ Format.asprintf
              "In data @%s: `basic field of type %a is uninitialized"
              name Type.pp_basic t
          | _ -> ());
      Option.iter align ~f:(function
          | n when n < 1 ->
            invalid_argf "In data @%s: invalid alignment %d" name n ()
          | _ -> ());
      {name; elts; linkage; align}

  let create
      ?(align = None)
      ?(linkage = Linkage.default_export)
      ~name
      ~elts
      () =
    Or_error.try_with @@ create_exn ~name ~elts ~linkage ~align

  let name d = d.name
  let elts ?(rev = false) d = Array.enum d.elts ~rev
  let linkage d = d.linkage
  let align d = d.align
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
    if Linkage.export d.linkage
    || Linkage.section d.linkage |> Option.is_some then
      Format.fprintf ppf "%a " Linkage.pp d.linkage;
    Format.fprintf ppf "data @@%s = " d.name;
    Option.iter d.align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
      (Array.pp pp_elt sep) d.elts

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
      funs : func array;
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
    m with funs = Array.remove_if m.funs ~f:(Fn.flip Func.has_name name);
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

  let pp_base pp_fn ppf m =
    let sep ppf = Format.fprintf ppf "@;@;" in
    match m.typs, m.data, m.funs with
    | [||], [||], [||] ->
      Format.fprintf ppf "@[<v 0>module %s@]" m.name
    | [||], [||], funs ->
      Format.fprintf ppf "@[<v 0>module %s@;@;\
                          @[<v 0>%a@]@]" m.name
        (Array.pp pp_fn sep) funs
    | [||], data, [||] ->
      Format.fprintf ppf "@[<v 0>module %s@;@;\
                          @[<v 0>%a@]@]" m.name
        (Array.pp Data.pp sep) data
    | typs, [||], [||] ->
      Format.fprintf ppf "@[<v 0>module %s@;@;\
                          @[<v 0>%a@]@]" m.name
        (Array.pp Type.pp_compound_decl sep) typs
    | [||], data, funs ->
      Format.fprintf ppf "@[<v 0>module %s@;@;\
                          @[<v 0>%a@]@;@;\
                          @[<v 0>%a@]@]" m.name
        (Array.pp Data.pp sep) data
        (Array.pp pp_fn sep) funs
    | typs, [||], funs ->
      Format.fprintf ppf "@[<v 0>module %s@;@;\
                          @[<v 0>%a@]@;@;\
                          @[<v 0>%a@]@]" m.name
        (Array.pp Type.pp_compound_decl sep) typs
        (Array.pp pp_fn sep) funs
    | typs, data, [||] ->
      Format.fprintf ppf "@[<v 0>module %s@;@;\
                          @[<v 0>%a@]@;@;\
                          @[<v 0>%a@]@]" m.name
        (Array.pp Type.pp_compound_decl sep) typs
        (Array.pp Data.pp sep) data
    | typs, data, funs ->
      Format.fprintf ppf "@[<v 0>module %s@;@;\
                          @[<v 0>%a@]@;@;\
                          @[<v 0>%a@]@;@;\
                          @[<v 0>%a@]@]" m.name
        (Array.pp Type.pp_compound_decl sep) typs
        (Array.pp Data.pp sep) data
        (Array.pp pp_fn sep) funs

  let pp = pp_base Func.pp
  let pp_hum = pp_base Func.pp_hum

  include Regular.Make(struct
      include T
      let module_name = Some "Virtual.Module"
      let version = "0.1"
      let pp = pp
      let hash = hash
    end)
end

type module_ = Module.t
