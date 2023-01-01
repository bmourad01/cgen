open Core
open Monads.Std
open Regular.Std

module Bitvec = struct
  include Bitvec
  include Bitvec_binprot
  include Bitvec_order
  include Bitvec_sexp
end

module List = struct
  include List

  let rec pp ppx sep ppf = function
    | x :: (_ :: _ as rest) ->
      Format.fprintf ppf "%a" ppx x;
      sep ppf;
      Format.fprintf ppf "%a" (pp ppx sep) rest
    | [x] -> Format.fprintf ppf "%a" ppx x
    | [] -> ()
end

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

  let concat_map xs ~f =
    of_list @@ fold_right xs ~init:[] ~f:(fun x acc -> f x @ acc)

  let findi_label xs f l = findi xs ~f:(fun _ x -> Label.equal l @@ f x)

  let lift : type a b. (a -> b) -> (a -> b option) = fun f ->
    Fn.compose Option.return f

  let next xs f l =
    let open Monad.Option.Syntax in
    findi_label xs f l >>= lift fst >>= lift succ >>= fun j ->
    if j >= length xs then None else Some xs.(j)

  let prev xs f l =
    let open Monad.Option.Syntax in
    findi_label xs f l >>= lift fst >>= lift pred >>= fun j ->
    if j < 0 then None else Some xs.(j)
end

type const = [
  | `int   of Bitvec.t
  | `float of Decimal.t
  | `sym   of string * int
]

let pp_const ppf : const -> unit = function
  | `int n -> Format.fprintf ppf "%a" Bitvec.pp n
  | `float f -> Format.fprintf ppf "%a" Decimal.pp f
  | `sym (s, 0) -> Format.fprintf ppf "@@%s" s
  | `sym (s, n) when n > 0 -> Format.fprintf ppf "@@%s+0x%x" s n
  | `sym (s, n) -> Format.fprintf ppf "@@%s-0x%x" s (lnot n + 1)

module Insn = struct
  type arg = [
    | const
    | `var of Var.t
  ]

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
  ]

  let pp_global ppf : global -> unit = function
    | `addr a -> Format.fprintf ppf "#%a" Bitvec.pp a
    | `sym s -> Format.fprintf ppf "@%s" s
    | `var v -> Format.fprintf ppf "%a" Var.pp v

  type local = [
    | `label of Label.t
  ]

  let pp_local ppf : local -> unit = function
    | `label l -> Format.fprintf ppf "%a" Label.pp l

  let pp_local_hum ppf : local -> unit = function
    | `label l -> Format.fprintf ppf "%a" Label.pp_hum l

  type dst = [
    | global
    | local
  ]

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
    }

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

    let free_vars p =
      Map.to_sequence p.ins |>
      Seq.map ~f:snd |>
      Seq.filter_map ~f:var_of_arg |>
      Var.Set.of_sequence

    let pp_in ppl ppf (l, x) = Format.fprintf ppf "%a -> %a" ppl l pp_arg x

    let pp_self ppl ppf p =
      let sep ppf = Format.fprintf ppf ",@;" in
      Format.fprintf ppf "%a = phi.%a [@[<v 0>%a@]]"
        Var.pp p.lhs Type.pp (p.typ :> Type.t)
        (List.pp (pp_in ppl) sep) (Map.to_alist p.ins)

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
    ]

    let free_vars_of_arith : arith -> Var.Set.t = function
      | `add  (_, l, r)
      | `div  (_, l, r)
      | `mul  (_, l, r)
      | `rem  (_, l, r)
      | `sub  (_, l, r)
      | `udiv (_, l, r)
      | `urem (_, l, r) ->
        List.filter_map [l; r] ~f:var_of_arg |> Var.Set.of_list
      | `neg  (_, a) ->
        var_of_arg a |> Option.to_list |> Var.Set.of_list

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
    ]

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
    ]

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
    ]

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
    ]

    let free_vars_of_cast : cast -> Var.Set.t = function
      | `bits   (_, a)
      | `ftosi  (_, _, a)
      | `ftoui  (_, _, a)
      | `ftrunc (_, a)
      | `itrunc (_, a)
      | `sext   (_, a)
      | `sitof  (_, _, a)
      | `uitof  (_, _, a)
      | `zext   (_, a) ->
        var_of_arg a |> Option.to_list |> Var.Set.of_list

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
    ]

    let free_vars_of_copy : copy -> Var.Set.t = function
      | `copy (_, a) ->
        var_of_arg a |> Option.to_list |> Var.Set.of_list
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
    ]

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
    ]

    let free_vars_of_void_call : void_call -> Var.Set.t = function
      | `call  (_, args)
      | `callv (_, args) ->
        List.filter_map args ~f:var_of_arg |> Var.Set.of_list

    type assign_call = [
      | `acall  of Var.t * Type.basic * global * arg list
      | `acallv of Var.t * Type.basic * global * arg list
    ]

    let free_vars_of_assign_call : assign_call -> Var.Set.t = function
      | `acall  (x, _, _, args)
      | `acallv (x, _, _, args) ->
        List.filter_map args ~f:var_of_arg |> List.cons x |> Var.Set.of_list

    type call = [
      | void_call
      | assign_call
    ]

    let free_vars_of_call : call -> Var.Set.t = function
      | #void_call   as v -> free_vars_of_void_call v
      | #assign_call as a -> free_vars_of_assign_call a

    let is_variadic : call -> bool = function
      | `acallv _ | `callv _ -> true
      | `acall _  | `call _  -> false

    let pp_call_args variadic ppf args =
      let sep ppf = Format.fprintf ppf ", " in
      Format.fprintf ppf "%a" (List.pp pp_arg sep) args;
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
    ]

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
      type t = Label.t Map.M(Bitvec).t

      let create_exn l = try Map.of_alist_exn (module Bitvec) l with
        | exn -> invalid_argf "%s" (Exn.to_string exn) ()

      let create l = Or_error.try_with @@ fun () -> create_exn l
      let enum t = Map.to_sequence t
      let find t v = Map.find t v

      let pp_elt ppl ppf (v, l) =
        Format.fprintf ppf "%a -> %a" Bitvec.pp v ppl l

      let pp ppl ppf t =
        let sep ppf = Format.fprintf ppf ",@;" in
        Format.fprintf ppf "%a" (List.pp (pp_elt ppl) sep) (Map.to_alist t)
    end

    type table = Table.t

    type t = [
      | `jmp    of dst
      | `jnz    of Var.t * dst * dst
      | `ret    of arg option
      | `switch of Type.imm * Var.t * Label.t * table
    ]

    let free_vars : t -> Var.Set.t = function
      | `jmp _ -> Var.Set.empty
      | `jnz (x, _, _) -> Var.Set.singleton x
      | `ret None -> Var.Set.empty
      | `ret (Some a) -> var_of_arg a |> Option.to_list |> Var.Set.of_list
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
  }

  type phi = Phi.t t
  type data = Data.t t
  type ctrl = Ctrl.t t

  let phi insn ~label : phi = {insn; label}
  let data insn ~label : data = {insn; label}
  let ctrl insn ~label : ctrl = {insn; label}

  let insn i = i.insn
  let label i = i.label
  let has_label i l = Label.(i.label = l)

  let lhs_of_phi i = Phi.lhs i.insn
  let lhs_of_data i = Data.lhs i.insn

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

module Blk = struct
  type t = {
    label : Label.t;
    phi   : Insn.phi array;
    data  : Insn.data array;
    ctrl  : Insn.ctrl;
  }

  let create ?(phi = []) ?(data = []) ~label ~ctrl () = {
    label;
    phi = Array.of_list phi;
    data = Array.of_list data;
    ctrl
  }

  let label b = b.label
  let phi b = Array.to_sequence b.phi
  let data b = Array.to_sequence b.data
  let ctrl b = b.ctrl
  let has_label b l = Label.(b.label = l)

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

  let map_data b ~f = {
    b with data = Array.map b.data ~f;
  }

  let concat_map_phi b ~f = {
    b with phi = Array.concat_map b.phi ~f;
  }

  let concat_map_data b ~f = {
    b with data = Array.concat_map b.data ~f;
  }

  let map_ctrl b ~f = {
    b with ctrl = f b.ctrl;
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

end

type blk = Blk.t

module Fn = struct
  type t = {
    name     : string;
    blks     : blk array;
    entry    : Label.t;
    args     : (Var.t * Type.arg) array;
    return   : Type.arg option;
    variadic : bool;
    linkage  : Linkage.t;
  }

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
  let blks fn = Array.to_sequence fn.blks
  let entry fn = fn.entry
  let args fn = Array.to_sequence fn.args
  let return fn = fn.return
  let variadic fn = fn.variadic
  let linkage fn = fn.linkage
  let has_name fn name = String.(name = fn.name)

  let map_blks fn ~f = {
    fn with blks = Array.map fn.blks ~f;
  }

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
end

type fn = Fn.t

module Data = struct
  type elt = [
    | `basic  of Type.basic * const list
    | `string of string
    | `zero   of int
  ]

  let pp_elt ppf : elt -> unit = function
    | `basic (t, cs) ->
      let sep ppf = Format.fprintf ppf " " in
      Format.fprintf ppf "%a %a" Type.pp_basic t (List.pp pp_const sep) cs
    | `string s -> Format.fprintf ppf "%a \"%s\"" Type.pp_basic `i8 s
    | `zero n -> Format.fprintf ppf "z %d" n

  type t = {
    name    : string;
    elts    : elt array;
    linkage : Linkage.t;
  }

  let create_exn ?(linkage = Linkage.default_export) ~name ~elts () =
    match Array.of_list elts with
    | [||] -> invalid_argf "Cannot create empty data %s" name ()
    | elts -> {name; elts; linkage}

  let create ?(linkage = Linkage.default_export) ~name ~elts () =
    Or_error.try_with @@ create_exn ~name ~elts ~linkage

  let name d = d.name
  let elts d = Array.to_sequence d.elts
  let linkage d = d.linkage
  let has_name d name = String.(name = d.name)

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
end

type data = Data.t

type t = {
  name : string;
  typs : Type.compound array;
  data : data array;
  funs : fn array;
}

let create ?(typs = []) ?(data = []) ?(funs = []) ~name () = {
  name;
  typs = Array.of_list typs;
  data = Array.of_list data;
  funs = Array.of_list funs;
}

let name u = u.name
let typs u = Array.to_sequence u.typs
let data u = Array.to_sequence u.data
let funs u = Array.to_sequence u.funs

let insert_type u t = {
  u with typs = Array.push_back u.typs t;
}

let insert_data u d = {
  u with data = Array.push_back u.data d;
}

let insert_fn u fn = {
  u with funs = Array.push_back u.funs fn;
}

let remove_type u name = {
  u with typs = Array.remove_if u.typs ~f:(function
    | `compound (n, _, _) -> String.(n = name))
}

let remove_data u name = {
  u with data = Array.remove_if u.data ~f:(Fn.flip Data.has_name name);
}

let remove_fn u name = {
  u with funs = Array.remove_if u.funs ~f:(Fn.flip Fn.has_name name);
}

let map_typs u ~f = {
  u with typs = Array.map u.typs ~f;
}

let map_data u ~f = {
  u with data = Array.map u.data ~f;
}

let map_funs u ~f = {
  u with funs = Array.map u.funs ~f;
}
