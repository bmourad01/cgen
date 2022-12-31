open Core
open Regular.Std

module Array = struct
  include Array

  let insert xs x i =
    init (length xs + i) ~f:(fun j ->
        if j < i then xs.(j)
        else if j = i then x
        else xs.(j - 1))

  let push_back xs x = insert xs x @@ length xs
  let push_front xs x = insert xs x 0

  let remove_if xs ~f =
    if Array.exists xs ~f
    then Array.filter xs ~f:(Fn.non f)
    else xs

  let update_if xs y ~f =
    if Array.exists xs ~f
    then Array.map xs ~f:(fun x -> if f x then y else x)
    else xs

  let pp ppx ppf xs =
    let last = Array.length xs - 1 in
    Array.iteri xs ~f:(fun i x ->
        if i < last
        then Format.fprintf ppf "%a@;" ppx x
        else Format.fprintf ppf "%a" ppx x)
end

module Insn = struct
  type const = [
    | `int   of Bitvec.t
    | `float of Decimal.t
    | `sym   of string
  ]

  type arg = [
    | const
    | `var of Var.t
  ]

  let pp_arg ppf : arg -> unit = function
    | `var v -> Format.fprintf ppf "%a" Var.pp v
    | `sym s -> Format.fprintf ppf "@@%s" s
    | `int i -> Format.fprintf ppf "%a" Bitvec.pp i
    | `float f -> Format.fprintf ppf "%a" Decimal.pp f

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
      dst : Var.t;
      typ : [Type.basic | Type.special];
      ins : arg Label.Map.t;
    }

    let create ?(ins = []) ~dst ~typ () = {
      dst;
      typ;
      ins = Label.Map.of_alist_exn ins;
    }

    let dst p = p.dst
    let typ p = p.typ
    let ins p = Map.to_sequence p.ins

    let rec pp_ins ppl ppf = function
      | (l, x) :: (_ :: _ as rest) ->
        Format.fprintf ppf "%a -> %a,@;%a"
          ppl l pp_arg x (pp_ins ppl) rest
      | [l, x] -> Format.fprintf ppf "%a -> %a" ppl l pp_arg x
      | [] -> ()

    let pp_self ppl ppf p =
      let ins = Map.to_alist p.ins in
      Format.fprintf ppf "%a = phi.%a [@[<v 0>%a@]]"
        Var.pp p.dst Type.pp (p.typ :> Type.t) (pp_ins ppl) ins

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
      | `udiv of Type.basic * arg * arg
      | `urem of Type.basic * arg * arg
    ]

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
        Format.fprintf ppf "urem.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `urem (t, x, y) ->
        Format.fprintf ppf "udiv.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y

    type bits = [
      | `and_ of Type.imm * arg * arg
      | `or_  of Type.imm * arg * arg
      | `sar  of Type.imm * arg * arg
      | `shl  of Type.imm * arg * arg
      | `shr  of Type.imm * arg * arg
      | `xor  of Type.imm * arg * arg
    ]

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
      | `o   of Type.basic * arg * arg
      | `sge of Type.basic * arg * arg
      | `sgt of Type.basic * arg * arg
      | `sle of Type.basic * arg * arg
      | `slt of Type.basic * arg * arg
      | `sne of Type.basic * arg * arg
      | `uo  of Type.basic * arg * arg
    ]

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
        Format.fprintf ppf "o.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `sge (t, x, y) ->
        Format.fprintf ppf "sge.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `sgt (t, x, y) ->
        Format.fprintf ppf "sgt.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `sle (t, x, y) ->
        Format.fprintf ppf "sle.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `slt (t, x, y) ->
        Format.fprintf ppf "slt.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `sne (t, x, y) ->
        Format.fprintf ppf "sne.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y
      | `uo (t, x, y) ->
        Format.fprintf ppf "uo.%a %a, %a" Type.pp_basic t pp_arg x pp_arg y

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
      | `copy of Type.basic * arg
      | `select of Type.basic * Var.t * arg * arg
    ]

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

    type assign_call = [
      | `acall  of Var.t * Type.basic * global * arg list
      | `acallv of Var.t * Type.basic * global * arg list
    ]

    type call = [
      | void_call
      | assign_call
    ]

    let is_variadic : call -> bool = function
      | `acallv _ | `callv _ -> true
      | `acall _  | `call _  -> false

    let rec pp_call_args variadic ppf = function
      | x :: (_ :: _ as rest) ->
        Format.fprintf ppf "%a, %a" pp_arg x (pp_call_args variadic) rest
      | [x] when not variadic -> Format.fprintf ppf "%a" pp_arg x
      | [x] -> Format.fprintf ppf "%a, ..." pp_arg x
      | [] when not variadic -> ()
      | [] -> Format.fprintf ppf "..."

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

    let pp ppf = function
      | #call as c -> pp_call ppf c
      | `op (l, r) -> Format.fprintf ppf "%a = %a" Var.pp l pp_op r
  end

  module Ctrl = struct
    type t = [
      | `jmp    of dst
      | `jnz    of Var.t * dst * dst
      | `ret    of arg option
      | `switch of Type.imm * Var.t * Label.t * (Bitvec.t * Label.t) list
    ]

    let rec pp_switch_table ppl ppf = function
      | (v, l) :: (_ :: _ as rest) ->
        Format.fprintf ppf "%a -> %a,@;%a"
          Bitvec.pp v ppl l (pp_switch_table ppl) rest
      | [v, l] -> Format.fprintf ppf "%a -> %a" Bitvec.pp v ppl l
      | [] -> ()

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
          Type.pp_imm t Var.pp x Label.pp ld (pp_switch_table ppl) tbl

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
  let nth_data b n = b.data.(n)
  let ctrl b = b.ctrl

  let map_data b ~f = {
    b with data = Array.map b.data ~f;
  }

  let concat_map_data b ~f =
    let f = Fn.compose Array.of_list f in {
      b with data = Array.concat_map b.data ~f
    }

  let map_ctrl b ~f = {
    b with ctrl = f b.ctrl;
  }

  let pp ppf b = match b.phi, b.data with
    | [||], [||] ->
      Format.fprintf ppf "%a:@;%a"
        Label.pp b.label Insn.pp_ctrl b.ctrl
    | _, [||] ->
      Format.fprintf ppf "%a:@;%a@;%a"
        Label.pp b.label
        (Array.pp Insn.pp_phi) b.phi
        Insn.pp_ctrl b.ctrl
    | [||], _ ->
      Format.fprintf ppf "%a:@;%a@;%a"
        Label.pp b.label
        (Array.pp Insn.pp_data) b.data
        Insn.pp_ctrl b.ctrl
    | _ ->
      Format.fprintf ppf "%a:@;%a@;%a@;%a"
        Label.pp b.label
        (Array.pp Insn.pp_phi) b.phi
        (Array.pp Insn.pp_data) b.data
        Insn.pp_ctrl b.ctrl

  let pp_hum ppf b = match b.phi, b.data with
    | [||], [||] ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@]"
        Label.pp_hum b.label Insn.pp_ctrl_hum b.ctrl
    | _, [||] ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@;%a@]"
        Label.pp_hum b.label
        (Array.pp Insn.pp_phi_hum) b.phi
        Insn.pp_ctrl_hum b.ctrl
    | [||], _ ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@;%a@]"
        Label.pp_hum b.label
        (Array.pp Insn.pp_data_hum) b.data
        Insn.pp_ctrl_hum b.ctrl
    | _ ->
      Format.fprintf ppf "%a:@[<v 1>@;%a@;%a@;%a@]"
        Label.pp_hum b.label
        (Array.pp Insn.pp_phi_hum) b.phi
        (Array.pp Insn.pp_data_hum) b.data
        Insn.pp_ctrl_hum b.ctrl

end

type blk = Blk.t

module Fn = struct
  type t = {
    name     : string;
    blks     : blk array;
    entry    : Label.t;
    args     : (Var.t * Type.t) array;
    return   : Type.t option;
    variadic : bool;
    linkage  : Linkage.t;
  }

  let create
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

  let name fn = fn.name
  let blks fn = Array.to_sequence fn.blks
  let entry fn = fn.entry
  let args fn = Array.to_sequence fn.args
  let return fn = fn.return
  let variadic fn = fn.variadic
  let linkage fn = fn.linkage

  let map_blks fn ~f = {
    fn with blks = Array.map fn.blks ~f;
  }

  let rec pp_args_aux ppf = function
    | (v, t) :: (_ :: _ as rest) ->
      Format.fprintf ppf "%a %a, %a" Type.pp t Var.pp v pp_args_aux rest
    | [v, t] -> Format.fprintf ppf "%a %a" Type.pp t Var.pp v
    | [] -> ()

  let pp_args ppf fn = match fn.variadic, fn.args with  
    | false, [||] -> ()
    | false, args -> pp_args_aux ppf @@ Array.to_list args
    | true, [||] -> Format.fprintf ppf "..."
    | true, args ->
      Format.fprintf ppf "%a, ..." pp_args_aux @@ Array.to_list args

  let pp ppf fn =
    Format.fprintf ppf "%a@;function " Linkage.pp fn.linkage;
    Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp);
    Format.fprintf ppf "@@%s(%a):@;@[<v 0>%a@]"
      fn.name pp_args fn (Array.pp Blk.pp) fn.blks

  let pp_hum ppf fn =
    Format.fprintf ppf "%a@;function " Linkage.pp fn.linkage;
    Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp);
    Format.fprintf ppf "@@%s(%a) {@;@[%a@]@;}"
      fn.name pp_args fn (Array.pp Blk.pp_hum) fn.blks
end

type fn = Fn.t
