open Core
open Virtual

module Vtree = Var.Tree
module Ltree = Label.Tree
module Vset = Var.Tree_set
module Smap = Cgen_containers.Champ.Make(String)

type 'a map = 'a Smap.t

exception Fail of Error.t

let failf fmt =
  Printf.ksprintf
    (fun msg -> raise_notrace (Fail (Error.of_string msg)))
    fmt

let or_error f =
  try Ok (f ())
  with Fail e -> Error e
[@@inline]

let ok = function
  | Error e -> raise_notrace (Fail e)
  | Ok x -> x
[@@inline]

type t = {
  target : Target.t;
  denv   : Type.named map;
  fenv   : Type.proto map;
  tenv   : Type.named map;
  venv   : Type.t Vtree.t map;
  genv   : Type.layout map;
}

let create target = {
  target;
  denv = Smap.empty;
  fenv = Smap.empty;
  tenv = Smap.empty;
  venv = Smap.empty;
  genv = Smap.empty;
}

let target t = t.target [@@inline]

let add_data_exn d env =
  let name = Data.name d in
  let word = Target.word env.target in
  if Smap.mem env.fenv name then
    failf "Tried to redefine function $%s as data" name
  else match Smap.add env.denv ~key:name ~data:(Data.typeof d ~word) with
    | `Duplicate -> failf "Redefinition of data $%s" name
    | `Ok denv -> {env with denv}

(* If we don't have the data defined in the module, then assume it is
   external (i.e. it is linked with our program a posteriori), and that
   the user accepts the risk. *)
let typeof_data name env = Smap.find env.denv name [@@inline]

let datanames env =
  Smap.to_sequence env.denv |> Sequence.map ~f:fst
[@@inline]

let add_fn_exn fn env =
  let name = Func.name fn in
  if Smap.mem env.denv name then
    failf "Tried to redefine data $%s as a function" name
  else match Smap.add env.fenv ~key:name ~data:(Func.typeof fn) with
    | `Duplicate -> failf "Redefinition of function $%s" name
    | `Ok fenv -> {env with fenv}

(* If we don't have the function defined in the module, then assume
   it is external (i.e. it is linked with our program a posteriori),
   and that the user accepts the risk. *)
let typeof_fn name env = Smap.find env.fenv name [@@inline]

let funcnames env =
  Smap.to_sequence env.fenv |> Sequence.map ~f:fst
[@@inline]

let check_typ_align t name = match Type.named_align t with
  | Some n when n < 1 || (n land (n - 1)) <> 0 ->
    failf "Invalid alignment %d of type :%s, must be \
           positive power of 2" n name
  | Some _ | None -> ()

let add_typ_exn t env =
  let name = Type.named_name t in
  check_typ_align t name;
  match Smap.add env.tenv ~key:name ~data:t with
  | `Duplicate -> failf "Redefinition of type :%s" name
  | `Ok tenv -> {env with tenv}

let typeof_typ_exn name env = match Smap.find env.tenv name with
  | None -> failf "Undefined type %s" name
  | Some t -> t
[@@inline]

let typenames env =
  Smap.to_sequence env.tenv |> Sequence.map ~f:fst
[@@inline]

let typeof_var_exn fn v env =
  let fname = Func.name fn in
  match Smap.find env.venv fname with
  | None ->
    failf "No function $%s in environment for variable %a" fname Var.pps v
  | Some m -> match Vtree.find m v with
    | Some t -> t
    | None -> failf "No variable %a in function $%s" Var.pps v fname

let add_var_exn fn v t env =
  let key = Func.name fn in
  let venv = Smap.update env.venv key ~f:(function
      | None -> Vtree.singleton v t
      | Some m ->
        Vtree.update_with m v
          ~nil:(fun () -> t)
          ~has:(fun t' ->
              if Type.(t <> t') then
                failf "Failed to unify types '%a' and '%a' for var %a in function $%s"
                  Type.pps t Type.pps t' Var.pps v key;
              t)) in
  {env with venv}

let add_layout_exn name l env =
  match Smap.add env.genv ~key:name ~data:l with
  | `Ok genv -> {env with genv}
  | `Duplicate -> failf "Redefinition of layout for :%s" name

let layout_exn name env = match Smap.find env.genv name with
  | None -> failf "Type :%s not found in gamma" name
  | Some l -> l

let add_typ t env = or_error @@ fun () -> add_typ_exn t env [@@inline]
let add_data d env = or_error @@ fun () -> add_data_exn d env [@@inline]
let add_fn fn env = or_error @@ fun () -> add_fn_exn fn env [@@inline]
let add_var fn v t env = or_error @@ fun () -> add_var_exn fn v t env [@@inline]
let typeof_typ name env = or_error @@ fun () -> typeof_typ_exn name env [@@inline]
let typeof_var fn v env = or_error @@ fun () -> typeof_var_exn fn v env [@@inline]
let layout name env = or_error @@ fun () -> layout_exn name env [@@inline]

(* Type collection. *)

let const_typ target : const -> Type.t = function
  | `bool _ -> `flag
  | `int (_, t) -> (t :> Type.t)
  | `float _ -> `f32
  | `double _ -> `f64
  | `sym _ -> (Target.word target :> Type.t)

let resolve_typ env : [Type.arg | `flag] -> Type.t = function
  | #Type.basic as b -> (b :> Type.t)
  | `flag -> `flag
  | `name n -> (typeof_typ_exn n env :> Type.t)

let fold_label_dsts (c : ctrl) ~init ~f =
  let do_dst acc (d : dst) = match d with
    | `label (l, args) -> f acc l args
    | _ -> acc in
  match c with
  | `hlt | `ret _ -> init
  | `jmp d -> do_dst init d
  | `br (_, t, e) -> do_dst (do_dst init t) e
  | `sw (_, _, d, tbl) ->
    let acc = do_dst init (d :> dst) in
    Ctrl.Table.enum tbl |> Sequence.fold ~init:acc
      ~f:(fun acc (_, l) -> do_dst acc (l :> dst))

let collect_fn env fn =
  let target = env.target in
  let word = (Target.word target :> Type.t) in
  (* Function arguments. *)
  let vt = Func.fold_args fn ~init:Vtree.empty ~f:(fun vt (x, t) ->
      let ty = resolve_typ env (t :> [Type.arg | `flag]) in
      Vtree.set vt ~key:x ~data:ty) in
  (* Stack slots, which are pointers. *)
  let vt = Func.fold_slots fn ~init:vt ~f:(fun vt s ->
      Vtree.set vt ~key:(Slot.var s) ~data:word) in
  (* Instruction results. *)
  let vt = Func.fold_blks fn ~init:vt ~f:(fun vt b ->
      Blk.fold_insns b ~init:vt ~f:(fun vt i ->
          match Insn.lhs i, Insn.typeof i with
          | Some x, Some t ->
            Vtree.set vt ~key:x ~data:(resolve_typ env t)
          | _ -> vt)) in
  (* Block parameters. *)
  let blk_params =
    Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
        Ltree.set acc ~key:(Blk.label b) ~data:(Blk.args_to_list b)) in
  let incoming =
    Func.fold_blks fn ~init:Vtree.empty ~f:(fun acc b ->
        fold_label_dsts (Blk.ctrl b) ~init:acc ~f:(fun acc l args ->
            match Ltree.find blk_params l with
            | None -> acc
            | Some params -> match List.zip params args with
              | Unequal_lengths -> acc
              | Ok pairs ->
                List.fold pairs ~init:acc ~f:(fun acc (p, a) ->
                    if Vtree.mem acc p then acc
                    else Vtree.set acc ~key:p ~data:a))) in
  let rec resolve vt visiting x = match Vtree.find vt x with
    | Some _ -> vt
    | None -> match Vtree.find incoming x with
      | None -> vt
      | Some _ when Vset.mem visiting x -> vt
      | Some (#const as c) ->
        Vtree.set vt ~key:x ~data:(const_typ target c)
      | Some (`var v) ->
        let visiting = Vset.add visiting x in
        let vt = resolve vt visiting v in
        match Vtree.find vt v with
        | Some t -> Vtree.set vt ~key:x ~data:t
        | None -> vt in
  Vtree.keys incoming |> List.fold ~init:vt
    ~f:(fun vt x -> resolve vt Vset.empty x)

let set_fn env fn =
  let key = Func.name fn in
  let data = collect_fn env fn in
  let venv = Smap.set env.venv ~key ~data in
  {env with venv}

let collect_fns env fns = or_error @@ fun () ->
  List.fold fns ~init:env ~f:set_fn

let collect_module_level m target =
  let env = create target in
  let env = Module.fold_typs m ~init:env ~f:(fun env t -> add_typ_exn t env) in
  let layouts = ok (Type.layouts_of_types (Smap.data env.tenv)) in
  let env = List.fold layouts ~init:env
      ~f:(fun env (name, l) -> add_layout_exn name l env) in
  let env = Module.fold_data m ~init:env ~f:(fun env d -> add_data_exn d env) in
  Module.fold_funs m ~init:env ~f:(fun env fn -> add_fn_exn fn env)

let collect m ~target = or_error @@ fun () ->
  Module.fold_funs m ~init:(collect_module_level m target) ~f:set_fn
