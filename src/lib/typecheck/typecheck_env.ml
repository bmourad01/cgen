open Core
open Regular.Std
open Virtual

let unify_fail t t' v fn = Or_error.errorf
    "Failed to unify types '%a' and '%a' for var %a in function $%s"
    Type.pps t Type.pps t' Var.pps v @@ Func.name fn

type t = {
  target : Target.t;
  denv   : Type.compound String.Map.t;
  fenv   : Type.proto String.Map.t;
  tenv   : Type.compound String.Map.t;
  venv   : Type.t Var.Map.t String.Map.t;
  genv   : Type.layout String.Map.t;
}

let create target = {
  target;
  denv = String.Map.empty;
  fenv = String.Map.empty;
  tenv = String.Map.empty;
  venv = String.Map.empty;
  genv = String.Map.empty;
}

let target t = t.target

let add_data d env =
  let name = Data.name d in
  let word = Target.word env.target in
  if Map.mem env.fenv name then
    Or_error.errorf "Tried to redefine function $%s as data" name
  else match Map.add env.denv ~key:name ~data:(Data.typeof d ~word) with
    | `Duplicate -> Or_error.errorf "Redefinition of data $%s" name
    | `Ok denv -> Ok {env with denv}

(* If we don't have the data defined in the module, then assume it is
   external (i.e. it is linked with our program a posteriori), and that
   the user accepts the risk. *)
let typeof_data name env = Map.find env.denv name

let datanames env =
  Map.to_sequence env.denv |> Seq.map ~f:fst

let add_fn fn env =
  let name = Func.name fn in
  if Map.mem env.denv name then
    Or_error.errorf "Tried to redefine data $%s as a function" name
  else match Map.add env.fenv ~key:name ~data:(Func.typeof fn) with
    | `Duplicate -> Or_error.errorf "Redefinition of function $%s" name
    | `Ok fenv -> Ok {env with fenv}

(* If we don't have the function defined in the module, then assume
   it is external (i.e. it is linked with our program a posteriori),
   and that the user accepts the risk. *)
let typeof_fn name env = Map.find env.fenv name

let funcnames env =
  Map.to_sequence env.fenv |> Seq.map ~f:fst

let check_typ_align t name = match Type.compound_align t with
  | Some n when n < 1 || (n land (n - 1)) <> 0 ->
    Or_error.errorf "Invalid alignment %d of type :%s, must be \
                     positive power of 2" n name
  | Some _ | None -> Ok ()

let add_typ t env =
  let name = Type.compound_name t in
  check_typ_align t name |> Or_error.bind ~f:(fun () ->
      match Map.add env.tenv ~key:name ~data:t with
      | `Duplicate -> Or_error.errorf "Redefinition of type :%s" name
      | `Ok tenv -> Ok {env with tenv})

let typeof_typ name env = match Map.find env.tenv name with
  | None -> Or_error.errorf "Undefined type %s" name
  | Some t -> Ok t

let typenames env =
  Map.to_sequence env.tenv |> Seq.map ~f:fst

let typeof_var fn v env =
  let fname = Func.name fn in
  match Map.find env.venv fname with
  | None ->
    Or_error.errorf
      "No function $%s in environment for variable %a"
      fname Var.pps v
  | Some m -> match Map.find m @@ Var.base v with
    | Some t -> Ok t
    | None ->
      Or_error.errorf
        "No variable %a in function $%s"
        Var.pps v fname

exception Unify_fail of Type.t

let add_var fn v t env = try
    let v = Var.base v in
    let venv = Map.update env.venv (Func.name fn) ~f:(function
        | None -> Var.Map.singleton v t
        | Some m -> Map.update m v ~f:(function
            | Some t' when Type.(t <> t') ->
              raise_notrace @@ Unify_fail t'
            | Some _ -> t
            | None -> t)) in
    Ok {env with venv}
  with Unify_fail t' -> unify_fail t t' v fn

let layout name env = match Map.find env.genv name with
  | None -> Or_error.errorf "Type :%s not found in gamma" name
  | Some l -> Ok l
