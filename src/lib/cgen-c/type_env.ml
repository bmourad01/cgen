open Core

type enum_element = {
  ecname  : string;
  ectag   : string;
  ecvalue : int64;
} [@@deriving bin_io, compare, equal, hash, sexp]

module Enum_element = struct
  type t = enum_element [@@deriving bin_io, compare, equal, hash, sexp]
  let name c = c.ecname
  let tag c = c.ectag
  let value c = c.ecvalue
end

type tag =
  | Tenum of (string * int64) list
  | Tcompound of {
      kind   : Type.compound;
      fields : Tdecl.field list;
    }
[@@deriving bin_io, compare, equal, hash, sexp]

module Smap = Cgen_containers.Champ.Make(String)

type 'a map = 'a Smap.t [@@deriving bin_io, compare, equal, hash, sexp]

let empty_map = Smap.empty

(* NB: `lenv` is a stack of scopes, because variables
   defined in a deeper block scope are allowed to shadow
   those of the same name in a shallower one. *)
type t = {
  tenv : tag map;           (* tags *)
  eenv : enum_element map;  (* enum elements *)
  denv : Texpr.ty map;      (* typedefs *)
  fenv : Texpr.ty map;      (* functions *)
  venv : Texpr.ty map;      (* globals *)
  lenv : Texpr.ty map list; (* locals and params *)
} [@@deriving bin_io, compare, equal, hash, sexp]

let empty = {
  tenv = empty_map;
  eenv = empty_map;
  denv = empty_map;
  fenv = empty_map;
  venv = empty_map;
  lenv = [empty_map];
}

(* All four maps below share the ordinary-identifier namespace per C99. *)
let in_ordinary env name =
  Smap.mem env.eenv name ||
  Smap.mem env.denv name ||
  Smap.mem env.fenv name ||
  Smap.mem env.venv name

let add_tag env ~name info =
  match Smap.add env.tenv ~key:name ~data:info with
  | `Duplicate -> Or_error.errorf "tag %S already defined" name
  | `Ok tenv -> Ok {env with tenv}

let add_enum_element env ~name ~tag ~value =
  if in_ordinary env name
  then Or_error.errorf "identifier %S already declared" name
  else
    let data = {ecname = name; ectag = tag; ecvalue = value} in
    Ok {env with eenv = Smap.set env.eenv ~key:name ~data}

let add_typedef env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier %S already declared" name
  else Ok {env with denv = Smap.set env.denv ~key:name ~data:ty}

let add_func env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier %S already declared" name
  else Ok {env with fenv = Smap.set env.fenv ~key:name ~data:ty}

let add_global env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier %S already declared" name
  else Ok {env with venv = Smap.set env.venv ~key:name ~data:ty}

let add_local env ~name ty = match env.lenv with
  | [] -> failwith "Type_env.add_local: no scope on the stack"
  | m :: rest -> {env with lenv = Smap.set m ~key:name ~data:ty :: rest}

let strict_add_local env ~name ty = match env.lenv with
  | [] -> failwith "Type_env.strict_add_local: no scope on the stack"
  | m :: rest -> match Smap.add m ~key:name ~data:ty with
    | `Duplicate -> Or_error.errorf "redeclaration of %S" name
    | `Ok m -> Ok {env with lenv = m :: rest}

let push_scope env = {env with lenv = empty_map :: env.lenv}

let find_tag env name = Smap.find env.tenv name
let find_enum_element env name = Smap.find env.eenv name
let find_typedef env name = Smap.find env.denv name
let find_func env name = Smap.find env.fenv name
let find_global env name = Smap.find env.venv name
let find_local env name = List.find_map env.lenv ~f:(Fn.flip Smap.find name)

let has_tag env name = Smap.mem env.tenv name
let has_enum_element env name = Smap.mem env.eenv name
let has_typedef env name = Smap.mem env.denv name
let has_func env name = Smap.mem env.fenv name
let has_global env name = Smap.mem env.venv name
let has_local env name = List.exists env.lenv ~f:(Fn.flip Smap.mem name)

let tags env = Smap.to_sequence env.tenv
let enum_elements env = Smap.to_sequence env.eenv
let typedefs env = Smap.to_sequence env.denv
let funcs env = Smap.to_sequence env.fenv
let globals env = Smap.to_sequence env.venv

let locals env =
  let init = empty_map in
  Smap.to_sequence @@ List.fold env.lenv ~init ~f:(fun init m ->
      Smap.foldi m ~init ~f:(fun ~key ~data m ->
          match Smap.add m ~key ~data with
          | `Duplicate -> m
          | `Ok m -> m))

let is_tag_complete env name = match Smap.find env.tenv name with
  | None | Some (Tenum [] | Tcompound {fields = []; _}) -> false
  | Some _ -> true

(* Resolve typedefs in a type, returning a `Texpr.ty` with no `Tnamed`
   typedef nodes.

   Outer cv-qualifiers compose, e.g. a `const` on the typedef name
   unions with whatever the underlying type has. Struct/union/enum
   tags are not expanded.

   This function is idempotent.
*)
let normalize env ty =
  let rec go : Texpr.ty -> Texpr.ty = function
    | Tbase _ as t -> t
    | Tnamed {kind = `typedef; name; cv} as t ->
      find_typedef env name |>
      Option.value_map ~default:t ~f:(fun underlying ->
          let underlying = go underlying in
          let combined = Type.Cv.combine cv (Type.cv_of underlying) in
          Type.with_cv combined underlying)
    | Tnamed _ as t -> t
    | Tptr {pointee; restrict; cv} ->
      Type.ptr ~cv ~restrict (go pointee)
    | Tarray {elem; size = None; cv} ->
      Type.array ~cv (go elem)
    | Tarray {elem; size = Some _ as size; cv} ->
      Type.array ~cv ?size @@ go elem
    | Tfun {result; params = None; _} ->
      Type.fun_kr (go result)
    | Tfun {result; params = Some ps; variadic} ->
      let params =
        List.map ps ~f:(fun (p : Texpr.t Type.param) ->
            Type.{p with ptype = go p.ptype}) in
      Type.fun_ ~result:(go result) ~params ~variadic () in
  go ty
