open Core

module Rrb = Cgen_containers.Rrb

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
      fields : Tdecl.field list option;  (* None: incomplete (forward-declared) *)
      attrs  : Attr.set;
    }
[@@deriving bin_io, compare, equal, hash, sexp]

module Smap = Cgen_containers.Champ.Make(String)

type 'a map = 'a Smap.t [@@deriving bin_io, compare, equal, hash, sexp]

let empty_map = Smap.empty

type tagid = int [@@deriving bin_io, compare, equal, hash, sexp]

(* NB: `lenv` and `tscopes` are stacks of scopes, because names
   defined in a deeper block scope are allowed to shadow those of
   the same name in a shallower one.

   Tags are split into a persistent store and a lexical scope stack.
   `tdefs`/`tnames` are indexed by identity and never popped, because
   the lowering (which has no notion of scope) must see every tag
   globally.
*)
type t = {
  tdefs   : tag Rrb.t;         (* tag info, by identity *)
  tnames  : string Rrb.t;      (* display name, by identity *)
  tids    : tagid map;         (* identity, by display name (persistent) *)
  tscopes : tagid map list;    (* per-scope: identify by source tag name *)
  eenv    : enum_element map;  (* enum elements *)
  denv    : Texpr.ty map;      (* typedefs *)
  fenv    : Texpr.ty map;      (* functions *)
  venv    : Texpr.ty map;      (* globals *)
  lenv    : Texpr.ty map list; (* locals and params *)
} [@@deriving bin_io, compare, equal, hash, sexp]

let empty = {
  tdefs   = Rrb.empty;
  tnames  = Rrb.empty;
  tids    = empty_map;
  tscopes = [empty_map];
  eenv    = empty_map;
  denv    = empty_map;
  fenv    = empty_map;
  venv    = empty_map;
  lenv    = [empty_map];
}

(* All four maps below share the ordinary-identifier namespace per C99. *)
let in_ordinary env name =
  Smap.mem env.eenv name ||
  Smap.mem env.denv name ||
  Smap.mem env.fenv name ||
  Smap.mem env.venv name

let same_compound_kind (a : Type.compound) (b : Type.compound) = match a, b with
  | `struct_, `struct_ | `union, `union -> true
  | _ -> false

let cur_tscope env = match env.tscopes with
  | m :: _ -> m
  | [] -> failwith "Type_env: empty tag scope stack"

let with_cur_tscope env m = match env.tscopes with
  | _ :: rest -> {env with tscopes = m :: rest}
  | [] -> failwith "Type_env: empty tag scope stack"

let fresh_display env name id =
  if Smap.mem env.tids name then Printf.sprintf "%s.%d" name id else name

(* Register a tag definition, returning the updated environment and the
   display name the tag was given (which the caller records in the
   elaborated type and layout). *)
let add_tag env ~name info =
  match Smap.find (cur_tscope env) name with
  | Some id ->
    (* When we have a redeclaration in the same scope, we either complete
       a forward declaration, accept a redundant re-forward-declaration,
       or reject an incompatible redefinition. The identity is preserved. *)
    let disp = Rrb.get_exn env.tnames id in
    let store info = {env with tdefs = Rrb.set env.tdefs id info} in
    begin match Rrb.get_exn env.tdefs id, info with
      | Tcompound {kind = ek; fields = None; _}, Tcompound {kind = nk; _}
        when same_compound_kind ek nk -> Ok (store info, disp)
      | Tcompound {fields = None; _}, _ ->
        Or_error.errorf "tag '%s' redeclared as a different kind" name
      | _, Tcompound {fields = None; _} -> Ok (env, disp)
      | _ -> Or_error.errorf "tag '%s' already defined" name
    end
  | None ->
    let id = Rrb.length env.tdefs in
    let disp = fresh_display env name id in
    let env = {
      env with
      tdefs = Rrb.snoc env.tdefs info;
      tnames = Rrb.snoc env.tnames disp;
      tids = Smap.set env.tids ~key:disp ~data:id;
    } in
    let env =
      with_cur_tscope env @@
      Smap.set (cur_tscope env) ~key:name ~data:id in
    Ok (env, disp)

let add_enum_element env ~name ~tag ~value =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else
    let data = {ecname = name; ectag = tag; ecvalue = value} in
    Ok {env with eenv = Smap.set env.eenv ~key:name ~data}

let add_typedef env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else Ok {env with denv = Smap.set env.denv ~key:name ~data:ty}

let add_func env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else Ok {env with fenv = Smap.set env.fenv ~key:name ~data:ty}

let add_global env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else Ok {env with venv = Smap.set env.venv ~key:name ~data:ty}

let add_local env ~name ty = match env.lenv with
  | [] -> failwith "Type_env.add_local: no scope on the stack"
  | m :: rest -> {env with lenv = Smap.set m ~key:name ~data:ty :: rest}

let strict_add_local env ~name ty = match env.lenv with
  | [] -> failwith "Type_env.strict_add_local: no scope on the stack"
  | m :: rest -> match Smap.add m ~key:name ~data:ty with
    | `Duplicate -> Or_error.errorf "redeclaration of '%s'" name
    | `Ok m -> Ok {env with lenv = m :: rest}

let push_scope env = {
  env with
  lenv = empty_map :: env.lenv;
  tscopes = empty_map :: env.tscopes;
}

let exit_block ~saved env = {
  env with
  eenv = saved.eenv;
  denv = saved.denv;
  lenv = saved.lenv;
  tscopes = saved.tscopes;
}

let resolve_tag env name =
  List.find_map env.tscopes ~f:(fun m -> Smap.find m name) |>
  Option.map ~f:(Rrb.get_exn env.tnames)

let find_tag env disp = Option.bind (Smap.find env.tids disp) ~f:(Rrb.get env.tdefs)
let find_enum_element env name = Smap.find env.eenv name
let find_typedef env name = Smap.find env.denv name
let find_func env name = Smap.find env.fenv name
let find_global env name = Smap.find env.venv name
let find_local env name = List.find_map env.lenv ~f:(Fn.flip Smap.find name)

let has_tag env disp = Smap.mem env.tids disp
let has_enum_element env name = Smap.mem env.eenv name
let has_typedef env name = Smap.mem env.denv name
let has_func env name = Smap.mem env.fenv name
let has_global env name = Smap.mem env.venv name
let has_local env name = List.exists env.lenv ~f:(Fn.flip Smap.mem name)

let tags env =
  Rrb.to_sequence env.tdefs |>
  Sequence.mapi ~f:(fun id tag -> Rrb.get_exn env.tnames id, tag)

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

let is_tag_complete env disp = match find_tag env disp with
  | None | Some (Tenum [] | Tcompound {fields = None; _}) -> false
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

let rec incomplete_object_type env ty = match normalize env ty with
  | Tnamed {kind = #Type.compound; name; _} ->
    if is_tag_complete env name then None else Some name
  | Tarray {elem; _} -> incomplete_object_type env elem
  | _ -> None
