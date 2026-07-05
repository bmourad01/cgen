open Core

(* pre: `align` is a positive power of 2 *)
let padding size align = ((size + align - 1) land -align) - size

type 'datum layout = {
  align   : int;
  size    : int;
  members : ('datum list, 'datum list list) Either.t;
} [@@deriving bin_io, compare, equal, hash, sexp]

let align l = l.align
let sizeof l = l.size
let is_empty l = l.size = 0
let members l = l.members

module type Field = sig
  type t [@@deriving bin_io, compare, equal, hash, sexp]
  type datum [@@deriving bin_io, compare, equal, hash, sexp]

  val pad : int -> datum
  val opaque : int -> datum
  val datum_bytes : datum -> int
  val try_merge : datum -> datum -> datum option
  val refs : t -> string list

  val field_data :
    gamma:(string -> datum layout) ->
    enclosing:string ->
    t ->
    datum list * int * int
end

module Make(F : Field) = struct
  type t = F.datum layout [@@deriving bin_io, compare, equal, hash, sexp]

  type compound = [
    | `struct_ of string * int option * F.t list
    | `union   of string * int option * F.t list
  ]

  type named = [
    | compound
    | `opaque of string * int * int
  ]

  let named_name : named -> string = function
    | `struct_ (s, _, _)
    | `union (s, _, _)
    | `opaque (s, _, _) -> s

  let named_align : named -> int option = function
    | `struct_ (_, a, _)
    | `union (_, a, _) -> a
    | `opaque (_, a, _) -> Some a

  (* pre: the list is accumulated in reverse *)
  let padded data = function
    | 0 -> data | p -> F.pad p :: data

  let coalesce ds =
    let rec aux acc = function
      | [] -> List.rev acc
      | x :: rest ->
        let acc = match acc with
          | [] -> [x]
          | y :: ys -> match F.try_merge y x with
            | Some m -> m :: ys
            | None -> x :: y :: ys in
        aux acc rest in
    aux [] ds

  let finalize data align size =
    padding size align |> padded data |> List.rev |> coalesce

  let sizeof_data d =
    List.fold d ~init:0 ~f:(fun s x -> s + F.datum_bytes x)

  let create_compound gamma name align fields =
    let data, align, size =
      let init = [], Option.value align ~default:1, 0 in
      List.fold fields ~init ~f:(fun (data, align, size) f ->
          let fdata, falign, fsize = F.field_data ~gamma ~enclosing:name f in
          let pad = padding size falign in
          let align = max align falign in
          let data = List.rev_append fdata @@ padded data pad in
          data, align, size + pad + fsize) in
    let member = finalize data align size in
    {align; size = sizeof_data member; members = First member}

  let create_union gamma name align fields =
    let fields' = List.map fields ~f:(fun f ->
        F.field_data ~gamma ~enclosing:name f) in
    let align = List.fold fields'
        ~init:(Option.value align ~default:1)
        ~f:(fun acc (_, falign, _) -> max acc falign) in
    let raw_size = List.fold fields' ~init:0
        ~f:(fun acc (_, _, fsize) -> max acc fsize) in
    let size =
      if raw_size = 0 then 0
      else raw_size + padding raw_size align in
    let members = if size = 0 then [] else
        List.map fields' ~f:(fun (fdata, _, fsize) ->
            let tail_pad = size - fsize in
            let data =
              if tail_pad > 0 then fdata @ [F.pad tail_pad] else fdata in
            coalesce data) in
    {align; size; members = Second members}

  let create gamma : named -> t = function
    | `opaque (s, n, _) | `struct_ (s, Some n, _)
    | `union (s, Some n, _)
      when n < 1 || (n land (n - 1)) <> 0 ->
      invalid_argf "Invalid alignment %d for type :%s, \
                    must be positive power of 2" n s ()
    | `opaque (s, _, n) when n < 1 ->
      invalid_argf "Invalid number of bytes %d for opaque \
                    type :%s, must be greater than 0" n s ()
    | `opaque (_, align, n) ->
      let d = padded [F.opaque n] @@ padding n align in
      {align; size = sizeof_data d; members = First d}
    | `struct_ (_, Some n, []) ->
      {align = n; size = 0; members = First []}
    | `struct_ (_, None, []) ->
      {align = 1; size = 0; members = First []}
    | `union (_, Some n, []) ->
      {align = n; size = 0; members = Second []}
    | `union (_, None, []) ->
      {align = 1; size = 0; members = Second []}
    | `struct_ (name, align, fields) ->
      create_compound gamma name align fields
    | `union (name, align, fields) ->
      create_union gamma name align fields

  module Typegraph = struct
    type t = String.Set.t String.Map.t

    let empty = String.Map.empty

    let insert n (g : t) : t =
      if Map.mem g n then g
      else Map.set g ~key:n ~data:String.Set.empty

    let add_edge ~src ~dst g : t =
      let g = insert dst g in
      Map.update g src ~f:(function
          | None -> String.Set.singleton dst
          | Some s -> Set.add s dst)

    let succs n g = match Map.find g n with
      | None -> String.Set.empty
      | Some s -> s

    let nodes g = Map.keys g

    let reverse_postorder g =
      let vis = String.Hash_set.create () in
      let out = ref [] in
      let rec visit n =
        Hash_set.strict_add vis n |>
        Or_error.iter ~f:(fun () ->
            Set.iter (succs n g) ~f:visit;
            out := n :: !out) in
      List.iter (nodes g) ~f:visit;
      !out

    let strong_components g =
      let index = ref 0 in
      let idx = String.Table.create () in
      let low = String.Table.create () in
      let on_stack = String.Hash_set.create () in
      let (.$[]) t k = Hashtbl.find_exn t k in
      let (.$[]<-) t k v = Hashtbl.set t ~key:k ~data:v in
      let (!!) x = Option.value_exn x in
      let stack = Stack.create () in
      let comps = ref [] in
      let rec connect v =
        idx.$[v] <- !index;
        low.$[v] <- !index;
        incr index;
        Stack.push stack v;
        Hash_set.add on_stack v;
        Set.iter (succs v g) ~f:(fun w ->
            match Hashtbl.find idx w with
            | None ->
              connect w;
              Hashtbl.update low v ~f:(fun lv -> Int.min !!lv low.$[w])
            | Some iw when Hash_set.mem on_stack w ->
              Hashtbl.update low v ~f:(fun lv -> Int.min !!lv iw)
            | Some _ -> ());
        if low.$[v] = idx.$[v] then
          let members = ref [] in
          let continue = ref true in
          while !continue do
            let w = Stack.pop_exn stack in
            Hash_set.remove on_stack w;
            members := w :: !members;
            if String.(w = v) then continue := false
          done;
          comps := !members :: !comps in
      List.iter (nodes g) ~f:(fun v ->
          if not (Hashtbl.mem idx v) then connect v);
      !comps
  end

  let build_tenv ts =
    List.fold ts ~init:String.Map.empty ~f:(fun tenv t ->
        let name = named_name t in
        match Map.add tenv ~key:name ~data:t with
        | `Duplicate -> invalid_argf "Duplicate type :%s" name ()
        | `Ok tenv -> tenv)

  let build_typ_graph tenv ts =
    let add_fields name fields g =
      let init = Typegraph.insert name g in
      List.fold fields ~init ~f:(fun g f ->
          List.fold (F.refs f) ~init:g ~f:(fun g n ->
              if Map.mem tenv n then
                Typegraph.add_edge ~src:n ~dst:name g
              else
                invalid_argf "Undeclared type field :%s in type :%s"
                  n name ())) in
    List.fold ts ~init:Typegraph.empty ~f:(fun g -> function
        | `opaque (name, _, _) -> Typegraph.insert name g
        | `struct_ (name, _, fields)
        | `union (name, _, fields) -> add_fields name fields g)

  let check_typ_cycles g =
    Typegraph.strong_components g |> List.iter ~f:(function
        | [] -> ()
        | [name] ->
          if Set.mem (Typegraph.succs name g) name
          then invalid_argf "Cycle detected in type :%s" name ()
        | xs ->
          invalid_argf "Cycle detected in types %s"
            (List.to_string ~f:(fun s -> ":" ^ s) xs)
            ())

  let layouts tenv g =
    let genv = String.Table.create () in
    Typegraph.reverse_postorder g |>
    List.map ~f:(fun name ->
        let t = Map.find_exn tenv name in
        let gamma name = match Hashtbl.find genv name with
          | None -> invalid_argf "Type :%s not found in gamma" name ()
          | Some l -> l in
        let l = create gamma t in
        Hashtbl.set genv ~key:name ~data:l;
        name, l)

  let of_types ts =
    let tenv = build_tenv ts in
    let g = build_typ_graph tenv ts in
    check_typ_cycles g;
    layouts tenv g
end
