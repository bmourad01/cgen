open Core
open Regular.Std

(* Ensure that we stay within the allotted bits for the payload. *)
let payload_mask = Int63.of_int ((1 lsl 57) - 1)

module Make(K : Hashtbl.Key) = struct
  module M = Map.Make(K)
  module P = Patricia_tree.Make(struct
      include Int63
      let size = 63
      let to_int = to_int_trunc
    end)

  type +'a t = 'a M.t P.t

  type 'a or_duplicate = [
    | `Ok of 'a t
    | `Duplicate
  ]

  exception Not_found = P.Not_found
  exception Duplicate = P.Duplicate

  let empty = P.empty
  let is_empty = P.is_empty

  let hash' k = Int63.(of_int (K.hash k) land payload_mask)

  let find_exn t k =
    hash' k |> P.find_exn t |>
    Fn.flip Map.find k |> function
    | None -> raise Not_found
    | Some v -> v

  let find t k = try Some (find_exn t k) with
    | Not_found -> None

  let mem t k = try ignore (find_exn t k); true with
    | Not_found -> false

  let singleton k v = P.singleton (hash' k) (M.singleton k v)

  let set t ~key ~data = P.update t (hash' key) ~f:(function
      | Some m -> Map.set m ~key ~data
      | None -> M.singleton key data)

  let add_multi t ~key ~data = P.update t (hash' key) ~f:(function
      | Some m -> Map.add_multi m ~key ~data
      | None -> M.singleton key [data])

  let add_exn t ~key ~data = P.update t (hash' key) ~f:(function
      | None -> M.singleton key data
      | Some m -> match Map.add m ~key ~data with
        | `Duplicate -> raise Duplicate
        | `Ok m -> m)

  let add t ~key ~data = try `Ok (add_exn t ~key ~data) with
    | Duplicate -> `Duplicate

  let remove t k = P.change t (hash' k)
      ~f:(Option.bind ~f:(fun m ->
          let m' = Map.remove m k in
          Option.some_if (not @@ Map.is_empty m') m'))

  let update t k ~f = P.update t (hash' k) ~f:(function
      | None -> M.singleton k @@ f None
      | Some m -> Map.update m k ~f)

  let update_with t k ~has ~nil =
    P.update_with t (hash' k)
      ~nil:(fun () -> M.singleton k @@ nil ())
      ~has:(fun m -> Map.update m k ~f:(function
          | Some v -> has v
          | None -> nil ()))

  let change t k ~f = P.change t (hash' k) ~f:(function
      | None -> f None |> Option.map ~f:(fun v -> M.singleton k v)
      | Some m ->
        let m' = Map.change m k ~f in
        Option.some_if (not @@ Map.is_empty m') m')

  let merge t1 t2 ~f =
    P.merge t1 t2 ~f:(fun ~key:_ -> Map.merge_skewed ~combine:f)

  let iter t ~f =
    P.iter t ~f:(fun ~key:_ ~data -> Map.iteri data ~f)

  let fold t ~init ~f =
    P.fold t ~init ~f:(fun ~key:_ ~data init -> Map.fold data ~init ~f)

  let length t =
    P.fold t ~init:0 ~f:(fun ~key:_ ~data acc -> acc + Map.length data)

  let keys t =
    fold t ~init:[] ~f:(fun ~key ~data:_ acc -> key :: acc)

  let data t =
    fold t ~init:[] ~f:(fun ~key:_ ~data acc -> data :: acc)

  let of_alist_exn =
    List.fold ~init:empty ~f:(fun acc (key, data) -> add_exn acc ~key ~data)

  let of_alist l = try Some (of_alist_exn l) with
    | Duplicate -> None

  let to_list t =
    fold t ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc)

  let to_sequence t =
    P.to_sequence t |>
    Seq.map ~f:snd |>
    Seq.bind ~f:Map.to_sequence
end
