open Core
open Pseudo

module Bitset = Cgen_containers.Bitset

module Take = struct
  type ('a, _) t =
    | T0 : ('a, _) t
    | T1 : 'a -> ('a, [`one]) t
    | T2 : 'a * 'a -> ('a, [`two]) t
    | T3 : 'a * 'a * 'a -> ('a, [`three]) t

  type _ key =
    | K1 : [`one] key
    | K2 : [`two] key
    | K3 : [`three] key
end

let (.!()) a i = Array.unsafe_get a i
let (.!()<-) a i x = Array.unsafe_set a i x

module View = struct
  type 'a t = 'a array

  let length = Array.length

  let get_exn t i = t.(i)

  let take (type k) t i (k : k Take.key) : (_, k) Take.t =
    let n = Array.length t in
    if i < 0 then T0 else match k with
      | K1 -> if i + 1 <= n then T1 t.!(i) else T0
      | K2 ->
        if i + 2 <= n
        then T2 (t.!(i), t.!(i + 1))
        else T0
      | K3 ->
        if i + 3 <= n
        then T3 (t.!(i), t.!(i + 1), t.!(i + 2))
        else T0
end

module Edit = struct
  type 'a t =
    | Rewrite of int * 'a
    | Delete of int
end

type 'a view = 'a View.t
type 'a edit = 'a Edit.t
type 'a rule = 'a view -> int -> ('a edit list * int) option

let rec first_match rules view i =
  match rules with
  | [] -> None
  | r :: rest -> match r view i with
    | Some _ as res -> res
    | None -> first_match rest view i

let scan_once ~rules arr =
  let n = Array.length arr in
  let payload = Array.map arr ~f:Insn.insn in
  let deleted = Bitset.create ~capacity:n () in
  let clean = ref true in
  let i = ref 0 in
  while !i < n do
    match first_match rules payload !i with
    | None -> incr i
    | Some (edits, next) ->
      clean := false;
      List.iter (edits : _ edit list) ~f:(function
          | Rewrite (j, x) -> payload.!(j) <- x
          | Delete j -> Bitset.add deleted j);
      i := Int.max next (!i + 1)
  done;
  if !clean then None else
    let first = ref (-1) in
    let total = ref 0 in
    for i = 0 to n - 1 do
      if not (Bitset.mem deleted i) then begin
        if !first < 0 then first := i;
        incr total
      end
    done;
    if !first < 0 || !total < 1 then Some [||] else
      let insn i = Insn.with_insn arr.!(i) payload.!(i) in
      let out = Array.create ~len:!total @@ insn !first in
      let cursor = ref 1 in
      for i = !first + 1 to n - 1 do
        if not (Bitset.mem deleted i) then begin
          let c = !cursor in
          out.!(c) <- insn i;
          cursor := c + 1
        end
      done;
      Some out

let run_blk ~rules changed b =
  let arr = Blk.insns b |> Sequence.to_array in
  if Array.is_empty arr then b else
    let rec loop arr any fuel = match scan_once ~rules arr with
      | Some arr' when fuel <= 0 -> Some arr'
      | Some arr' -> loop arr' true (fuel - 1)
      | None when any -> Some arr
      | None -> None in
    match loop arr false (Array.length arr) with
    | None -> b
    | Some arr' ->
      changed := true;
      Blk.with_insns b (Array.to_list arr')

let run ~changed ~rules fn = Func.map_blks fn ~f:(run_blk ~rules changed)
