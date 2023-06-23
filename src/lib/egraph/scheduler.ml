open Core
open Regular.Std
open Common

type t = {
  match_limit : int;
  ban_length  : int;
}

let create_exn ?(match_limit = 1000) ?(ban_length = 5) () =
  if match_limit < 1 then invalid_arg "match_limit must be greater than zero";
  if ban_length < 1 then invalid_arg "ban_length must be greater than zero";
  {match_limit; ban_length}

type 'a data = {
  rule                 : 'a rule;
  mutable banned_until : int;
  mutable times_banned : int;
}

let create_data rule = {
  rule;
  banned_until = 0;
  times_banned = 0;
}

let from_rules rules =
  Array.of_list_map rules ~f:create_data |>
  Array.to_sequence_mutable

let threshold t d = t.match_limit lsl d.times_banned

let ban t d =
  (* XXX: a shift could set the MSB, which would give us a negative
     value, or it could overflow to zero. *)
  let b = t.ban_length lsl d.times_banned in
  d.banned_until <- if b <= 0 then Int.max_value else b;
  d.times_banned <- d.times_banned + 1

(* This should be called when no changes are made after a single
   iteration, at which point we check if there are rules that we
   banned from being applied. If so, we should relax their ban
   lengths and try applying them again to see if we will get any
   changes. *)
let should_stop t rules i =
  let banned = Seq.filter rules ~f:(fun d ->
      (* Reject rules that have been banned too many times. *)
      d.times_banned < Sys.int_size_in_bits &&
      (* Also reject rules that will never match. *)
      threshold t d > 0 &&
      d.banned_until > i) in
  Seq.min_elt banned ~compare:(fun a b ->
      compare a.banned_until b.banned_until) |>
  Option.value_map ~default:true ~f:(fun d ->
      let n = d.banned_until - i in
      Seq.iter banned ~f:(fun d ->
          d.banned_until <- d.banned_until - n);
      false)

let check t d i =
  if d.times_banned < Sys.int_size_in_bits
  && i >= d.banned_until then
    (* XXX: can we assume that the result is zero if the shift
       overflows? *)
    let threshold = threshold t d in
    Option.some_if (threshold > 0) threshold
  else None

let guard t d i ~(f : unit -> matches) : matches option =
  check t d i |> Option.bind ~f:(fun threshold ->
      let matches = f () in
      if Vec.length matches > threshold
      then (ban t d; None) else Some matches)
