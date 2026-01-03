open Core
open Regular.Std
open Graphlib.Std

let check
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?dom g entry =
  with_return @@ fun {return} ->
  let dom = match dom with
    | None -> Semi_nca.compute (module G) g entry
    | Some dom -> dom in
  let (#>) a b = Semi_nca.Tree.dominates dom a b in
  Graphlib.depth_first_search (module G) g
    ~start:entry ~init:()
    ~start_tree:(fun n () ->
        (* We're only interested in the spanning tree with
           the entry node as the root. *)
        if G.Node.(n <> entry) then return true)
    ~enter_edge:(fun k e () -> match k with
        | `Tree | `Forward | `Cross -> ()
        | `Back ->
          (* For a back edge (u,v), if v dominates u then v
             is a natural loop header. Otherwise, the loop
             has multiple entries and is thus irreducible. *)
          let u, v = G.Edge.(src e, dst e) in
          if not (v #> u) then return false);
  true
