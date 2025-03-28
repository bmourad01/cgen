open Core

module Make(M : Machine_intf.S) = struct
  module Rv = M.Regvar

  (* Enforce the invariant that the scratch register for each
     class may not appear in the allocatable registers. *)
  let () =
    List.iter M.Reg.allocatable ~f:(fun r ->
        assert (not M.Reg.(equal r scratch));
        assert (not M.Reg.(equal r sp));
        assert (not M.Reg.(equal r fp));
        match M.Reg.classof r with
        | `fp -> assert false
        | `gpr -> ());
    List.iter M.Reg.allocatable_fp ~f:(fun r ->
        assert (not M.Reg.(equal r scratch_fp));
        match M.Reg.classof r with
        | `gpr -> assert false
        | `fp -> ())

  let classof rv = match Rv.which rv with
    | First r -> M.Reg.classof r
    | Second (_, k) -> k

  let same_class k k' = match k, k' with
    | `gpr, `gpr -> true
    | `fp, `fp -> true
    | _ -> false

  let same_class_node a b = same_class (classof a) (classof b)

  let allocatable = Array.of_list M.Reg.(scratch :: allocatable)
  let allocatable_fp = Array.of_list M.Reg.(scratch_fp :: allocatable_fp)

  let kallocatable = Array.length allocatable
  let kallocatable_fp = Array.length allocatable_fp

  let prealloc =
    let t = Hashtbl.create (module M.Reg) in
    Array.iteri allocatable ~f:(fun i r ->
        Hashtbl.add_exn t ~key:r ~data:i);
    t

  let prealloc_fp =
    let t = Hashtbl.create (module M.Reg) in
    Array.iteri allocatable_fp ~f:(fun i r ->
        Hashtbl.add_exn t ~key:r ~data:i);
    t

  let () = assert (Hashtbl.find_exn prealloc M.Reg.scratch = 0)
  let () = assert (Hashtbl.find_exn prealloc_fp M.Reg.scratch_fp = 0)
  let scratch_inv_mask = Z.(~!one)

  let reg_color r =
    let tbl = match M.Reg.classof r with
      | `gpr -> prealloc
      | `fp -> prealloc_fp in
    Hashtbl.find tbl r

  (* The number of allocatable registers for a given register class. *)
  let class_k = function
    | `gpr -> kallocatable
    | `fp -> kallocatable_fp

  (* Choose K based on the register class. `initial` should
     not contain pre-colored nodes. *)
  let node_k n = class_k @@ classof n
end
