open Core

module MR = Machine_regvar

module Make(M : Machine_intf.S) = struct
  module Rv = M.Regvar

  let () =
    List.iter M.Reg.allocatable ~f:(fun r ->
        assert (not M.Reg.(equal r sp));
        assert (not M.Reg.(equal r fp));
        match M.Reg.classof r with
        | FP -> assert false
        | GPR -> ());
    List.iter M.Reg.allocatable_fp ~f:(fun r ->
        match M.Reg.classof r with
        | GPR -> assert false
        | FP -> ())

  let classof rv = match Rv.which rv with
    | First r -> M.Reg.classof r
    | Second (_, k) -> k

  let same_class_node a b = MR.equal_cls (classof a) (classof b)

  let allocatable = Array.of_list M.Reg.allocatable
  let allocatable_fp = Array.of_list M.Reg.allocatable_fp

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

  let reg_color r =
    let tbl = match M.Reg.classof r with
      | GPR -> prealloc
      | FP -> prealloc_fp in
    Hashtbl.find tbl r

  (* The number of allocatable registers for a given register class. *)
  let class_k : MR.cls -> int = function
    | GPR -> kallocatable
    | FP -> kallocatable_fp

  (* Choose K based on the register class. `initial` should
     not contain pre-colored nodes. *)
  let node_k n = class_k @@ classof n
end
