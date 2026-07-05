open Core
open Virtual

module E = Cgen_utils.Monads.Error
module Lset = Label.Tree_set
module LT = Label.Dense_table
module LS = Label.Dense_set

open E.Let

module Operands = Set.Make(struct
    type t = operand [@@deriving compare, sexp]
  end)

module Phis_lang = struct
  module Ctrl = struct
    type t = ctrl
    let locals = (Phi_values.locals Ctrl.Table.enum :> t -> _)
  end
  module Blk = Blk
  module Func = Func
  module Cfg = Cfg
end

module Phis_domain = struct
  type t = Operands.t [@@deriving equal]
  let one = Operands.singleton
  let join = Set.union
end

module Phis = Phi_values.Make(Phis_lang)(Phis_domain)

module Scc = struct
  module Group = struct
    type t = Lset.t

    let mem = Lset.mem

    let pp ppl ppf t =
      Format.fprintf ppf "{%a}"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ") ppl)
        (Lset.to_list t)
  end

  type t = {
    ids   : int LT.t;
    comps : Group.t array;
  }

  let group scc l =
    LT.find scc.ids l |>
    Option.map ~f:(fun i -> scc.comps.(i))

  let pp ppl ppf scc =
    Format.fprintf ppf "[%a]"
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
         (Group.pp ppl))
      (Array.to_list scc.comps)

  let compute (g : Cfg.t) =
    let index = ref 0 in
    let n = Cfg.number_of_nodes g in
    let idx = LT.create ~capacity:n () in
    let low = LT.create ~capacity:n () in
    let ids = LT.create ~capacity:n () in
    let on_stack = LS.create ~capacity:n () in
    let (.$[]) t k = LT.find_exn t k in
    let (.$[]<-) t k v = LT.set t ~key:k ~data:v in
    let stack = Stack.create () in
    let comps = ref [] in
    let comp_count = ref 0 in
    let rec connect v =
      let i = !index in
      incr index;
      idx.$[v] <- i;
      low.$[v] <- i;
      Stack.push stack v;
      LS.add on_stack v;
      Sequence.iter (Cfg.Node.succs v g) ~f:(fun w ->
          match LT.find idx w with
          | None ->
            connect w;
            let lw = low.$[w] in
            LT.update low v ~f:(function
                | None -> lw
                | Some lv -> Int.min lv lw)
          | Some iw when LS.mem on_stack w ->
            LT.update low v ~f:(function
                | None -> iw
                | Some lv -> Int.min lv iw)
          | Some _ -> ());
      if low.$[v] = idx.$[v] then
        let cid = !comp_count in
        incr comp_count;
        let members = ref Lset.empty in
        let continue = ref true in
        while !continue do
          let w = Stack.pop_exn stack in
          LS.remove on_stack w;
          members := Lset.add !members w;
          ids.$[w] <- cid;
          if Label.(w = v) then continue := false
        done;
        comps := !members :: !comps in
    Sequence.iter (Cfg.nodes g) ~f:(fun v ->
        if not (LT.mem idx v) then connect v);
    {ids; comps = Array.of_list_rev !comps}
end

(* General information about the function we're translating. *)
type t = {
  fn   : func;          (* The function itself. *)
  loop : loops;         (* Loops analysis. *)
  reso : resolver;      (* Labels to blocks/insns. *)
  cfg  : Cfg.t;         (* The CFG. *)
  dom  : Semi_nca.tree; (* Dominator tree. *)
  pdom : Semi_nca.tree; (* Post-dominator tree. *)
  rdom : Dominance.t;   (* Fine-grained dominance relation. *)
  lst  : Last_stores.t; (* Last stores analysis. *)
  tenv : Type_env.t;    (* Typing environment. *)
  phis : Phis.state;    (* Block argument value sets. *)
  scc  : Scc.t;         (* Strongly-connected components. *)
}

let init_dom_relation reso dom =
  let module Dom = Dominance.Make(struct
      type lhs = Var.t option
      type insn = Insn.t
      module Blk = Blk
      let is_descendant_of = Semi_nca.Tree.is_descendant_of dom
      let resolve = Resolver.resolve reso
    end) in
  Dom.dominates

let init_last_stores start cfg reso =
  let module Lst = Last_stores.Make(struct
      module Insn = Insn
      module Blk = Blk
      module Cfg = Cfg
      let resolve l = match Resolver.resolve reso l with
        | Some `insn _ | None -> assert false
        | Some `blk b -> b
    end) in
  Lst.analyze cfg start

let resolve_blk reso l =
  match Resolver.resolve reso l with
  | Some `blk b -> Some b
  | Some _ | None -> None

(* The label of the block that `l` belongs to (whether `l` is a block or
   an instruction label). *)
let resolve_blk_label reso l =
  match Resolver.resolve reso l with
  | Some (`insn (_, b, _, _) | `blk b) -> Blk.label b
  | None -> assert false

let init fn tenv =
  let+ reso = Resolver.create fn in
  let start = Func.entry fn in
  let cfg = Cfg.create fn in
  let dom = Semi_nca.compute cfg Label.pseudoentry in
  let loop = Loops.analyze ~dom ~name:(Func.name fn) cfg in
  let pdom = Semi_nca.compute cfg Label.pseudoexit ~rev:true in
  let rdom = init_dom_relation reso dom in
  let lst = init_last_stores start cfg reso in
  let phis = Phis.analyze ~blk:(resolve_blk reso) cfg in
  let scc = Scc.compute cfg in
  Logs.debug (fun m ->
      m "%s: SCCs of $%s: %a%!"
        __FUNCTION__ (Func.name fn) (Scc.pp Label.pp) scc);
  {fn; loop; reso; cfg; dom; pdom; rdom; lst; tenv; phis; scc}
