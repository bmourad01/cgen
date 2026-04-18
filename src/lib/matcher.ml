(* Adapted from the paper "Efficient E-matching for SMT Solvers (2007)"
   by L. de Moura and N. Bjørner *)

open Core

module OA = Option_array

(* At minimum, we'll have a branching factor of 2,
   but in cases where there is a large amount of
   sharing it can be in the hundreds. My initial
   analysis shows that 4 is the average for the
   kinds of rulesets we're going to be running with. *)
let branching_factor = 4

module type L = sig
  type op [@@deriving compare, equal, hash, sexp]
  type term
  type id [@@deriving equal]

  val is_commutative : op -> bool

  val term_op : term -> op option
  val term_args : term -> id list
  val term_union : term -> (id * id) option

  val pp_id : Format.formatter -> id -> unit
  val pp_op : Format.formatter -> op -> unit
end

let (let@) f x = f x

module Make(M : L) = struct
  open M

  let is_ground_term t = List.is_empty @@ term_args t

  let term_equal_op t op = match term_op t with
    | Some op' -> equal_op op op'
    | None -> false

  module Op = struct
    type t = op [@@deriving compare, equal, hash, sexp]
  end

  (* A pattern *)
  type pat =
    | V of string
    | P of op * pat list
  [@@deriving compare, equal, hash, sexp]

  (* Enumerate all permutations of commutative subterms in `pat`,
     calling `f` once per permutation. *)
  let iter_permutations pat ~f =
    let rec go pat k = match pat with
      | V _ -> k pat
      | P (_, []) -> k pat
      | P (op, [a; b]) when is_commutative op ->
        let@ a' = go a in
        let@ b' = go b in
        k (P (op, [a'; b']));
        if not (equal_pat a' b') then
          k (P (op, [b'; a']))
      | P (op, args) ->
        let rec walk acc = function
          | [] -> k (P (op, List.rev acc))
          | arg :: rest ->
            let@ arg' = go arg in
            walk (arg' :: acc) rest in
        walk [] args in
    go pat f
  [@@specialise]

  let rec pp_pat ppf = function
    | V x -> Format.fprintf ppf "?%s" x
    | P (op, []) -> Format.fprintf ppf "%a" pp_op op
    | P (op, ps) ->
      let pp_sep ppf () = Format.fprintf ppf " " in
      Format.fprintf ppf "(%a %a)"
        pp_op op
        (Format.pp_print_list ~pp_sep pp_pat)
        ps

  (* VM register *)
  type reg = {
    reg : int
  } [@@unboxed] [@@deriving compare, equal, hash, sexp]

  let r0 = {reg = 0}

  let (+$) r i = {reg = r.reg + i} [@@inline] [@@ocaml.warning "-32"]

  (* Program label *)
  type label = {
    label : int;
  } [@@unboxed] [@@deriving compare, equal, hash, sexp]

  let (+@) l i = {label = l.label + i} [@@inline]

  let nil = {label = -1}

  let pp_reg ppf {reg} = Format.fprintf ppf "$%d" reg
  let pp_label ppf {label} = Format.fprintf ppf "@%d" label

  (* Environment mapping pattern variables to VM registers. *)
  module Varenv = struct
    (* These environments are typically very small, so we can
       get away with using an association list. *)
    type t =
      | Nil
      | Var of string * reg * t
    [@@deriving compare, hash, sexp]

    let empty = Nil

    let rec find env x = match env with
      | Nil -> None
      | Var (y, r, _) when String.(x = y) -> Some r
      | Var (_, _, env) -> find env x

    let add env x r = Var (x, r, env)

    let to_subst env ~lookup =
      let rec go m = function
        | Nil -> m
        | Var (x, r, env) ->
          go (Map.add_exn m ~key:x ~data:(lookup r)) env in
      go String.Map.empty env

    let[@tail_mod_cons] rec to_list = function
      | Nil -> []
      | Var (x, r, env) -> (x, r) :: to_list env
  end

  type varenv = Varenv.t [@@deriving compare, hash, sexp]

  (* A VM instruction. *)
  type insn =
    (* Start at a new root. This will not be handled in the
       VM directly, but instead used to initialize the state
       of the machine for a new term. *)
    | Init of {
        f : op;
        nargs : int;
        mutable next : (label [@hash.ignore] [@compare.ignore]);
      }
    (* Match `i` with operator `f`, and if successful, bind its
       arguments starting at `o` before continuing to `next`. *)
    | Bind of {
        i : reg;
        f : op;
        o : reg;
        nargs : int;
        mutable next : (label [@hash.ignore] [@compare.ignore]);
      }
    (* Same as `Bind`, but specialized to ground terms. *)
    | Check of {
        i : reg;
        t : op;
        mutable next : (label [@hash.ignore] [@compare.ignore]);
      }
    (* Check that `i` and `j` unify to the same term, and if
       successful, continue to `next`. *)
    | Compare of {
        i : reg;
        j : reg;
        mutable next : (label [@hash.ignore] [@compare.ignore]);
      }
    (* Save `alt` as a backtracking point (if available), and
       continue to next. *)
    | Choose of {
        mutable alt : (label option [@hash.ignore] [@compare.ignore]);
        mutable next : (label [@hash.ignore] [@compare.ignore]);
      }
    (* Yield a successful match; `regs` will be used to build
       the resulting substitution. *)
    | Yield of {
        rule : int;
        regs : varenv;
      }
  [@@deriving compare, hash, sexp]

  (* We have to ignore the mutable fields for `compare` anyway,
     so it ends up being the same as the `compatible` relation. *)
  let compatible a b = compare_insn a b = 0

  type succs =
    | Zero
    | One of label
    | Two of label * label

  let succs_of_insn = function
    | Init i  -> One i.next
    | Bind b  -> One b.next
    | Check c -> One c.next
    | Compare c -> One c.next
    | Choose {alt = None; next} -> One next
    | Choose {alt = Some a; next} -> Two (a, next)
    | Yield _ -> Zero

  module Insn = struct
    type t = insn [@@deriving compare, hash, sexp]
    let init f nargs = Init {f; nargs; next = nil}
    let bind i f o nargs = Bind {i; f; o; nargs; next = nil}
    let check i t = Check {i; t; next = nil}
    let compare_ i j = Compare {i; j; next = nil}
    let yield regs rule = Yield {regs; rule}
  end

  let pp_insn ppf = function
    | Init i ->
      Format.fprintf ppf "init(%a, nargs=%d, %a)" pp_op i.f i.nargs pp_label i.next
    | Bind b ->
      Format.fprintf ppf "bind(%a, %a, %a, nargs=%d, %a)"
        pp_reg b.i pp_op b.f pp_reg b.o b.nargs pp_label b.next
    | Check c ->
      Format.fprintf ppf "check(%a, %a, %a)"
        pp_reg c.i pp_op c.t pp_label c.next
    | Compare c ->
      Format.fprintf ppf "compare(%a, %a, %a)"
        pp_reg c.i pp_reg c.j pp_label c.next
    | Choose {alt = None; next} ->
      Format.fprintf ppf "choose(nil, %a)" pp_label next
    | Choose {alt = Some a; next} ->
      Format.fprintf ppf "choose(%a, %a)"
        pp_label a pp_label next
    | Yield y ->
      Format.fprintf ppf "yield(%a) ; rule %d"
        (Format.pp_print_list
           (fun ppf (x, r) -> Format.fprintf ppf "%a:?%s" pp_reg r x)
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ", "))
        (Varenv.to_list y.regs) y.rule

  (* A tree of code sequences. *)
  type tree =
    (* The end of a code sequence. This should always
       be a [Yield] in practice. *)
    | Leaf of insn
    (* Execute [insn] and proceed to the [next] tree. *)
    | Seq of {
        insn : insn;
        mutable next : tree;
      }
    (* Choose one of a set of [alts]. *)
    | Br of {
        alts  : tree Vec.t;
        index : (insn, int) Hashtbl.t;
      }

  let rec sexp_of_tree : tree -> Sexp.t = function
    | Leaf l -> List [Atom "Leaf"; sexp_of_insn l]
    | Seq s ->
      List [
        Atom "Seq";
        List [
          Atom "insn";
          sexp_of_insn s.insn;
        ];
        List [
          Atom "next";
          sexp_of_tree s.next;
        ];
      ]
    | Br b ->
      List [
        Atom "Br";
        List [
          Atom "alts";
          List (List.map ~f:sexp_of_tree @@ Vec.to_list b.alts);
        ];
      ]

  let pp_tree ppf t =
    Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_tree t
  [@@ocaml.warning "-32"]

  module Tree = struct
    let leaf insn = Leaf insn
    let seq insn next = Seq {insn; next} [@@ocaml.warning "-32"]

    let br t t' =
      let v = Vec.create ~capacity:branching_factor () in
      let index = Hashtbl.create (module Insn) ~size:branching_factor in
      let[@inline] init_index i = function
        | Seq s -> Hashtbl.set index ~key:s.insn ~data:i
        | _ -> () in
      Vec.push v t;
      Vec.push v t';
      init_index 0 t;
      init_index 1 t';
      Br {alts = v; index}
  end

  type 'a program = {
    name : string;                (* Name of the ruleset *)
    rule : (pat * 'a) array;      (* Map rule IDs to their payloads *)
    code : insn Vec.t;            (* The compiled VM program *)
    root : (op, label) Hashtbl.t; (* Entry points; each is a root in the forest *)
    prio : int array;             (* Backtracking priority: this is in rule ID order *)
    maxd : int;                   (* Maximum possible continuations that can be live *)
    maxr : int;                   (* Maximum needed size of the register file *)
  }

  let name p = p.name

  let pp_program ppf p = Vec.iteri p.code ~f:(fun l i ->
      Format.fprintf ppf "@%d: %a\n" l pp_insn i)

  module Compiler = struct
    let enqueue_children w cs o =
      List.fold cs ~init:o ~f:(fun o a ->
          Queue.enqueue w (o, a);
          o + 1)

    (* [v]: a mapping from substitution variables to registers

       [w]: the current worklist of subpatterns, keyed by their
       corresponding register

       [o]: the next free register

       [rule]: the ordinal for the rule
    *)
    let compile_pat ~rule w o =
      let[@tail_mod_cons] rec go v o =
        match Queue.dequeue w with
        | None ->
          (* Worklist is empty. Yield the registers. *)
          Tree.leaf @@ Insn.yield v rule
        | Some (i, p) ->
          match p with
          | P (t, []) ->
            (* Ground term. *)
            Seq {
              insn = Insn.check {reg = i} t;
              next = go v o;
            }
          | P (f, args) ->
            (* Bind each argument to a new register and
               continue. *)
            let nargs = List.length args in
            let o' = enqueue_children w args o in
            Seq {
              insn = Insn.bind {reg = i} f {reg = o} nargs;
              next = go v o';
            }
          | V x ->
            match Varenv.find v x with
            | Some j ->
              (* Recurrence of variable, emit a comparison
                 to verify that they point to the same term. *)
              Seq {
                insn = Insn.compare_ {reg = i} j;
                next = go v o;
              }
            | None ->
              (* New variable, continue processing. *)
              go (Varenv.add v x {reg = i}) o in
      go Varenv.empty o

    let compile_one_rule w rule = function
      | P (f, args) ->
        let nargs = List.length args in
        let o = enqueue_children w args 1 in
        Seq {
          insn = Insn.init f nargs;
          next = compile_pat ~rule w o;
        }
      | V x ->
        failwithf
          "compile_one_rule: in rule %d, variable ?%s is at the toplevel"
          rule x ()

    (* Insert a sequence of instructions into an existing tree.

       This is intended to enable sharing of subtrees, which can
       reduce both the final code size and the cost of backtracking
       during execution.
    *)
    let rec insert p t = match p, t with
      | Leaf (Yield _ as y), Br b ->
        Vec.push b.alts @@ Tree.leaf y;
        t
      | Leaf (Yield _ as y), _ ->
        Tree.br t @@ Tree.leaf y
      | Leaf _, _ -> assert false
      | Seq {insn = Yield _; _}, _ -> assert false
      | Seq _, Leaf _ ->
        (* Existing leaf (a Yield): new pattern diverges. *)
        Tree.br t p
      | Seq {insn; next}, Seq s when compatible insn s.insn ->
        (* Shared prefix: continue downward. *)
        let n = insert next s.next in
        if not (phys_equal n s.next) then s.next <- n;
        t
      | Seq _, Seq _ ->
        (* Divergence: branch here. *)
        Tree.br t p
      | Seq {insn; next}, Br b ->
        merge_alt insn next b.alts b.index;
        t
      | Br _, _ -> assert false

    (* Try to merge the subsequence `p` into one of the `alts`
       of a branch. *)
    and merge_alt key rest alts index =
      match Hashtbl.find index key with
      | None ->
        let i = Vec.length alts in
        Vec.push alts @@ Seq {insn = key; next = rest};
        Hashtbl.set index ~key ~data:i
      | Some i -> match Vec.get_exn alts i with
        | Seq s ->
          let n = insert rest s.next in
          if not (phys_equal n s.next) then s.next <- n
        | _ -> assert false

    let emit code i =
      let label = Vec.length code in
      Vec.push code i;
      {label}
    [@@inline]

    let emit_choice code =
      emit code @@ Choose {alt = None; next = nil}
    [@@inline]

    let patch_next_at code i next =
      match Vec.get_exn code i.label with
      | Init i -> i.next <- next
      | Bind b -> b.next <- next
      | Check c -> c.next <- next
      | Compare c -> c.next <- next
      | Choose c -> c.next <- next
      | Yield _ -> assert false

    let patch_choose_alt_at code i alt =
      match Vec.get_exn code i.label with
      | Choose c -> c.alt <- Some alt
      | _ -> assert false

    let linearize code t =
      let rec go = function
        | Leaf insn -> emit code insn
        | Seq s ->
          let label = emit code s.insn in
          patch_next_at code label @@ go s.next;
          label
        | Br b ->
          (* We should always have at least two alternatives to
             choose from. *)
          let n = Vec.length b.alts in
          assert (n > 1);
          (* Emit a `choose` instruction for each alternative. *)
          let first = emit_choice code in
          for _ = 1 to n - 1 do ignore @@ emit_choice code done;
          Vec.iteri b.alts ~f:(fun i a ->
              (* Emit the body of the alternative and make it the
                 `next` for the corresponding `choose`. *)
              let c = first +@ i in
              patch_next_at code c @@ go a;
              (* Unless this is the last alternative, patch its
                 continuation to be the next `choose` instruction. *)
              if i < n - 1 then patch_choose_alt_at code c (c +@ 1));
          (* Use the first alternative as the label. *)
          first in
      go t

    (* Compute a backtracking priority for each program label.

       In this case, we want `yield` instructions to be visited
       in rule ID (insertion) order when we run the VM.

       We take advantage of the fact that the control-flow graph
       of the program is essentially a forest, so there are no
       back-edges to consider (which means we do not need to
       perform a full iterative worklist analysis).
    *)
    let compute_priority code =
      let prio = Array.create ~len:(Vec.length code) Int.max_value in
      (* Assuming the code is laid out topologically in `linearize`,
         we can do an O(n) backwards traversal to compute the minimum
         rule ID for each instruction. *)
      Vec.iteri_rev code ~f:(fun i -> function
          | Yield y -> prio.(i) <- y.rule
          | insn ->
            prio.(i) <- match succs_of_insn insn with
              | Zero ->
                (* The only case where we have no successors is a
                   `Yield`, which we covered above. *)
                assert false
              | One s ->
                assert (i < s.label);
                prio.(s.label)
              | Two (s1, s2) ->
                assert (i < s1.label);
                assert (i < s2.label);
                Int.min prio.(s1.label) prio.(s2.label));
      prio

    (* Compute the maximum frame stack depth and maximum register file
       size needed by the VM, from the compiled program code alone. *)
    let compute_caps code =
      let n = Vec.length code in
      let depth = Array.create ~len:n 0 in
      Vec.iteri_rev code ~f:(fun i -> function
          | Yield _ -> ()
          | Bind b -> depth.(i) <- depth.(b.next.label)
          | Init t -> depth.(i) <- depth.(t.next.label)
          | Check c -> depth.(i) <- depth.(c.next.label)
          | Compare c -> depth.(i) <- depth.(c.next.label)
          | Choose c ->
            let dn = depth.(c.next.label) in
            let da = match c.alt with
              | Some a -> 1 + depth.(a.label)
              | None -> 0 in
            depth.(i) <- Int.max (1 + dn) da);
      let maxr, maxd =
        Vec.foldi code ~init:(0, 0)
          ~f:(fun i ((r, d) as acc) -> function
              | Init t ->
                let r = Int.max r t.nargs in
                let d = Int.max d depth.(i) in
                r, d
              | Bind b ->
                let r = Int.max r (b.o.reg + b.nargs - 1) in
                r, d
              | _ -> acc) in
      maxd, maxr + 1

    let compile_tree forest w i pat =
      match compile_one_rule w i pat with
      | Seq {insn = Init {f; _}; _} as t ->
        (* Trees that share the same root can be merged together. *)
        Hashtbl.update forest f ~f:(function
            | Some existing -> insert t existing
            | None -> t)
      | _ ->
        failwithf "compile_tree: invalid root at rule %d" i ()

    let compile ?(commute = false) ~name rules =
      let[@alert "-deprecated"] t0 = Time.now () in
      let rule = Array.of_list rules in
      let code = Vec.create () in
      let w = Queue.create ~capacity:7 () in
      let prio, root, maxd, maxr = match rules with
        | [] -> [||], Hashtbl.create (module Op), 0, 1
        | _ ->
          let forest = Hashtbl.create (module Op) in
          if commute then
            Array.iteri rule ~f:(fun i (pat, _) ->
                iter_permutations pat ~f:(compile_tree forest w i))
          else
            Array.iteri rule ~f:(fun i (pat, _) ->
                compile_tree forest w i pat);
          let root = Hashtbl.map forest ~f:(linearize code) in
          let prio = compute_priority code in
          let depth, regs = compute_caps code in
          prio, root, depth, regs in
      let[@alert "-deprecated"] t = Time.now () in
      let[@alert "-deprecated"] elapsed = Time.(Span.to_sec (diff t t0)) in
      Logs.debug (fun m ->
          m "%s: ruleset %S: compiled %d rules to %d instructions in %g seconds, \
             commute=%b, maxd=%d, maxr=%d%!"
            __FUNCTION__ name (Array.length rule) (Vec.length code)
            elapsed commute maxd maxr);
      {name; rule; code; root; prio; maxd; maxr}
  end

  let compile = Compiler.compile
  let is_empty p = Vec.is_empty p.code

  type subst = id String.Map.t

  type 'a yield = {
    subst : subst;
    payload : 'a;
    rule : int;
    pat : pat;
  }

  let pp_yield_dbg ppn ppf y =
    Format.fprintf ppf "rule %d:\n" y.rule;
    Format.fprintf ppf "pattern: %a\n" pp_pat y.pat;
    if Map.is_empty y.subst then
      Format.fprintf ppf "subst = {}\n"
    else begin
      Format.fprintf ppf "subst = {\n";
      Map.iteri y.subst ~f:(fun ~key:x ~data:id ->
          Format.fprintf ppf "  %s = %a, id %a\n" x ppn id pp_id id);
      Format.fprintf ppf "}\n"
    end

  module Yield = struct
    type 'a t = 'a yield
    let subst y = y.subst
    let payload y = y.payload
    let rule y = y.rule
    let pat y = y.pat
  end

  module VM = struct
    exception Finished

    type regs = id OA.t

    (* A saved execution context for backtracking.

       Each frame holds an independent snapshot of the register file taken
       at push time. On `backtrack`, the snapshot is swapped in as the live
       registers. This correctly handles non-LIFO frame pops (priority-based
       selection) because each frame owns its own state and is independent of
       others.
    *)
    type frame = {
      pc   : label;
      regs : regs;
      maxw : int;
      rule : int;
    }

    let frame_order f1 f2 =
      match Int.compare f1.rule f2.rule with
      | 0 -> compare_label f1.pc f2.pc
      | n -> n

    type 'a state = {
      mutable pc     : label;       (* Current instruction *)
      mutable regs   : regs;        (* Current register file *)
      mutable maxw   : int;         (* Maximum register written *)
      mutable lookup : id -> term;  (* Look up a term using its ID *)
      pool           : regs Vec.t;  (* Spare register files to recycle *)
      cont           : frame Vec.t; (* Queue of saved continuations *)
      prog           : 'a program;  (* The VM program *)
    }

    let default_lookup _ =
      failwith "VM: term lookup is uninitialized"

    let (.![]) v i = Vec.unsafe_get v i
    let (.![]<-) v i x = Vec.unsafe_set v i x

    let create prog = {
      pc = nil;
      lookup = default_lookup;
      regs = OA.create ~len:(max 1 prog.maxr);
      maxw = 0;
      pool = Vec.create ~capacity:prog.maxd ();
      cont = Vec.create ~capacity:prog.maxd ();
      prog;
    }

    (* Pop the highest priority frame.

       The continuation queue is usually very small; on current workloads
       I never saw it grow past 5 elements. We can get better performance
       with a flat vector combined with selection sort.

       This also makes more sense when we consider that the VM can run
       incrementally, and a user might greedily pick the first match, so
       sorting the rest of the queue would be a waste of effort.
    *)
    let pop_frame st =
      let n = Vec.length st.cont in
      if n = 0 then None else
        let mi = ref 0 in
        let last = n - 1 in
        for i = 1 to last do
          if frame_order st.cont.![i] st.cont.![!mi] < 0 then mi := i
        done;
        let f = st.cont.![!mi] in
        if !mi < last then st.cont.![!mi] <- st.cont.![last];
        ignore (Vec.pop_exn st.cont);
        Some f

    (* Save the current register file.

       We're going to look for the most recent pool entry that can fit
       our current needed size. If none exists, we create it.
    *)
    let snapshot_regs st =
      let n = st.maxw + 1 in
      let last = Vec.length st.pool - 1 in
      let i = ref last in
      while !i >= 0 && OA.length st.pool.![!i] < n do decr i done;
      let dst =
        if !i < 0 then OA.create ~len:n else
          let a = st.pool.![!i] in
          if !i < last then st.pool.![!i] <- st.pool.![last];
          ignore (Vec.pop_exn st.pool);
          a in
      OA.unsafe_blit ~src:st.regs ~src_pos:0 ~dst ~dst_pos:0 ~len:n;
      dst

    let reset st =
      st.pc <- nil;
      st.lookup <- default_lookup;
      st.maxw <- 0;
      OA.clear st.regs;
      Vec.iter st.cont ~f:(fun f ->
          if Vec.length st.pool < st.prog.maxd then
            Vec.push st.pool f.regs);
      Vec.clear st.cont

    let push_frame st pc =
      Vec.push st.cont {
        pc;
        regs = snapshot_regs st;
        maxw = st.maxw;
        rule = st.prog.prio.(pc.label);
      }

    let push_union_frame st r id =
      let regs = snapshot_regs st in
      OA.set_some regs r.reg id;
      Vec.push st.cont {
        pc = st.pc;
        regs;
        maxw = st.maxw;
        rule = st.prog.prio.(st.pc.label);
      }

    let backtrack st = match pop_frame st with
      | None ->
        reset st;
        raise_notrace Finished
      | Some f ->
        if Vec.length st.pool < st.prog.maxd then
          Vec.push st.pool st.regs;
        st.regs <- f.regs;
        st.maxw <- f.maxw;
        st.pc <- f.pc

    let (.$[]) st r = match OA.get st.regs r.reg with
      | None -> failwithf "VM: register $%d is uninitialized" r.reg ()
      | Some t -> t

    let root st = st.$[r0] [@@inline]

    let (.$[]<-) st r x =
      OA.set_some st.regs r.reg x;
      if r.reg > st.maxw then st.maxw <- r.reg
    [@@inline]

    let ensure_cap' st cap last =
      if last < cap then cap else
        let new_len = max (last + 1) (2 * cap + 1) in
        let dst = OA.create ~len:new_len in
        OA.unsafe_blit ~src:st.regs ~src_pos:0 ~dst ~dst_pos:0 ~len:cap;
        st.regs <- dst;
        new_len
    [@@inline]

    let ensure_cap st last =
      ignore (ensure_cap' st (OA.length st.regs) last)
    [@@inline]

    let load_args st r t =
      match term_args t with
      | [] -> ()
      | [a] ->
        let i = r.reg in
        ensure_cap st i;
        OA.unsafe_set_some st.regs i a;
        if i > st.maxw then st.maxw <- i
      | [a; b] ->
        let i = r.reg in
        let j = i + 1 in
        ensure_cap st j;
        let regs = st.regs in
        OA.unsafe_set_some regs i a;
        OA.unsafe_set_some regs j b;
        if j > st.maxw then st.maxw <- j
      | [a; b; c] ->
        let i = r.reg in
        let k = i + 2 in
        ensure_cap st k;
        let regs = st.regs in
        OA.unsafe_set_some regs i a;
        OA.unsafe_set_some regs (i + 1) b;
        OA.unsafe_set_some regs k c;
        if k > st.maxw then st.maxw <- k
      | args ->
        let rec loop st cap i = function
          | [] -> i
          | x :: xs ->
            let cap = ensure_cap' st cap i in
            OA.unsafe_set_some st.regs i x;
            loop st cap (i + 1) xs in
        let last = loop st (OA.length st.regs) r.reg args - 1 in
        if last > st.maxw then st.maxw <- last

    let bind st o t next =
      load_args st o t;
      st.pc <- next
    [@@inline]

    (* Extract the term that `id` represents, handling chains
       of unions along the way. *)
    let rec normalize_term st r id =
      let t = st.lookup id in
      match term_union t with
      | None -> t
      | Some (pre, post) ->
        (* Bookmark the `pre` term for exploration. *)
        push_union_frame st r pre;
        (* Explore the `post` term, although it may be
           a union itself, so we need to recurse. *)
        normalize_term st r post

    type 'a step =
      | Continue
      | Yield of 'a yield

    let step st =
      if equal_label st.pc nil then
        raise_notrace Finished;
      match Vec.get_exn st.prog.code st.pc.label with
      | Init _ ->
        (* NB: this should be done manually at the toplevel *)
        assert false
      | Bind b ->
        let t = normalize_term st b.i st.$[b.i] in
        if term_equal_op t b.f
        then bind st b.o t b.next
        else backtrack st;
        Continue
      | Check c ->
        let t = normalize_term st c.i st.$[c.i] in
        if is_ground_term t && term_equal_op t c.t
        then st.pc <- c.next
        else backtrack st;
        Continue
      | Choose c ->
        let () = match c.alt with
          | None -> ()
          | Some alt -> push_frame st alt in
        st.pc <- c.next;
        Continue
      | Compare c ->
        let i = st.$[c.i] in
        let j = st.$[c.j] in
        if equal_id i j
        then st.pc <- c.next
        else backtrack st;
        Continue
      | Yield y ->
        let subst = Varenv.to_subst y.regs ~lookup:(fun r -> st.$[r]) in
        let pat, payload = st.prog.rule.(y.rule) in
        Yield {subst; payload; rule = y.rule; pat}

    let (let-) x f = match x with
      | Some y -> f y
      | None -> false
    [@@inline]

    let init ~lookup st id =
      reset st;
      let t = lookup id in
      let- op = term_op t in
      let- r = Hashtbl.find st.prog.root op in
      match Vec.get_exn st.prog.code r.label with
      | Init i ->
        assert (equal_op op i.f);
        st.pc <- i.next;
        st.lookup <- lookup;
        st.$[r0] <- id;
        load_args st {reg = 1} t;
        true
      | _ -> assert false

    let many ?(limit = Int.max_value) st =
      let result = ref [] in
      let count = ref 0 in
      let () =
        try
          while !count < limit do
            match step st with
            | Continue -> ()
            | Yield y ->
              result := y :: !result;
              incr count;
              backtrack st
          done;
        with Finished -> () in
      List.rev !result

    let one st = match many ~limit:1 st with
      | [] -> None
      | [y] -> Some y
      | _ -> assert false
  end
end
