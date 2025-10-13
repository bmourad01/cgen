(* Adapted from the paper "Efficient E-matching for SMT Solvers (2007)"
   by L. de Moura and N. Bjørner *)

open Core

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

  let rec permute_commutative = function
    | V _ as v -> [v]
    | P (_, []) as p -> [p]
    | P (f, [a; b]) when is_commutative f ->
      (* Assume that all commutative ops are binary, this way
         we can specialize. *)
      let pa = permute_commutative a in
      let pb = permute_commutative b in
      List.bind pa ~f:(fun a' ->
          List.bind pb ~f:(fun b' ->
              if equal_pat a' b'
              then [P (f, [a'; b'])]
              else [P (f, [a'; b']); P (f, [b'; a'])]))
    | P (f, args) ->
      List.rev_map args ~f:permute_commutative |>
      List.fold ~init:[[]] ~f:(fun acc xs ->
          List.bind xs ~f:(fun x ->
              List.map acc ~f:(List.cons x))) |>
      List.map ~f:(fun args' -> P (f, args'))

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

  let (+$) r i = {reg = r.reg + i} [@@inline]

  (* Program label *)
  type label = {
    label : int;
  } [@@unboxed] [@@deriving compare, equal, hash, sexp]

  let (+@) l i = {label = l.label + i} [@@inline]

  let nil = {label = -1}

  let pp_reg ppf {reg} = Format.fprintf ppf "$%d" reg
  let pp_label ppf {label} = Format.fprintf ppf "@%d" label

  (* A VM instruction. *)
  type insn =
    (* Start at a new root. This will not be handled in the
       VM directly, but instead used to initialize the state
       of the machine for a new term. *)
    | Init of {
        f : op;
        mutable next : (label [@hash.ignore] [@compare.ignore]);
      }
    (* Match `i` with operator `f`, and if successful, bind its
       arguments starting at `o` before continuing to `next`. *)
    | Bind of {
        i : reg;
        f : op;
        o : reg;
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
        regs : reg Map.M(String).t;
        rule : int;
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
    | Init i -> One i.next
    | Bind b -> One b.next
    | Check c -> One c.next
    | Compare c -> One c.next
    | Choose {alt = None; next} -> One next
    | Choose {alt = Some a; next} -> Two (a, next)
    | Yield _ -> Zero

  module Insn = struct
    type t = insn [@@deriving compare, hash, sexp]
    let init f = Init {f; next = nil}
    let bind i f o = Bind {i; f; o; next = nil}
    let check i t = Check {i; t; next = nil}
    let compare_ i j = Compare {i; j; next = nil}
    let yield regs rule = Yield {regs; rule}
  end

  let pp_insn ppf = function
    | Init i ->
      Format.fprintf ppf "init(%a, %a)" pp_op i.f pp_label i.next
    | Bind b ->
      Format.fprintf ppf "bind(%a, %a, %a, %a)"
        pp_reg b.i pp_op b.f pp_reg b.o pp_label b.next
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
        (Map.to_alist y.regs) y.rule

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
    (* Choose one of a set of [alts]. The [memo] table
       is here to cache previous results locally. *)
    | Br of {
        alts : tree Vec.t;
        mutable memo : memo;
      }

  and memo =
    | M0
    | M1 of {
        insn : insn;
        tree : tree;
      }
    | M2 of {
        insn1 : insn;
        tree1 : tree;
        insn2 : insn;
        tree2 : tree;
      }
    | M3 of {
        insn1 : insn;
        tree1 : tree;
        insn2 : insn;
        tree2 : tree;
        insn3 : insn;
        tree3 : tree;
      }
    | MN of (insn, tree) Hashtbl.t

  (* Look up the memoized entry. *)
  let memo_lookup m k ~has ~nil = match k with
    | Yield _ -> nil ()
    | _ -> match m with
      | M1 m when compatible m.insn  k -> has m.tree
      | M2 m when compatible m.insn1 k -> has m.tree1
      | M2 m when compatible m.insn2 k -> has m.tree2
      | M3 m when compatible m.insn1 k -> has m.tree1
      | M3 m when compatible m.insn2 k -> has m.tree2
      | M3 m when compatible m.insn3 k -> has m.tree3
      | MN t ->
        begin match Hashtbl.find t k with
          | Some t -> has t
          | None -> nil ()
        end
      | _ -> nil ()
  [@@specialise]

  (* Assuming that `k` is not present in `m`, compute a new `m`
     with `k` and `v` associated. *)
  let memo_set_assuming_not_present m k v = match k with
    | Yield _ -> m
    | _ -> match m with
      | M0 -> M1 {insn = k; tree = v}
      | M1 m ->
        M2 {
          insn1 = m.insn;
          tree1 = m.tree;
          insn2 = k;
          tree2 = v;
        }
      | M2 m ->
        M3 {
          insn1 = m.insn1;
          tree1 = m.tree1;
          insn2 = m.insn2;
          tree2 = m.tree2;
          insn3 = k;
          tree3 = v;
        }
      | M3 m ->
        let t = Hashtbl.create (module Insn) in
        Hashtbl.set t ~key:m.insn1 ~data:m.tree1;
        Hashtbl.set t ~key:m.insn2 ~data:m.tree2;
        Hashtbl.set t ~key:m.insn3 ~data:m.tree3;
        Hashtbl.set t ~key:k ~data:v;
        MN t
      | MN t ->
        Hashtbl.set t ~key:k ~data:v;
        m

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
      Vec.push v t;
      Vec.push v t';
      Br {alts = v; memo = M0}
  end

  type 'a program = {
    rule : (pat * 'a) array;
    code : insn Vec.t;
    root : (op, label) Hashtbl.t;
    rmin : int array;
  }

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
        (* Pop from the worklist. *)
        match Queue.dequeue w with
        | None ->
          (* Worklist is empty. Yield the registers. *)
          [Insn.yield v rule]
        | Some (i, p) ->
          match p with
          | P (t, []) ->
            (* Ground term. *)
            Insn.check {reg = i} t :: go v o
          | P (f, args) ->
            (* Bind each argument to a new register and
               continue. *)
            let o' = enqueue_children w args o in
            Insn.bind {reg = i} f {reg = o} :: go v o'
          | V x ->
            match Map.find v x with
            | Some j ->
              (* Recurrence of variable, emit a comparison
                 to verify that they point to the same term. *)
              Insn.compare_ {reg = i} j :: go v o
            | None ->
              (* New variable, continue processing. *)
              go (Map.set v ~key:x ~data:{reg = i}) o in
      go String.Map.empty o

    let compile_one_rule rule = function
      | P (f, args) ->
        let w = Queue.create ~capacity:7 () in
        let o = enqueue_children w args 1 in
        Insn.init f :: compile_pat ~rule w o
      | V x ->
        failwithf
          "compile_one_rule: in rule %d, variable ?%s is at the toplevel"
          rule x ()

    (* Create a tree from a sequence of instructions. *)
    let[@tail_mod_cons] rec sequentialize = function
      | [] -> failwith "sequentialize: empty"
      | [i] -> Tree.leaf i
      | insn :: rest ->
        (* NB: we have to mention the constructor directly in order
           to take advantage of `tail_mod_cons`. *)
        Seq {insn; next = sequentialize rest}

    (* Insert a sequence of instructions into an existing tree.

       This is intended to enable sharing of subtrees, which can
       reduce both the final code size and the cost of backtracking
       during execution.
    *)
    let rec insert p t = match p, t with
      | [], t ->
        (* Reached the end of the rule. Return the existing tree. *)
        t
      | _ :: _, Leaf _ ->
        (* Existing leaf: no continuation to descend. *)
        Tree.br t @@ sequentialize p
      | insn :: rest, Seq s when compatible insn s.insn ->
        (* Shared prefix: continue downward. *)
        let n = insert rest s.next in
        if not (phys_equal n s.next) then s.next <- n;
        t
      | _ :: _, Seq _ ->
        (* Divergence: branch here. *)
        Tree.br t @@ sequentialize p
      | insn :: rest, Br b ->
        memo_lookup b.memo insn
          ~nil:(fun () ->
              let m = merge_alt p b.alts b.memo in
              if not (phys_equal m b.memo) then b.memo <- m)
          ~has:(function
              | Leaf _ | Br _ -> assert false
              | Seq s ->
                (* We know that the prefix matches at this alternative,
                   so the root of this subtree should not change. *)
                assert (compatible insn s.insn);
                let n = insert rest s.next in
                if not (phys_equal n s.next) then s.next <- n);
        t

    (* Try to merge the subsequence `p` into one of the `alts` of
       a branch.

       pre: `hd p` is not a member of `memo`
    *)
    and merge_alt p alts memo = match p with
      | [] -> failwith "merge_alt: empty sequence"
      | key :: rest ->
        (* Use first-fit ordering semantics like the paper. We inline
           the prefix check once to see if we can avoid allocating
           a subtree that would be discarded anyway. *)
        Vec.find alts ~f:(function
            | Leaf _ -> false
            | Seq s when not (compatible s.insn key) -> false
            | Seq s ->
              let n = insert rest s.next in
              if not (phys_equal n s.next) then s.next <- n;
              true
            | Br _ ->
              (* We should never end up with a tree structure like this. *)
              assert false) |> function
        | Some _ when Vec.length alts <= branching_factor ->
          (* We have a hit, but not enough alternatives to make caching
             worth it over scanning linearly. *)
          memo
        | Some a ->
          (* Worth caching now. *)
          memo_set_assuming_not_present memo key a
        | None ->
          (* If no match was found, we need to insert a new alternative. *)
          let a = sequentialize p in
          Vec.push alts a;
          memo

    let emit code i =
      let label = Vec.length code in
      Vec.push code i;
      {label}

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
          let n = Vec.length b.alts in
          assert (n > 0);
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
    let compute_rmin code =
      let rmin = Array.create ~len:(Vec.length code) Int.max_value in
      (* Assuming the code is laid out topologically in `linearize`,
         we can do an O(n) backwards traversal to compute the minimum
         rule ID for each instruction. *)
      Vec.iteri_rev code ~f:(fun i -> function
          | Yield y -> rmin.(i) <- y.rule
          | insn ->
            rmin.(i) <- match succs_of_insn insn with
              | Zero ->
                (* The only case where we have no successors is a
                   `Yield`, which we covered above. *)
                assert false
              | One s ->
                assert (i < s.label);
                rmin.(s.label)
              | Two (s1, s2) ->
                assert (i < s1.label);
                assert (i < s2.label);
                Int.min rmin.(s1.label) rmin.(s2.label));
      rmin

    let compile_tree forest i pat =
      match compile_one_rule i pat with
      | (Init i :: _) as p ->
        (* Trees that share the same root can be merged together. *)
        Hashtbl.update forest i.f ~f:(function
            | Some t -> insert p t
            | None -> sequentialize p)
      | _ :: _ ->
        failwithf "compile_tree: invalid root at rule %d" i ()
      | [] ->
        failwithf "compile_tree: empty sequence at rule %d" i ()

    let compile ?(commute = false) rules =
      let rule = Array.of_list rules in
      let code = Vec.create () in
      let root = Hashtbl.create (module Op) in
      let rmin = match rules with
        | [] -> [||]
        | _ ->
          let forest = Hashtbl.create (module Op) in
          if commute then
            Array.iteri rule ~f:(fun i (pat, _) ->
                permute_commutative pat |>
                List.iter ~f:(compile_tree forest i))
          else
            Array.iteri rule ~f:(fun i (pat, _) ->
                compile_tree forest i pat);
          Hashtbl.iteri forest ~f:(fun ~key ~data ->
              let data = linearize code data in
              Hashtbl.set root ~key ~data);
          compute_rmin code in
      {rule; code; root; rmin}
  end

  let compile = Compiler.compile

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

    type regs = id Option_array.t

    type frame = {
      pc : label;
      regs : regs;
      rule : int;
    }

    let frame_order f1 f2 =
      match Int.compare f1.rule f2.rule with
      | 0 -> compare_label f1.pc f2.pc
      | n -> n

    type state = {
      mutable pc : label;
      mutable regs : regs;
      mutable lookup : id -> term;
      cont : frame Pairing_heap.t;
    }

    let default_lookup _ =
      failwith "VM: term lookup is uninitialized"

    let create ?(registers = 10) () = {
      pc = nil;
      lookup = default_lookup;
      regs = Option_array.create ~len:(max 2 registers);
      cont = Pairing_heap.create ~cmp:frame_order ();
    }

    let snapshot_regs st = Option_array.copy st.regs

    let reset st =
      st.pc <- nil;
      st.lookup <- default_lookup;
      Option_array.clear st.regs;
      Pairing_heap.clear st.cont

    let push_frame prog st pc =
      Pairing_heap.add st.cont {
        pc;
        regs = snapshot_regs st;
        rule = prog.rmin.(pc.label);
      }

    let backtrack st = match Pairing_heap.pop st.cont with
      | None ->
        reset st;
        raise_notrace Finished
      | Some f ->
        st.regs <- f.regs;
        st.pc <- f.pc

    let (.$[]) st r = match Option_array.get st.regs r.reg with
      | None -> failwithf "VM: register $%d is uninitialized" r.reg ()
      | Some t -> t

    let root st = st.$[r0]

    let (.$[]<-) st r x =
      Option_array.set_some st.regs r.reg x

    let ensure_regs st need =
      let n = need + 1 in
      let current_len = Option_array.length st.regs in
      if current_len < n then
        let new_len = max n (2 * current_len + 1) in
        let bigger = Option_array.create ~len:new_len in
        Option_array.blit
          ~src:st.regs ~src_pos:0
          ~dst:bigger ~dst_pos:0
          ~len:current_len;
        st.regs <- bigger

    let load_args st r t =
      let args = term_args t in
      let len = List.length args in
      if len > 0 then begin
        ensure_regs st (r.reg + len);
        List.iteri args ~f:(fun i t -> st.$[r +$ i] <- t)
      end;
      len

    let bind st o t next =
      ignore @@ load_args st o t;
      st.pc <- next

    (* Extract the term that `id` represents, handling chains
       of unions along the way. *)
    let rec normalize_term st prog r id =
      let t = st.lookup id in
      match term_union t with
      | None -> t
      | Some (pre, post) ->
        (* Bookmark the `pre` term for exploration. *)
        let regs' = snapshot_regs st in
        Option_array.set_some regs' r.reg pre;
        Pairing_heap.add st.cont {
          pc = st.pc;
          regs = regs';
          rule = prog.rmin.(st.pc.label);
        };
        (* Explore the `post` term, although it may be
           a union itself, so we need to recurse. *)
        normalize_term st prog r post

    type 'a result =
      | Continue
      | Yield of 'a yield

    let step st prog =
      if equal_label st.pc nil then
        raise_notrace Finished;
      match Vec.get_exn prog.code st.pc.label with
      | Init _ ->
        (* NB: this should be done manually at the toplevel *)
        assert false
      | Bind b ->
        let t = normalize_term st prog b.i st.$[b.i] in
        if term_equal_op t b.f
        then bind st b.o t b.next
        else backtrack st;
        Continue
      | Check c ->
        let t = normalize_term st prog c.i st.$[c.i] in
        if is_ground_term t && term_equal_op t c.t
        then st.pc <- c.next
        else backtrack st;
        Continue
      | Choose c ->
        Option.iter c.alt ~f:(push_frame prog st);
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
        let subst = Map.map y.regs ~f:(fun r -> st.$[r]) in
        let pat, payload = prog.rule.(y.rule) in
        Yield {subst; payload; rule = y.rule; pat}

    let (let-) x f = match x with
      | Some y -> f y
      | None -> false

    let init ~lookup st prog id =
      let t = lookup id in
      let- op = term_op t in
      let- r = Hashtbl.find prog.root op in
      match Vec.get_exn prog.code r.label with
      | Init i ->
        assert (equal_op op i.f);
        st.pc <- i.next;
        st.lookup <- lookup;
        st.$[r0] <- id;
        let n = load_args st {reg = 1} t in
        for i = n + 1 to Option_array.length st.regs - 1 do
          Option_array.set_none st.regs i;
        done;
        Pairing_heap.clear st.cont;
        true
      | _ -> assert false

    let many ?(limit = Int.max_value) st prog =
      let result = ref [] in
      let count = ref 0 in
      let continue = ref true in
      while !continue && !count < limit do
        try match step st prog with
          | Continue -> ()
          | Yield y ->
            result := y :: !result;
            incr count;
            backtrack st
        with Finished -> continue := false
      done;
      List.rev !result

    let one st prog =
      match many ~limit:1 st prog with
      | [] -> None
      | [y] -> Some y
      | _ -> assert false
  end
end
