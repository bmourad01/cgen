(* Adapted from the paper "Efficient E-matching for SMT Solvers (2007)"
   by L. de Moura and N. Bjørner *)

open Core

module type L = sig
  type op [@@deriving compare, equal, hash, sexp]
  type term [@@deriving equal]
  type id [@@deriving equal]

  val is_commutative : op -> bool

  val term_op : term -> op option
  val term_args : term -> id list

  val pp_id : Format.formatter -> id -> unit
  val pp_op : Format.formatter -> op -> unit
end

let rec permutations = function
  | [] -> [[]]
  | x :: xs ->
    permutations xs |> List.bind ~f:(fun ys ->
        List.length ys |> succ |> List.init ~f:(fun i ->
            let l, r = List.split_n ys i in
            l @ (x :: r)))

let rec cartesian_product = function
  | [] -> [[]]
  | xs :: rest ->
    List.bind xs ~f:(fun x ->
        cartesian_product rest |>
        List.map ~f:(List.cons x))

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
  [@@deriving compare, equal, sexp]

  let make_pats f = List.map ~f:(fun args -> P (f, args))
  let dedup_pats = List.dedup_and_sort ~compare:compare_pat

  let rec permute_commutative = function
    | V _ as p -> [p]
    | P (f, args) ->
      let sub = List.map args ~f:permute_commutative in
      let prod = cartesian_product sub in
      if is_commutative f then
        List.bind prod ~f:permutations |>
        make_pats f |> dedup_pats
      else make_pats f prod

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

  let (+$) r i = {reg = r.reg + i}

  (* Program label *)
  type label = {
    label : int;
  } [@@unboxed] [@@deriving compare, equal, hash, sexp]

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
        regs : (reg * string) list;
        rule : int;
      }
  [@@deriving compare, hash, sexp]

  (* We have to ignore the mutable fields for `compare` anyway,
     so it ends up being the same as the `compatible` relation. *)
  let compatible a b = compare_insn a b = 0

  let succs_of_insn = function
    | Init i' -> [i'.next.label]
    | Bind b -> [b.next.label]
    | Check c -> [c.next.label]
    | Compare c -> [c.next.label]
    | Choose {alt = None; next} -> [next.label]
    | Choose {alt = Some a; next} -> [a.label; next.label]
    | Yield _ -> []

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
           (fun ppf (r, x) -> Format.fprintf ppf "%a:?%s" pp_reg r x)
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ", "))
        y.regs y.rule

  (* A tree of code sequences. *)
  type tree =
    (* The end of a code sequence. This should always
       be a [Yield] in practice. *)
    | Leaf of insn
    (* Execute [insn] and proceed to the [next] tree. *)
    | Seq of {
        insn : insn;
        next : tree;
      }
    (* Choose one of a set of [alts]. The [memo] table
       is here to cache previous results locally. *)
    | Br of {
        alts : tree Vec.t;
        memo : (insn, tree * int) Hashtbl.t;
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
    let seq insn next = Seq {insn; next}

    let br alts = Br {
        alts = Vec.of_list alts;
        memo = Hashtbl.create (module Insn);
      }
  end

  type 'a program = {
    rule : (pat * 'a) Vec.t;
    code : insn Vec.t;
    root : (op, label) Hashtbl.t;
    rmin : int array;
  } [@@ocaml.warning "-69"]

  let pp_program ppf p = Vec.iteri p.code ~f:(fun l i ->
      Format.fprintf ppf "@%d: %a\n" l pp_insn i)

  module Compiler = struct
    let enqueue_children ?(w = Int.Map.empty) cs o =
      List.fold cs ~init:(w, o) ~f:(fun (w, o) a ->
          Map.set w ~key:o ~data:a, o + 1)

    let yield_regs v vars =
      List.rev @@ List.filter_map vars ~f:(fun x ->
          Map.find v x |> Option.map ~f:(fun r -> r, x))

    (* Simple heuristic for picking the next pattern.

       The goal is to prioritize patterns that maximize
       discrimination (i.e. the one that is most likely to fail early).
    *)
    let rec depth = function
      | P (_, args) -> 1 + List.sum (module Int) args ~f:depth
      | V _ -> 0

    let pick_one w =
      Map.fold w ~init:None ~f:(fun ~key ~data acc ->
          let d = depth data in
          match acc with
          | Some (_, _, d') when d' >= d -> acc
          | Some _ | None -> Some (key, data, d))

    (* [v]: a mapping from substitution variables to registers

       [vars]: the current substitution variables in last-seen order

       [a]: the payload for the rule

       [rule]: the ordinal for the rule

       [w]: the current worklist of subpatterns, keyed by their
       corresponding register

       [o]: the next free register
    *)
    let compile_pat ~rule w o =
      let[@tail_mod_cons] rec go w v o vars =
        match pick_one w with
        | None ->
          (* Worklist is empty. Yield the registers in first-seen
             variable order. *)
          [Insn.yield (yield_regs v vars) rule]
        | Some (i, p, _) ->
          (* Pop from the worklist. *)
          let w' = Map.remove w i in
          match p with
          | P (t, []) ->
            (* Ground term. *)
            Insn.check {reg = i} t :: go w' v o vars
          | P (f, args) ->
            let wext, o' = enqueue_children ~w:w' args o in
            Insn.bind {reg = i} f {reg = o} :: go wext v o' vars
          | V x ->
            match Map.find v x with
            | Some j -> Insn.compare_ {reg = i} j :: go w' v o vars
            | None ->
              (* We haven't seen this variable before, so push it and
                 continue processing the worklist. *)
              let v' = Map.set v ~key:x ~data:{reg = i} in
              go w' v' o (x :: vars) in
      go w String.Map.empty o []

    let compile_one_rule rule = function
      | P (f, args) ->
        let w, o = enqueue_children args 0 in
        Insn.init f :: compile_pat ~rule w o
      | V x ->
        failwithf
          "compile_one_rule: in rule %d, variable ?%s is at the toplevel"
          rule x ()

    (* Create a tree from a sequence of instructions. *)
    let rec sequentialize = function
      | [] -> failwith "sequentialize: empty"
      | [i] -> Tree.leaf i
      | hd :: tl -> Tree.seq hd @@ sequentialize tl

    (* Insert a sequence of instructions into an existing tree.

       This is intended to enable sharing of subtrees, which can
       reduce both the final code size and the cost of backtracking
       during execution.
    *)
    let rec insert p t = match p, t with
      | [], t ->
        (* Reached the end of the rule. Return the existing tree. *)
        t, false
      | insn :: rest, Seq s ->
        (* Existing sequential node. *)
        if compatible insn s.insn then
          (* Shared prefix: continue downward. *)
          let next, _ = insert rest s.next in
          Seq {s with next}, true
        else
          (* Divergence: branch here. *)
          Tree.br [t; sequentialize p], false
      | insn :: _, Br b ->
        begin match Hashtbl.find b.memo insn with
          | Some (a, i) ->
            let a', changed = insert p a in
            if changed then begin
              Hashtbl.set b.memo ~key:insn ~data:(a', i);
              Vec.set_exn b.alts i a'
            end;
            t, true
          | None ->
            (* Existing branch node: see if any alternatives can
               be merged with the program. If none matched, then
               the program just becomes a new alternative. *)
            t, merge_alt p b.alts b.memo
        end
      | _ :: _, Leaf _ ->
        (* Existing leaf: no continuation to descend. *)
        Tree.br [t; sequentialize p], false

    and merge_alt p alts memo =
      let key = List.hd_exn p in
      let any = ref false in
      (* Use first-fit ordering semantics like the paper. *)
      Vec.iteri alts ~f:(fun i a ->
          if not !any then match insert p a with
            | a', true ->
              Hashtbl.set memo ~key ~data:(a', i);
              Vec.set_exn alts i a';
              any := true
            | _ -> ());
      if not !any then begin
        let i = Vec.length alts in
        let a = sequentialize p in
        Hashtbl.set memo ~key ~data:(a, i);
        Vec.push alts a
      end;
      !any

    let emit code i =
      let label = Vec.length code in
      Vec.push code i;
      {label}

    let patch_next_at code i next =
      match Vec.get_exn code i.label with
      | Init i -> i.next <- next
      | Bind b -> b.next <- next
      | Check c -> c.next <- next
      | Compare c -> c.next <- next
      | Choose _ | Yield _ -> assert false

    let patch_choose_alt_at code i alt =
      match Vec.get_exn code i.label with
      | Choose c -> c.alt <- alt
      | _ -> assert false

    let linearize code t =
      let rec go = function
        | Leaf insn -> emit code insn
        | Seq s ->
          let label = emit code s.insn in
          patch_next_at code label @@ go s.next;
          label
        | Br b ->
          assert (not @@ Vec.is_empty b.alts);
          (* Emit a `choose` instruction for each alternative. *)
          let alts = Vec.fold b.alts ~init:[] ~f:(fun acc a ->
              (emit code @@ Choose {alt = None; next = go a}) :: acc) in
          (* Every alternative but the last one will have its
             next one as a continuation for its subtree. *)
          let label = List.fold alts ~init:None ~f:(fun alt ch ->
              patch_choose_alt_at code ch alt;
              Some ch) in
          (* Use the first alternative as the label. *)
          Option.value_exn label in
      go t

    (* Compute a backtracking priority for each program label.

       In this case, we want `yield` instructions to be visited
       in rule ID (insertion) order when we run the VM.
    *)
    let compute_rmin code =
      let n = Vec.length code in
      (* Compute the control-flow graph. *)
      let succs = Array.init n ~f:(fun i ->
          succs_of_insn @@ Vec.get_exn code i) in
      let preds = Array.create ~len:n [] in
      Array.iteri succs ~f:(fun i ss ->
          List.iter ss ~f:(fun s ->
              preds.(s) <- i :: preds.(s)));
      (* Seed the worklist with all `yield` instructions. *)
      let inf = Int.max_value in
      let rmin = Array.create ~len:n inf in
      let q = Stack.create () in
      Vec.iteri code ~f:(fun i -> function
          | Yield y ->
            rmin.(i) <- y.rule;
            Stack.push q i
          | _ -> ());
      (* Merge function. *)
      let min_succ i = List.fold succs.(i) ~init:inf
          ~f:(fun acc j -> Int.min acc rmin.(j)) in
      let yield_at i = match Vec.get_exn code i with
        | Yield y -> y.rule
        | _ -> inf in
      let merge p = Int.min (yield_at p) (min_succ p) in
      (* Perform a backwards-flow analysis until we reach a
         fixed point. *)
      Stack.until_empty q (fun v ->
          List.iter preds.(v) ~f:(fun p ->
              let m = merge p in
              if m < rmin.(p) then begin
                rmin.(p) <- m;
                Stack.push q p
              end));
      rmin

    let compile_tree forest i pat =
      match compile_one_rule i pat with
      | (Init i :: _) as p ->
        (* Trees that share the same root can be merged together. *)
        Hashtbl.update forest i.f ~f:(function
            | Some t -> fst @@ insert p t
            | None -> sequentialize p)
      | _ :: _ ->
        failwithf "compile_tree: invalid root at rule %d" i ()
      | [] ->
        failwithf "compile_tree: empty sequence at rule %d" i ()

    let compile ?(commute = false) rules =
      let rule = Vec.of_list rules in
      let code = Vec.create () in
      let root = Hashtbl.create (module Op) in
      let forest = Hashtbl.create (module Op) in
      let rmin = match rules with
        | [] -> [||]
        | _ ->
          if commute then
            Vec.iteri rule ~f:(fun i (pat, _) ->
                permute_commutative pat |>
                List.iter ~f:(compile_tree forest i))
          else
            Vec.iteri rule ~f:(fun i (pat, _) ->
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

    let frame_order f1 f2 = Int.compare f1.rule f2.rule

    type state = {
      mutable pc : label;
      mutable regs : regs;
      mutable lookup : id -> term;
      cont : frame Pairing_heap.t;
    }

    let default_lookup _ =
      failwith "VM: term lookup is uninitialized"

    let create () = {
      pc = nil;
      lookup = default_lookup;
      regs = Option_array.create ~len:16;
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

    let (.$[]<-) st r x =
      Option_array.set_some st.regs r.reg x

    let ensure_regs st need =
      let n = need + 1 in
      if Option_array.length st.regs < n then
        let current_len = Option_array.length st.regs in
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

    (* pre: each `x` should be unique *)
    let make_subst st regs : subst =
      List.fold regs ~init:String.Map.empty
        ~f:(fun s (r, x) -> Map.set s ~key:x ~data:st.$[r])

    type 'a result =
      | Continue
      | Yield of 'a yield

    let bind st o t next =
      ignore @@ load_args st o t;
      st.pc <- next

    let step st prog =
      if equal_label st.pc nil then
        raise_notrace Finished;
      match Vec.get_exn prog.code st.pc.label with
      | Init _ ->
        (* NB: this should be done manually at the toplevel *)
        assert false
      | Bind b ->
        let t = st.lookup st.$[b.i] in
        if term_equal_op t b.f
        then bind st b.o t b.next
        else backtrack st;
        Continue
      | Check c ->
        let t = st.lookup st.$[c.i] in
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
        let subst = make_subst st y.regs in
        let pat, payload = Vec.get_exn prog.rule y.rule in
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
        let n = load_args st {reg = 0} t in
        for i = n to Option_array.length st.regs - 1 do
          Option_array.set_none st.regs i;
        done;
        Pairing_heap.clear st.cont;
        true
      | _ -> assert false

    let many ?limit st prog =
      let result = ref [] in
      let count = ref 0 in
      let limit = Option.value limit ~default:Int.max_value in
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
