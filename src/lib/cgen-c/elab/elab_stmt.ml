(* Statement elaboration (C99 §6.8): `'a Stmt.t` to `Tstmt.t`.

   Drives the expression elaborator, supplied via the `elab_rval`
   and `elab_void` callbacks, in the right role at each position
   and threads block scopes through the elaborator state.

   Two lowerings bridge the surface forms and the flatter typed IR:

   - A controlling expression is a pure `Texpr.t` in the typed IR, so
     a loop condition with side effects is lowered to run those
     effects each iteration followed by `if (!cond) break;`.

   - A `for` init clause is lifted into an enclosing block (giving
     declarations, multiple declarators, and initializer side effects
     somewhere to live), leaving `Sfor` with no init clause; the step
     must reduce to a flat instruction list so that `continue` still
     targets it via `Sfor`.

   The walk also enforces the §6.8 control-flow constraints that need
   lexical context: `break`/`continue` placement (§6.8.6.2/§6.8.6.3)
   and `case`/`default` placement, uniqueness, and constant values
   (§6.8.1, §6.8.4.2).
*)

open Core

module Bv = Cgen_utils.Bv
module DM = Data_model
module EC = Elab_conv
module ET0 = Elab_type

open Elab_common

let one = Texpr.int_ Bv.one ~ty:(Type.int_ ())

(* `!cond` as an `int` 0/1, for the loop-condition lowering. *)
let negate cond = Texpr.unary ~op:`lnot_ ~arg:cond ~ty:(Type.int_ ())

let rec flatten_instrs (s : Tstmt.t) = match s with
  | Sinstr is -> Some is
  | Sblock items ->
    List.fold_until items ~init:[]
      ~finish:(fun acc -> Some (List.concat (List.rev acc)))
      ~f:(fun acc -> function
          | Bdecl _ -> Stop None
          | Bstmt s -> match flatten_instrs s with
            | Some is -> Continue (is :: acc)
            | None -> Stop None)
  | _ -> None

(* Rewrite every `continue` that targets the current loop into a
   `goto label`.

   Descends into blocks, `if`, labels, and `switch` bodies (a
   `continue` inside a switch still targets the enclosing loop),
   but not into nested loops, which capture their own `continue`.

   Used to lower a `for` whose step has control flow.
*)
let rec rewrite_continue label (s : Tstmt.t) = match s with
  | Scontinue -> Tstmt.goto label
  | Sblock items ->
    Tstmt.block @@ List.map items ~f:(function
        | Bdecl _ as d -> d
        | Bstmt s -> Tstmt.bstmt (rewrite_continue label s))
  | Sif {cond; then_; else_} ->
    Tstmt.if_ ~cond
      ~then_:(rewrite_continue label then_)
      ?else_:(Option.map else_ ~f:(rewrite_continue label))
      ()
  | Slabel {name; body} ->
    Tstmt.label ~name ~body:(rewrite_continue label body)
  | Sswitch {expr; body} ->
    Tstmt.switch ~expr ~body:(rewrite_continue label body)
  | Scase {value; body} ->
    Tstmt.case ~value ~body:(rewrite_continue label body)
  | Sdefault body -> Tstmt.default (rewrite_continue label body)
  (* Nested loops capture their own `continue`. *)
  | Swhile _
  | Sdowhile _
  | Sfor _
  | Sbreak
  | Sgoto _
  | Sgotoind _
  | Sreturn _
  | Sinstr _
    -> s

module Make(A : Annotation) = struct
  module Ctx = Elab_ctx.Make(A)
  module ET = ET0.Make(A)
  module EI = Elab_init.Make(A)

  open Ctx
  open Syntax

  (* Per-switch state for validating its labels (§6.8.4.2):

     - The promoted width of the controlling expression (case
       values are converted to it)
     - The set of case values seen so far (for duplicate detection)
     - Whether a `default` has appeared.
  *)
  type switch_state = {
    ctrl_bits            : int;
    mutable seen_cases   : Bv.t list;
    mutable seen_default : bool;
  }

  (* Threaded through the statement walk:

     - the expression-elaboration entry points
     - the lexical control-flow context used to check
       `break`/`continue`/`case`/`default` placement

     `in_loop` tracks an enclosing iteration statement (for
     `continue` and `break`)

     `switch` is the innermost enclosing switch, if any (for
     `break` and `case`/`default`).

     A loop nested inside a switch keeps `switch` set, so
     `case` labels may appear in it (such as with Duff's device).
  *)
  type env = {
    elab_rval   : A.ann Expr.t -> (Texpr.t -> Tstmt.t M.m) -> Tstmt.t M.m;
    elab_void   : A.ann Expr.t -> Tstmt.t M.m;
    elab_tydecl : A.ann Tydecl.t -> Tdecl.t option M.m;
    in_loop     : bool;
    switch      : switch_state option;
  }

  (* Elaborate `e` as an rvalue, capturing its side-effect statement
     and resulting value. *)
  let capture env e =
    let slot = ref None in
    let+ stmt = env.elab_rval e @@ fun rv ->
      slot := Some rv;
      !!(Tstmt.Sinstr []) in
    stmt, Option.value_exn !slot

  (* Evaluate `e` as an integer constant expression in the local context. *)
  let local_eval_int env (e : A.ann Expr.t) : Bv.t M.m =
    let* _stmt, rv = capture env e in
    let* layout = M.gets Ctx.layout in
    Ctx.lift_err @@ Eval.int_const (Eval.create_init layout) rv

  (* A non-VLA array bound must be an integer constant expression (§6.7.6.2).
     block-scope arrays are no exception (cgen has no VLAs). *)
  let elab_size env e =
    let+ v = local_eval_int env e in
    Texpr.int_ v ~ty:(Type.int_ ())

  (* Elaborate a controlling expression: capture it and require a
     scalar result. *)
  let elab_cond env e =
    let* stmt, rv = capture env e in
    let* tenv = M.gets Ctx.tenv in
    let+ () =
      M.unless (EC.is_scalar tenv rv.Texpr.ty) @@ fun () ->
      Ctx.fatal "controlling expression must have scalar type, got %a"
        pp_ty rv.ty () in
    stmt, rv

  let attr_arg ~eval_int (e : A.ann Expr.t) : Attr.arg option M.m =
    match e.Expr.node with
    | Expr.Econst (Expr.Cstr s) -> !!(Some (Attr.Astr s))
    | _ ->
      M.catch
        (let+ v = eval_int e >>| Bv.to_int64 in Some (Attr.Aint v))
        (fun _ -> match e.Expr.node with
           | Expr.Ename s -> !!(Some (Attr.Aname s))
           | _ -> !!None)

  let resolve_attr ~eval_int (r : A.ann Attr.raw) : Attr.t M.m =
    let+ args = M.List.filter_map r.Attr.rargs ~f:(attr_arg ~eval_int) in
    Attr.of_gnu r.Attr.rname args

  let resolve_attrs ~eval_int (raws : A.ann Attr.raws) : Attr.set M.m =
    M.List.map raws ~f:(resolve_attr ~eval_int)

  let local_align env (ld : A.ann Stmt.localdecl) =
    let+ attrs = resolve_attrs ~eval_int:(local_eval_int env) ld.ldattrs in
    match Attr.alignment attrs with
    | Some n when n > 0 -> Some n
    | _ -> None

  (* Elaborate a local declaration's type, resolving typedefs. Any block-scope
     typedef is dropped when the block is left (see `Layout.exit_block`), but
     the resolved type persists in the emitted declaration for the lowering. *)
  let elab_local_ty env ldty =
    let* ty = ET.elab ~elab_size:(elab_size env) ldty in
    let+ tenv = M.gets Ctx.tenv in
    Type_env.normalize tenv ty

  (* §6.7 ¶7: a block-scope object must have a complete type at the point
     of its declaration (unlike a file-scope tentative definition, which may
     be completed later). *)
  let require_complete_object ~name ~ty =
    let* tenv = M.gets Ctx.tenv in
    M.when_ (Option.is_some (Type_env.incomplete_object_type tenv ty)) @@ fun () ->
    Ctx.fatal "'%s' has incomplete type '%a'" name pp_ty ty ()

  (* Elaborate one local declaration, binding it in the current scope
     and returning the block items that realize it.

     The initializer's side-effect prefix, if any, is followed by the
     typed declaration.
  *)
  let elab_local env (ld : A.ann Stmt.localdecl) =
    match ld.ldstorage with
    | SCstatic ->
      (* §6.2.4 ¶3: a block-scope `static` has static storage but no
         linkage.

         We hoist it to a private module-level global under a unique
         mangled symbol and alias the source name to it, so references
         resolve to that symbol instead of a stack slot.

         Its initializer must be constant (via `require_const`), and
         no block item is emitted, so the lowering allocates no slot
         for it.
      *)
      let* base_ty = elab_local_ty env ld.ldty in
      let* sym = Ctx.fresh_static_sym ~source:ld.ldname in
      let* cty, init = match ld.ldinit with
        | None -> !!(base_ty, None)
        | Some i ->
          let+ _pre, cty, flat =
            EI.elab ~require_const:true ~elab_rval:env.elab_rval
              ~ty:base_ty i in
          cty, Some flat in
      let* () = Ctx.add_local ~name:ld.ldname ~ty:cty in
      let* () = Ctx.add_static_alias ~name:ld.ldname ~link:sym in
      let+ () =
        Ctx.hoist_global @@
        Tdecl.global ?init
          ~name:sym ~ty:cty
          ~linkage:Tdecl.Lstatic
          ~tls:false () in
      []
    | SCextern ->
      (* §6.2.2: a block-scope `extern` names an object with external
         linkage defined elsewhere; §6.7.8 ¶5 forbids an initializer.

         We alias the source name to itself so references become an
         (unmangled) external global symbol. No definition is emitted.
      *)
      let* () =
        M.when_ (Option.is_some ld.ldinit) @@ fun () ->
        let@ () = Ctx.with_location_of ld.ldann in
        Ctx.fatal "a block-scope 'extern' declaration shall have no initializer" () in
      let* base_ty = elab_local_ty env ld.ldty in
      let* () = Ctx.add_local ~name:ld.ldname ~ty:base_ty in
      let+ () = Ctx.add_static_alias ~name:ld.ldname ~link:ld.ldname in
      []
    | SCdefault | SCauto | SCregister ->
      let* base_ty = elab_local_ty env ld.ldty in
      let* align = local_align env ld in
      match ld.ldinit with
      | None ->
        let* () = require_complete_object ~name:ld.ldname ~ty:base_ty in
        let+ () = Ctx.add_local ~name:ld.ldname ~ty:base_ty in
        [Tstmt.bdecl (Tstmt.localdecl ~name:ld.ldname ~ty:base_ty ?align ())]
      | Some init ->
        (* §6.2.1 ¶7: the declared identifier is in scope inside its own
           initializer (a struct/array may reference its own address), so
           bind it before elaborating. The initializer may complete an array
           bound, so update the binding to the completed type afterward. *)
        let* () = Ctx.add_local ~name:ld.ldname ~ty:base_ty in
        let* pre, cty, flat =
          EI.elab ~elab_rval:env.elab_rval ~ty:base_ty init in
        let* () = Ctx.update_local ~name:ld.ldname ~ty:cty in
        let+ () = require_complete_object ~name:ld.ldname ~ty:cty in
        let decl =
          Tstmt.bdecl @@
          Tstmt.localdecl ~name:ld.ldname ~ty:cty ~init:flat ?align () in
        if stmt_is_empty pre then [decl] else [Tstmt.bstmt pre; decl]

  let elab_locals env locals =
    M.List.map locals ~f:(elab_local env) >>| List.concat

  let warn_unused_result (e : A.ann Expr.t) = match e.Expr.node with
    | Expr.Ecall {callee = {Expr.node = Expr.Ename fname; _}; _} ->
      let* attrs = M.gets (fun ctx -> Ctx.attrs_of ctx fname) in
      M.when_
        (Attr.exists attrs ~f:(function Attr.Warn_unused_result -> true | _ -> false))
      @@ fun () ->
      Ctx.warnf
        "ignoring return value of '%s', declared with attribute \
         warn_unused_result" fname ()
    | _ -> !!()

  let rec go env (s : A.ann Stmt.t) : Tstmt.t M.m =
    let@ () = Ctx.with_location_of s.ann in
    match s.node with
    (* §6.8.3 ¶3: the null statement. *)
    | Snull -> !!(Tstmt.instr [])
    (* §6.8.3: an expression statement evaluates the expression as a
       void expression (its value discarded). *)
    | Sexpr e ->
      let* () = warn_unused_result e in
      env.elab_void e
    | Sblock items -> go_block env items
    (* §6.8.6.1: `goto`. The target label's existence is validated by
       the whole-function pass in declaration elaboration. *)
    | Sgoto name -> !!(Tstmt.goto name)
    (* GNU computed goto: dispatch on the (index-valued) target. *)
    | Sgotoind e -> env.elab_rval e @@ fun rv -> !!(Tstmt.gotoind rv)
    | Sbreak -> stmt_break env
    | Scontinue -> stmt_continue env
    | Slabel {name; body} -> stmt_label env name body
    | Sif {cond; then_; else_} -> stmt_if env cond then_ else_
    | Swhile {cond; body} -> stmt_while env cond body
    | Sdowhile {body; cond} -> stmt_dowhile env body cond
    | Sfor {init; cond; step; body} -> go_for env ~init ~cond ~step ~body
    | Sswitch {expr; body} -> stmt_switch env expr body
    | Scase {value; body} -> stmt_case env value body
    | Sdefault body -> stmt_default env body
    | Sreturn value -> stmt_return env value

  (* §6.8.6.3: `break` shall appear only in or as a loop or switch
     body. *)
  and stmt_break env =
    let+ () =
      M.unless (env.in_loop || Option.is_some env.switch) @@ fun () ->
      Ctx.fatal "'break' statement not in a loop or switch" () in
    Tstmt.break

  (* §6.8.6.2: `continue` shall appear only in or as a loop body. *)
  and stmt_continue env =
    let+ () =
      M.unless env.in_loop @@ fun () ->
      Ctx.fatal "'continue' statement not in a loop" () in
    Tstmt.continue

  (* §6.8.1: a labeled statement. *)
  and stmt_label env name body =
    let+ body = go env body in
    Tstmt.label ~name ~body

  (* §6.8.4.1: the `if` statement; the controlling expression has
     scalar type. *)
  and stmt_if env cond then_ else_ =
    let* cstmt, crv = elab_cond env cond in
    let* then_ = go env then_ in
    let+ else_ = match else_ with
      | None -> !!None
      | Some s -> let+ s = go env s in Some s in
    let sif = Tstmt.if_ ~cond:crv ~then_ ?else_ () in
    if stmt_is_empty cstmt
    then sif
    else mkblock [
        Tstmt.bstmt cstmt;
        Tstmt.bstmt sif
      ]

  (* §6.8.5.1: the `while` statement.

     Its body is an iteration context for `break`/`continue`.
  *)
  and stmt_while env cond body =
    let* cstmt, crv = elab_cond env cond in
    let+ body = go {env with in_loop = true} body in
    if stmt_is_empty cstmt
    then Tstmt.while_ ~cond:crv ~body
    else
      (* `while (<effects>; crv) body`

         becomes

         `while (1) {<effects>; if (!crv) break; body}`
      *)
      let guard =
        Tstmt.if_
          ~cond:(negate crv)
          ~then_:Tstmt.break
          () in
      let body =
        mkblock [
          Tstmt.bstmt cstmt;
          Tstmt.bstmt guard;
          Tstmt.bstmt body;
        ] in
      Tstmt.while_ ~cond:one ~body

  (* §6.8.5.2: the `do`-`while` statement. *)
  and stmt_dowhile env body cond =
    let* body = go {env with in_loop = true} body in
    let+ cstmt, crv = elab_cond env cond in
    if stmt_is_empty cstmt
    then Tstmt.dowhile ~body ~cond:crv
    else
      (* `do body while (<effects>; crv)`

         becomes

         `do { body; <effects> } while (crv)`
      *)
      let body =
        mkblock [
          Tstmt.bstmt body;
          Tstmt.bstmt cstmt;
        ] in
      Tstmt.dowhile ~body ~cond:crv

  (* §6.8.4.2: the `switch` statement.

     The controlling expression has integer type and is
     integer-promoted. Its promoted type is what `case`
     values are converted to.

     The body opens a fresh switch context for its
     `case`/`default` labels.
  *)
  and stmt_switch env expr body =
    let* estmt, erv = capture env expr in
    let* tenv = M.gets Ctx.tenv in
    let* () =
      M.unless (EC.is_integer tenv erv.ty) @@ fun () ->
      Ctx.fatal "switch quantity must have integer type, got %a"
        pp_ty erv.ty () in
    let* dm = M.gets Ctx.dmodel in
    let erv = EC.promote_integer dm tenv erv in
    let ctrl_bits =
      Option.value (EC.int_bits dm tenv erv.ty) ~default:(DM.int_bits dm) in
    let state = {ctrl_bits; seen_cases = []; seen_default = false} in
    let+ body = go {env with switch = Some state} body in
    let sw = Tstmt.switch ~expr:erv ~body in
    if stmt_is_empty estmt
    then sw
    else mkblock [
        Tstmt.bstmt estmt;
        Tstmt.bstmt sw;
      ]

  (* §6.8.1, §6.8.4.2: a `case` label only inside a switch.

     Its value is an integer constant expression (unevaluated,
     so any ill-formed side effects are dropped), converted to
     the promoted type of the controlling expression, and distinct
     from the other case values.
  *)
  and stmt_case env value body =
    let* state = match env.switch with
      | Some s -> !!s
      | None -> Ctx.fatal "'case' label not within a switch" () in
    let* value =
      let@ () = Ctx.discarding_temps in
      let* _, rv = capture env value in
      let* layout = M.gets Ctx.layout in
      let+? v = Eval.int_const (Eval.create_init layout) rv in
      (* Convert to the promoted controlling type (§6.8.4.2 ¶2). *)
      Bv.extract ~hi:(state.ctrl_bits - 1) ~lo:0 v in
    let* () =
      M.when_ (List.mem state.seen_cases value ~equal:Bv.equal) @@ fun () ->
      Ctx.fatal "duplicate case value in switch" () in
    state.seen_cases <- value :: state.seen_cases;
    let+ body = go env body in
    Tstmt.case ~value ~body

  (* §6.8.1, §6.8.4.2: at most one `default` label per switch. *)
  and stmt_default env body =
    let* state = match env.switch with
      | Some s -> !!s
      | None -> Ctx.fatal "'default' label not within a switch" () in
    let* () =
      M.when_ state.seen_default @@ fun () ->
      Ctx.fatal "multiple default labels in one switch" () in
    state.seen_default <- true;
    let+ body = go env body in
    Tstmt.default body

  (* §6.8.6.4: `return`.

     A value is converted as if by assignment to the function's
     return type (`convert_for_return`), which also rejects
     returning a value from a `void` function.
  *)
  and stmt_return env value =
    match value with
    | None -> !!(Tstmt.return ())
    | Some e ->
      let* ret = M.gets Ctx.return_ty in
      let ret = match ret with
        | Some t -> t
        | None -> failwith "Elab_stmt: return outside a function" in
      let* estmt, rv = capture env e in
      let* layout = M.gets Ctx.layout in
      let tenv = Layout.tenv layout in
      let eval = Eval.create_init layout in
      let*? converted, w = EC.convert_for_return tenv eval ~ret ~rhs:rv in
      let+ () = Ctx.warn_opt w in
      let r = Tstmt.return ~value:converted () in
      if stmt_is_empty estmt then r else mkblock [
          Tstmt.bstmt estmt;
          Tstmt.bstmt r;
        ]

  (* Elaborate a block's items in the current scope, without pushing
     a fresh one.

     Shared by `go_block`, which wraps it in a fresh scope, and
     `elab_fnbody`, which runs it directly in the parameter scope.
  *)
  and block_items env items =
    let rec loop acc = function
      | [] -> !!(List.rev acc)
      | Stmt.Bstmt s :: rest ->
        let* s = go env s in
        loop (Tstmt.bstmt s :: acc) rest
      | Stmt.Bdecl locals :: rest ->
        let* items = elab_locals env locals in
        loop (List.rev_append items acc) rest
      | Stmt.Btype tds :: rest ->
        (* Register each block-scope type declaration in the current scope. *)
        let* () = M.List.iter tds ~f:(fun td ->
            env.elab_tydecl td >>= function
            | Some tdecl -> Ctx.hoist_global tdecl
            | None -> !!()) in
        loop acc rest in
    loop [] items

  and go_block env items =
    let@ () = Ctx.with_block_scope in
    let+ items = block_items env items in
    Tstmt.block items

  (* `for` is realized as an enclosing block holding the (lifted)
     init clause, around the loop proper. The init clause is lifted
     so declarations, multiple declarators, and initializer side
     effects have somewhere to live; the loop then sees them in this
     scope.

     When the step is a straight-line instruction list we use `Sfor`,
     whose step field preserves `continue` semantics directly.

     When the step has any other kind of control flow, it cannot fit
     `Sfor`'s `instr list`, so we lower to `while (1)` with the step
     at the bottom under a label and every `continue` in the body
     rewritten to jump there (see `for_loop`).

     A side-effecting condition is run each iteration before the body
     and tested with `if (!cond) break;`.
  *)
  and go_for env ~init ~cond ~step ~body =
    let@ () = Ctx.with_block_scope in
    let* pre = match init with
      | None -> !![]
      | Some Stmt.FIexpr e ->
        let+ s = env.elab_void e in
        if stmt_is_empty s then [] else [Tstmt.bstmt s]
      | Some Stmt.FIdecl locals -> elab_locals env locals in
    let* cond = match cond with
      | None -> !!None
      | Some c -> elab_cond env c >>| Option.some in
    let* body = go {env with in_loop = true} body in
    let* step = match step with
      | None -> !!(Tstmt.instr [])
      | Some e -> env.elab_void e in
    let+ loop = for_loop ~cond ~step ~body in
    mkblock (pre @ [Tstmt.bstmt loop])

  (* Build the loop proper from the elaborated condition (with its
     side-effect prefix), step statement, and body. *)
  and for_loop ~cond ~step ~body =
    match flatten_instrs step with
    | Some step -> !!(sfor_loop ~cond ~step ~body)
    | None -> while_loop ~cond ~step ~body

  (* Straight-line step: an `Sfor`.

     A side-effecting condition is moved to the top of the body as
     `if (!cond) break;`.
  *)
  and sfor_loop ~cond ~step ~body =
    match cond with
    | None -> Tstmt.for_ ~step ~body ()
    | Some (cstmt, crv) when stmt_is_empty cstmt ->
      Tstmt.for_ ~cond:crv ~step ~body ()
    | Some (cstmt, crv) ->
      let guard = Tstmt.if_ ~cond:(negate crv) ~then_:Tstmt.break () in
      let body =
        mkblock [
          Tstmt.bstmt cstmt;
          Tstmt.bstmt guard;
          Tstmt.bstmt body;
        ] in
      Tstmt.for_ ~step ~body ()

  (* Control-flow step: lower to

     ```
     while (1) { <cond?>; body'; L: step; }
     ```

     Where:

     1. `cond?` is the (optional) per-iteration condition check
     2. `L: step` puts the step at the bottom under a fresh label
     3. `body'` is `body` with each `continue` targeting this loop
       rewritten to `goto L` so the step still runs on `continue`.
  *)
  and while_loop ~cond ~step ~body =
    let+ label = Ctx.fresh_label in
    let body = rewrite_continue label body in
    let guard = match cond with
      | None -> []
      | Some (cstmt, crv) ->
        let g = Tstmt.if_ ~cond:(negate crv) ~then_:Tstmt.break () in
        if stmt_is_empty cstmt
        then [Tstmt.bstmt g]
        else [Tstmt.bstmt cstmt; Tstmt.bstmt g] in
    let labeled_step = Tstmt.label ~name:label ~body:step in
    let loop_body =
      mkblock (guard @ [Tstmt.bstmt body; Tstmt.bstmt labeled_step]) in
    Tstmt.while_ ~cond:one ~body:loop_body

  (* Public entry.

     A function body starts outside any loop or switch.
  *)
  let elab ~elab_rval ~elab_void ~elab_tydecl s =
    go {
      elab_rval;
      elab_void;
      elab_tydecl;
      in_loop = false;
      switch = None;
    } s

  (* Public entry for a function body.

     The body's outermost block is elaborated in the current scope
     rather than a fresh one, so the parameters (which the caller has
     already seeded into that scope) and the body's top-level locals
     share a scope: a top-level local that reuses a parameter name is a
     redeclaration error, not a legal shadow (C99 §6.8.1).

     A non-block body (unusual, but the AST permits it) is elaborated
     normally.
  *)
  let elab_fnbody ~elab_rval ~elab_void ~elab_tydecl (s : A.ann Stmt.t) =
    let env = {
      elab_rval;
      elab_void;
      elab_tydecl;
      in_loop = false;
      switch = None;
    } in
    match s.node with
    | Sblock items ->
      let@ () = Ctx.with_location_of s.ann in
      let+ items = block_items env items in
      Tstmt.block items
    | _ -> go env s
end
