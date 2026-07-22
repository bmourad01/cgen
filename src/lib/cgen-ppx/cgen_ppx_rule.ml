(** A [%rule ...] extension that gives OCaml a [MonadFail]-style pattern-matching
    sugar for writing rewrite rules.

    Within the block, a refutable binding that does not match short-circuits the
    whole rule to [mzero] instead of raising, so a rule reads as a straight-line
    sequence of decompositions and guards ending in a pure success value.

    Desugaring (with the tail leaf implicitly lifted by [return], so the trailing
    [Some] is dropped):

    {v
    let PAT = e in k   ~> (match e with PAT -> <k> | _ -> mzero)    (* refutable *)
    let* PAT = e in k  ~> bind e (function PAT -> <k> | _ -> mzero)
    let*! PAT = e in k ~> (match e with Some PAT -> <k> | _ -> mzero) (* bare option *)
    let@ PAT = e in k  ~> let@ PAT = e in <k>                        (* opaque bind *)
    guard c; k         ~> if c then <k> else mzero
    if c then a else b ~> if c then <a> else <b>
    match e with cs    ~> match e with <cs>                         (* arms recursed *)
    fail               ~> mzero
    continue e         ~> e                                         (* e is already monadic; not lifted *)
    <leaf>             ~> return <leaf>
    v}

    [continue e] is the escape hatch for a tail that already yields the monad
    (a recursive call, say). It suppresses the implicit [return] the tail leaf
    would otherwise get, so the "dropped Some" convention does not double-wrap.

    The names [return], [bind] and [mzero] are resolved in the caller's scope
    through a [Rule_syntax] module (the ppx_let convention), so the same sugar
    serves any fallible monad. For the option monad: return x = Some x,
    bind = Option.bind, mzero = None.
*)

open Ppxlib
open Ast_builder.Default

let syntax_ref ~loc name = pexp_ident ~loc {
    txt = Ldot (Lident "Rule_syntax", name);
    loc;
  }

let mzero ~loc = syntax_ref ~loc "mzero"

let ret ~loc e = pexp_apply ~loc (syntax_ref ~loc "return") [Nolabel, e]

let bind_to ~loc ~exp ~f =
  pexp_apply ~loc (syntax_ref ~loc "bind") [Nolabel, exp; Nolabel, f]

(* Single-argument lambda in the merged-function AST (OCaml 5.2+). *)
let lam ~loc pat body =
  pexp_function ~loc
    [{pparam_loc = loc; pparam_desc = Pparam_val (Nolabel, None, pat)}]
    None (Pfunction_body body)

(* A bare `function ...` with the given cases. *)
let func_cases ~loc cases =
  pexp_function ~loc [] None (Pfunction_cases (cases, loc, []))

(* A syntactically-irrefutable pattern never fails to match, so it needs no
   fallthrough arm (and adding one would be a redundant-case warning).

   We take the conservative posture here, where anything not obviously
   irrefutable is treated as refutable.
*)
let rec is_irrefutable p = match p.ppat_desc with
  | Ppat_any | Ppat_var _ -> true
  | Ppat_constraint (p, _) | Ppat_alias (p, _) | Ppat_lazy p
  | Ppat_open (_, p) -> is_irrefutable p
  | Ppat_tuple ps -> List.for_all is_irrefutable ps
  | Ppat_record (fields, _) ->
    List.for_all (fun (_, p) -> is_irrefutable p) fields
  | Ppat_construct ({ txt = Lident "()"; _ }, None) -> true
  | _ -> false

(* `guard c; k` is a pseudo-statement recognized by its head identifier. *)
let guard_cond e = match e.pexp_desc with
  | Pexp_apply (
      {pexp_desc = Pexp_ident { txt = Lident "guard"; _ }; _},
      [Nolabel, c]
    ) -> Some c
  | _ -> None

(* The catch-all arm we insert is redundant for the rare exhaustive pattern;
   silence warning 11 locally rather than trying to prove exhaustiveness. *)
let silence_redundant e =
  let loc = e.pexp_loc in
  let attr =
    attribute ~loc ~name:{txt = "ocaml.warning"; loc}
      ~payload:(PStr [pstr_eval ~loc (estring ~loc "-11") []]) in
  {e with pexp_attributes = attr :: e.pexp_attributes}

(* Match `scrut` against `pat`, falling through to `mzero` on mismatch. *)
let refute ~loc ~scrut ~pat ~ok =
  silence_redundant @@ pexp_match ~loc scrut [
    case ~lhs:pat ~guard:None ~rhs:ok;
    case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:(mzero ~loc);
  ]

let monadic_let = ["let*"; "let+"]

let rec desugar e =
  let loc = e.pexp_loc in
  match e.pexp_desc with
  (* Descend through the binder chain (`fun p i -> ...`) and any annotation. *)
  | Pexp_function (params, ct, Pfunction_body body) ->
    {e with pexp_desc = Pexp_function (params, ct, Pfunction_body (desugar body))}
  | Pexp_function (params, ct, Pfunction_cases (cases, cloc, cattrs)) ->
    let cases = Pfunction_cases (List.map desugar_case cases, cloc, cattrs) in
    {e with pexp_desc = Pexp_function (params, ct, cases)}
  | Pexp_constraint (body, ty) ->
    {e with pexp_desc = Pexp_constraint (desugar body, ty)}
  (* Refutable `let PAT = e1 in k`: fail the rule if the shape does not match. *)
  | Pexp_let (Nonrecursive, [vb], body)
    when vb.pvb_attributes = []
      && not (is_irrefutable vb.pvb_pat) ->
    refute ~loc ~scrut:vb.pvb_expr ~pat:vb.pvb_pat ~ok:(desugar body)
  (* Any other let (irrefutable, rec, multi-binding): bindings stay opaque, the
     body is the monadic tail. *)
  | Pexp_let (rf, vbs, body) ->
    {e with pexp_desc = Pexp_let (rf, vbs, desugar body)}
  (* Monadic bind through the result monad: `let* PAT = e1 in k` / `let+ ...`. *)
  | Pexp_letop { let_; ands = []; body } when List.mem let_.pbop_op.txt monadic_let ->
    let f =
      if is_irrefutable let_.pbop_pat
      then lam ~loc let_.pbop_pat (desugar body)
      else silence_redundant @@ func_cases ~loc [
          case ~lhs:let_.pbop_pat ~guard:None ~rhs:(desugar body);
          case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:(mzero ~loc);
        ] in
    bind_to ~loc ~exp:let_.pbop_exp ~f
  (* `let*! PAT = e in k`: bind a bare `option`, declining to mzero on None.
     For a projection that yields a plain option rather than the result monad
     (e.g. a first-class projection param), this is the classic `let*!` lift. *)
  | Pexp_letop { let_; ands = []; body } when let_.pbop_op.txt = "let*!" ->
    let some =
      ppat_construct ~loc {txt = Lident "Some"; loc} (Some let_.pbop_pat) in
    refute ~loc ~scrut:let_.pbop_exp ~pat:some ~ok:(desugar body)
  (* Any other let-operator (e.g. a CPS `let@`) is an opaque bind whose body is
     the monadic tail. *)
  | Pexp_letop { let_; ands; body } ->
    {e with pexp_desc = Pexp_letop {let_; ands; body = desugar body}}
  (* `guard c; k` fails unless `c`. A plain `e1; k` keeps `e1` for effect. *)
  | Pexp_sequence (s, k) ->
    begin match guard_cond s with
      | Some c -> pexp_ifthenelse ~loc c (desugar k) (Some (mzero ~loc))
      | None -> {e with pexp_desc = Pexp_sequence (s, desugar k)}
    end
  (* Branches are all monadic tails. *)
  | Pexp_ifthenelse (c, t, Some f) ->
    pexp_ifthenelse ~loc c (desugar t) (Some (desugar f))
  | Pexp_match (scrut, cases) ->
    {e with pexp_desc = Pexp_match (scrut, List.map desugar_case cases)}
  (* Explicit failure. *)
  | Pexp_ident { txt = Lident "fail"; _ } -> mzero ~loc
  (* A tail already in the monad (e.g. a recursive call) gets spliced raw,
     so that the implicit `return` does not double-wrap it. *)
  | Pexp_apply (
      {pexp_desc = Pexp_ident { txt = Lident "continue"; _ }; _},
      [Nolabel, e']
    ) -> e'
  (* Leaf is a pure success value, lifted into the result monad. *)
  | _ -> ret ~loc e

and desugar_case c = {c with pc_rhs = desugar c.pc_rhs}

let ext =
  Extension.declare "rule" Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    (fun ~loc:_ ~path:_ e -> desugar e)

let () = Driver.register_transformation "cgen_ppx_rule" ~extensions:[ext]
