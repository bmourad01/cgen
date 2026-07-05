(* Expression elaboration *)

open Core

module Bv = Cgen_utils.Bv
module DM = Data_model
module EC = Elab_conv
module ET0 = Elab_type
module TE = Type_env
module EE = TE.Enum_element

open Elab_common

(* Type of an integer literal (C99 §6.4.4.1 ¶5).

   For each suffix the standard gives a candidate list of types
   and assigns the literal the first type in the list whose range
   contains the value.

   A decimal constant's candidates are all signed; an octal, hexadecimal,
   or binary constant also admits the unsigned variant of each rank.
*)
let int_const_type dm ~base value suffix =
  let int_bits = DM.int_bits dm in
  let long_bits = DM.long_bits dm in
  let llong_bits = DM.long_long_bits in
  let fits_signed bits = Bv.(value <= max_signed_value bits) in
  let fits_unsigned bits = Bv.(value <= max_unsigned_value bits) in
  let int_ = Type.int_ () and uint = Type.int_ ~sign:Sunsigned () in
  let long_ = Type.long_ () and ulong = Type.long_ ~sign:Sunsigned () in
  let llong = Type.longlong_ () and ullong = Type.longlong_ ~sign:Sunsigned () in
  (* Whether the unsigned variant of each rank joins the candidate list. *)
  let alt = match base with `dec -> false | `oct | `hex | `bin -> true in
  match suffix with
  | None ->
    if fits_signed int_bits then int_
    else if alt && fits_unsigned int_bits then uint
    else if fits_signed long_bits then long_
    else if alt && fits_unsigned long_bits then ulong
    else if fits_signed llong_bits then llong
    else ullong
  | Some `u ->
    if fits_unsigned int_bits then uint
    else if fits_unsigned long_bits then ulong
    else ullong
  | Some `l ->
    if fits_signed long_bits then long_
    else if alt && fits_unsigned long_bits then ulong
    else if fits_signed llong_bits then llong
    else ullong
  | Some `ul ->
    if fits_unsigned long_bits then ulong
    else ullong
  | Some `ll ->
    if fits_signed llong_bits || not alt then llong
    else ullong
  | Some `ull -> ullong

(* Type of a literal constant (C99 §6.4.4.x). *)
let type_of_const dm (c : Expr.const) = match c with
  | Cint {value; suffix; base} -> int_const_type dm ~base value suffix
  | Cstr s ->
    (* `char[strlen(s) + 1]` including the null terminator. *)
    let len = String.length s + 1 in
    let bv = Bv.M64.int len in
    let size = Texpr.int_ bv ~ty:(Type.long_ ~sign:Sunsigned ()) in
    Type.array ~size (Type.plain_char_ ())
  | Cchar _ -> Type.int_ ()
  | Cfloat _ -> Type.float_ ()
  | Cdouble _ -> Type.double_ ()

(* Whether `ty`'s own size depends on a variable-length array
   dimension (an array whose size is not an integer constant
   expression).

   We follow array element chains (both dimensions of `T[m][n]`
   contribute to the size) but not pointers; e.g. `int (\*\)[n]`
   has a constant (pointer) size.
*)
let contains_vla layout ty =
  let tenv = Layout.tenv layout in
  let eval = Eval.create_init layout in
  let rec go ty = match ET0.normalize tenv ty with
    | Tarray {size = Some e; elem; _} ->
      begin match Eval.int_const eval e with
        | Ok _ -> go elem
        | Error _ -> true
      end
    | Tarray {size = None; elem; _} -> go elem
    | _ -> false in
  go ty

type pure_binop = [Expr.barith | Expr.bbitwise]

let find_field fields name =
  List.find fields ~f:(fun f -> String.(f.Tdecl.fname = name))

(* Whether `lv` designates a bit-field member.

   A bit-field's stored value is truncated to the field width and re-extended
   per its signedness, so the value of an assignment to it must be re-read from
   the field, not taken from the (untruncated) right-hand side (§6.5.16.1).
*)
let is_bitfield_lval layout tenv (lv : Texpr.tlval) = match lv.node with
  | Lmember {lval; field} ->
    begin match ET0.normalize tenv lval.ty with
      | Tnamed {kind = #Type.compound; name = tag; _} ->
        Result.is_ok (Layout.bitfield_info layout ~tag ~field)
      | _ -> false
    end
  | _ -> false

(* The truth value of a scalar rvalue as an `int` 0/1, i.e. the
   elaboration of `rv != 0`. The `(T)0` comparand (see `scalar_zero`)
   is a null pointer constant for pointer operands and a plain zero
   for arithmetic ones, so the single form covers both. *)
let truth_value (rv : Texpr.t) : Texpr.t =
  Texpr.binary ~op:`ne ~lhs:rv ~rhs:(scalar_zero rv.ty) ~ty:(Type.int_ ())

let known_nonzero eval (e : Texpr.t) : bool =
  match Eval.int_const eval e with
  | Ok v -> not Bv.(v = zero)
  | Error _ -> false

(* A conservative, syntactic test for whether evaluating `e` might fault:
   it loads from memory, or divides/takes the remainder by something not
   known to be nonzero. *)
let rec can_trap eval (e : Texpr.t) : bool = match e.node with
  | Econst _ | Evar _ | Efun _ | Eenum_const _ -> false
  | Eunary {op = `deref; _} | Eindex _ | Emember _ -> true
  | Ebinary {op = `div | `mod_; lhs; rhs} ->
    not (known_nonzero eval rhs) || can_trap eval lhs || can_trap eval rhs
  | Eunary {arg; _} -> can_trap eval arg
  | Ebinary {lhs; rhs; _} -> can_trap eval lhs || can_trap eval rhs
  | Ecast {arg; _} -> can_trap eval arg
  | Econd {cond; then_; else_} ->
    can_trap eval cond || can_trap eval then_ || can_trap eval else_
  | Eaddrof lv -> addr_can_trap eval lv
  | Ecompound _ -> true

(* The address of an lvalue evaluates the index/pointer subexpressions
   that locate it, but performs no load of the object itself. *)
and addr_can_trap eval (lv : Texpr.tlval) : bool = match lv.node with
  | Lvar _ -> false
  | Lderef e -> can_trap eval e
  | Lmember {lval; _} -> addr_can_trap eval lval
  | Lindex {lval; index} -> addr_can_trap eval lval || can_trap eval index

(* Name resolution

   An `Ename` resolves to one of four kinds, dispatched on which
   namespace of `Type_env` holds the name.

   The lookup order matches C99 scope rules: locals shadow file-scope
   identifiers.
*)
type resolved =
  | Rlocal  of string * Texpr.ty
  | Rglobal of string * Texpr.ty
  | Rfunc   of string * Texpr.ty
  | Renum   of TE.enum_element

module Make(A : Annotation) = struct
  module ET = ET0.Make(A)
  module EI = Elab_init.Make(A)
  module Ctx = ET.Ctx

  open Ctx
  open Syntax

  let resolve_name name =
    let* env = M.gets Ctx.tenv in
    match TE.find_local env name with
    | Some ty ->
      (* A block-scope static/extern is bound as a local for typing and
         scoping, but resolves to a link symbol (a global), so references
         lower to that symbol rather than a stack slot. *)
      let* link = M.gets (Ctx.static_link name) in
      begin match link with
        | Some sym -> !!(Rglobal (sym, ty))
        | None -> !!(Rlocal (name, ty))
      end
    | None -> match TE.find_global env name with
      | Some ty -> !!(Rglobal (name, ty))
      | None -> match TE.find_func env name with
        | Some ty -> !!(Rfunc (name, ty))
        | None -> match TE.find_enum_element env name with
          | Some e -> !!(Renum e)
          | None ->
            Ctx.fatal "undefined identifier '%s'" name ()

  (* C99 §6.4.2.2: `__func__` is implicitly declared in every function body as
     `static const char __func__[] = "<name>"`. GCC additionally provides the
     aliases `__FUNCTION__` and `__PRETTY_FUNCTION__`. We model all three as a
     string literal of the enclosing function's name (like most small
     compilers). *)
  let predefined_func_name = function
    | "__func__" | "__FUNCTION__" | "__PRETTY_FUNCTION__" ->
      M.gets Ctx.func_name
    | _ -> !!None

  (* Helper for building a Texpr.t for an enum constant, given its
     `Bv.t` value and the data model's `int` width. *)
  let enum_const_texpr dm ee =
    let bits = DM.int_bits dm in
    let m = Bv.modulus bits in
    let ty = Type.int_ () in
    Texpr.enum_const
      ~tag:(EE.tag ee)
      ~name:(EE.name ee)
      ~value:Bv.(int64 (EE.value ee) mod m)
      ~ty

  (* Look up the effective type of a field on a struct/union
     parent.

     §6.7.3 ¶9: a field of a cv-qualified compound is itself
     cv-qualified, so we OR the parent's outer cv into the field's
     own cv before returning.
  *)
  let lookup_field ~parent_ty ~field =
    let* tenv = M.gets Ctx.tenv in
    match ET0.normalize tenv parent_ty with
    | Tnamed {kind = #Type.compound; name = tag; _} ->
      begin match TE.find_tag tenv tag with
        | Some Tcompound {fields; _} ->
          begin match find_field fields field with
            | Some f ->
              let cv =
                Type.Cv.combine
                  (Type.cv_of parent_ty)
                  (Type.cv_of f.fty) in
              !!(Type.with_cv cv f.fty)
            | None ->
              Ctx.fatal "no field '%s' in type '%a'"
                field pp_ty parent_ty ()
          end
        | _ ->
          Ctx.fatal "member access on incomplete type '%a'"
            pp_ty parent_ty ()
      end
    | _ ->
      Ctx.fatal "member access on non-compound type '%a'"
        pp_ty parent_ty ()

  (* Type-check helpers.

     Each fails with a diagnostic naming the operator and operand
     type, so the §6.5 constraint violations surface at elaboration
     time.
  *)

  let require_unary ~op ~kind ~p (rv : Texpr.t) =
    let* tenv = M.gets Ctx.tenv in
    M.unless (p tenv rv.ty) @@ fun () ->
    Ctx.fatal "operand of unary '%s' must be %s, got '%a'"
      op kind pp_ty rv.ty ()

  let require_binary ~op ~kind ~p (lhs : Texpr.t) (rhs : Texpr.t) =
    let* tenv = M.gets Ctx.tenv in
    M.unless (p tenv lhs.ty && p tenv rhs.ty) @@ fun () ->
    Ctx.fatal "operands of binary '%s' must be %s, got '%a' and '%a'"
      op kind pp_ty lhs.ty pp_ty rhs.ty ()

  (* Comparison operand constraints (§6.5.8 / §6.5.9):

     - both arithmetic; or
     - both pointers, where:
         * for relational `<` `>` `<=` `>=` (§6.5.8 ¶2), the pointees
           are compatible object types, so neither a `void` nor a
           function type; or
         * for equality `==` `!=` (§6.5.9 ¶2), the pointees are
           compatible, or one is an object pointer and the other a
           `void *`; or
     - for equality only, one operand is a pointer and the other is a
       null pointer constant (§6.3.2.3 ¶3, computed by `Eval.const`).
  *)
  let require_comparison ~op ~is_equality (lhs : Texpr.t) (rhs : Texpr.t) =
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let eval = Eval.create_init layout in
    let lhs_t = ET0.normalize tenv lhs.ty in
    let rhs_t = ET0.normalize tenv rhs.ty in
    let la = Type.is_arithmetic lhs_t in
    let ra = Type.is_arithmetic rhs_t in
    let lp = Type.is_pointer lhs_t in
    let rp = Type.is_pointer rhs_t in
    let pointers_ok = match lhs_t, rhs_t with
      | Tptr {pointee = a; _}, Tptr {pointee = b; _} ->
        let a_void = Type.is_void a in
        let b_void = Type.is_void b in
        let a_fun = Type.is_function a in
        let b_fun = Type.is_function b in
        if is_equality then
          EC.pointee_compatible tenv eval a b
          || (a_void && not b_fun)
          || (b_void && not a_fun)
        else
          EC.pointee_compatible tenv eval a b
          && not (a_void || a_fun || b_void || b_fun)
      | _ -> false in
    let ok =
      (la && ra)
      || pointers_ok
      || (is_equality && lp && EC.is_null_pointer_constant eval rhs)
      || (is_equality && rp && EC.is_null_pointer_constant eval lhs)
      (* `pointers_ok` is the §6.5.8/§6.5.9-conformant check, but gcc accepts a
         comparison between two distinct, non-compatible pointer types
         (differing nested qualifiers or signedness) with a warning rather than
         an error. We match that leniency and warn below. Pointer-vs-integer is
         still rejected, as it needs `ra`/`la`, not `rp`/`lp`. *)
      || (lp && rp) in
    let* () =
      M.unless ok @@ fun () ->
      Ctx.fatal "operands of '%s' have incompatible types: '%a' and '%a'"
        op pp_ty lhs.ty pp_ty rhs.ty () in
    M.when_ (lp && rp && not pointers_ok) @@ fun () ->
    Ctx.warnf "comparison of distinct pointer types: '%a' and '%a'"
      pp_ty lhs.ty pp_ty rhs.ty ()

  (* Cast constraints (§6.5.4):

     - destination void: any source type accepted; or
     - destination scalar and operand scalar, with no float <-> pointer
       mix.
  *)
  let require_cast ~(dst : Texpr.ty) ~(arg : Texpr.t) =
    let* tenv = M.gets Ctx.tenv in
    M.unless (EC.is_void tenv dst) @@ fun () ->
    let* () = M.unless (EC.is_scalar tenv dst) @@ fun () ->
      Ctx.fatal "cast to non-scalar type '%a'" pp_ty dst () in
    let* () = M.unless (EC.is_scalar tenv arg.ty) @@ fun () ->
      Ctx.fatal "cast of non-scalar operand of type '%a'" pp_ty arg.ty () in
    let df = EC.is_floating tenv dst in
    let af = EC.is_floating tenv arg.ty in
    let dp = EC.is_pointer tenv dst in
    let ap = EC.is_pointer tenv arg.ty in
    M.when_ ((df && ap) || (dp && af)) @@ fun () ->
    Ctx.fatal "cast between pointer and floating types: '%a' to '%a'"
      pp_ty arg.ty pp_ty dst ()

  (* §6.3.2.1 ¶1: an lvalue used as the target of an assignment
     (or inc/dec) must be a modifiable lvalue, which excludes
     const-qualified types, array types, and function types. *)
  let require_modifiable ~op (lv : Texpr.tlval) =
    let* tenv = M.gets Ctx.tenv in
    let nty = ET0.normalize tenv lv.ty in
    let* () =
      M.when_ (Type.Cv.is_const (Type.cv_of lv.ty)) @@ fun () ->
      Ctx.fatal "'%s' on const-qualified lvalue of type '%a'"
        op pp_ty lv.ty () in
    let* () =
      M.when_ (Type.is_function nty) @@ fun () ->
      Ctx.fatal "'%s' on function-typed lvalue of type '%a'"
        op pp_ty lv.ty () in
    M.when_ (Type.is_array nty) @@ fun () ->
    Ctx.fatal "'%s' on array-typed lvalue of type '%a'"
      op pp_ty lv.ty ()

  (* §6.5.13–15: the operands of `&&` / `||` and the controlling
     operand of `?:` must have scalar type. `what` names the
     operand for the diagnostic. *)
  let require_scalar ~what (rv : Texpr.t) =
    let* tenv = M.gets Ctx.tenv in
    M.unless (EC.is_scalar tenv rv.ty) @@ fun () ->
    Ctx.fatal "%s must have scalar type, got '%a'" (what ()) pp_ty rv.ty ()

  (* The `size_t` value of `sizeof ty` (§6.5.3.4).

     For a type whose size is constant this is an integer constant
     expression (§6.6 ¶6) and we emit the folded literal. For a
     variable-length array type the size is computed at run time
     (§6.5.3.4 ¶2): the product of the (runtime) dimension lengths
     and the constant element size. The elaborator builds that
     expression as if the backend supported VLAs; rejection, if any,
     happens when lowering to Structured/Virtual IR.

     The result has type `size_t`.
  *)
  let rec sizeof_of ty : Texpr.t M.m =
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let dm = Layout.dmodel layout in
    (* We need to resolve all typedefs upfront, which helps us avoid a
       false "unresolved typedef" error. *)
    let nty = ET0.normalize tenv ty in
    let* () =
      M.when_ (EC.is_function tenv nty) @@ fun () ->
      Ctx.fatal "sizeof applied to a function type '%a'" pp_ty ty () in
    let size_t = DM.size_t dm in
    if not (contains_vla layout nty) then
      (* Constant size: a folded `size_t` literal. *)
      let+? n = Layout.sizeof layout nty in
      let bits = DM.pointer_bits dm in
      Texpr.int_ Bv.(int n mod modulus bits) ~ty:size_t
    else match nty with
      | Tarray {size = Some dim; elem; _} ->
        (* `dim * sizeof(elem)`, in `size_t`. The dimension length
           was elaborated at the declaration; the element size may
           itself be a runtime VLA size. *)
        let+ elem_sz = sizeof_of elem in
        let dim = Texpr.cast ~dst:size_t ~arg:dim in
        Texpr.binary ~op:`mul ~lhs:dim ~rhs:elem_sz ~ty:size_t
      | _ ->
        (* `contains_vla` only follows array element chains, so a
           VLA-containing type is necessarily a (complete) array. *)
        Ctx.fatal "sizeof of an incomplete array type '%a'" pp_ty ty ()

  (* Elaborate a list of expressions as rvalues, left-to-right,
     handing the resulting list to `cont`.

     Used in the `Ecall` case.
  *)
  let rec elab_rvals elab_one args cont = match args with
    | [] -> cont []
    | a :: rest ->
      let@ a_rv = elab_one a in
      let@ rest = elab_rvals elab_one rest in
      cont (a_rv :: rest)

  (* Read `lv` as an rvalue, applying the integer promotion (§6.3.1.1) that a
     bit-field undergoes.

     A field narrower than `int` promotes to `int`, so that, for example, a
     comparison against it is signed rather than unsigned.
  *)
  let read_lval_rvalue layout tenv dm (lv : Texpr.tlval) : Texpr.t =
    let rv = EC.lvalue_to_rvalue tenv lv in
    let promote = match lv.node with
      | Lmember {lval; field} ->
        begin match ET0.normalize tenv lval.ty with
          | Tnamed {kind = #Type.compound; name = tag; _} ->
            begin match Layout.bitfield_info layout ~tag ~field with
              | Ok bf -> Layout.Bitfield.width bf < DM.int_bits dm
              | Error _ -> false
            end
          | _ -> false
        end
      | _ -> false in
    if promote then Texpr.cast ~dst:(Type.int_ ()) ~arg:rv else rv

  (* Entry points *)

  let rec elab_rval (e : A.ann Expr.t) cont =
    let@ () = Ctx.with_location_of e.ann in
    match e.node with
    | Econst c -> rval_const c cont
    | Ename name -> rval_name name cont
    (* GNU `&&label`: a `void *` whose value is the label's dispatch index. *)
    | Elabaddr name ->
      let* i = Ctx.labaddr_index name in
      cont (Texpr.int_ Bv.(M64.int i) ~ty:(Type.ptr (Type.void ())))
    | Eunary {op = `addr; arg} -> rval_addrof arg cont
    | Eunary {op = `deref; _} | Eindex _ | Emember _ | Earrow _
    | Ecompound _ -> rval_of_lvalue e cont
    | Eunary {op = #Expr.uarith as op; arg} -> rval_unary_arith op arg cont
    | Eunary {op = `not_; arg} -> rval_complement arg cont
    | Eunary {op = `lnot_; arg} -> rval_lnot arg cont
    | Ebinary {op = #Expr.barith | #Expr.bbitwise as op; lhs; rhs} ->
      rval_binary op lhs rhs cont
    | Ebinary {op = #Expr.cmp as op; lhs; rhs} ->
      rval_compare op lhs rhs cont
    | Ecast {dst; arg} -> rval_cast dst arg cont
    | Esizeof_t ty -> rval_sizeof_t ty cont
    | Esizeof_e operand -> rval_sizeof_e operand cont
    | Eunary {op = #Expr.inc | #Expr.dec as op; arg} ->
      rval_incdec op arg cont
    | Ebinary {op = `assign; lhs; rhs} -> rval_assign lhs rhs cont
    | Ebinary {op = `assign_arith op_a; lhs; rhs} ->
      compound_assign (op_a :> pure_binop) lhs rhs cont
    | Ebinary {op = `assign_bitwise op_b; lhs; rhs} ->
      compound_assign (op_b :> pure_binop) lhs rhs cont
    | Ecall {callee; args} -> rval_call callee args cont
    | Ebinary {op = #Expr.blogical as op; lhs; rhs} ->
      rval_logical op lhs rhs cont
    | Econd {cond; then_; else_} -> rval_cond cond then_ else_ cont
    | Ecomma {lhs; rhs} -> rval_comma lhs rhs cont
    | Ebuiltin {name; args} -> rval_builtin name args cont

  (* A literal constant (§6.4.4).

     A string literal has array type (`char[N]`), and like any array
     it decays to a pointer to its first element in rvalue position
     (§6.3.2.1 ¶3).

     For the scalar constants `decay_array` is a no-op.
  *)
  and rval_const c cont =
    let* dm = M.gets Ctx.dmodel in
    let* tenv = M.gets Ctx.tenv in
    cont (EC.decay_array tenv (Texpr.const c ~ty:(type_of_const dm c)))

  (* An identifier (§6.5.1): a variable's value, a function
     designator (which decays to a function pointer), or an enum
     constant. *)
  and rval_name name cont =
    predefined_func_name name >>= function
    | Some fname -> rval_const (Cstr fname) cont
    | None ->
      let* r = resolve_name name in
      let* tenv = M.gets Ctx.tenv in
      let* dm = M.gets Ctx.dmodel in
      match r with
      | Rlocal (n, ty) | Rglobal (n, ty) ->
        let lv = Texpr.lvar n ~ty in
        cont (EC.lvalue_to_rvalue tenv lv)
      | Rfunc (n, ty) ->
        let fn_expr = Texpr.fun_ n ~ty in
        cont (EC.decay_function tenv fn_expr)
      | Renum e -> cont (enum_const_texpr dm e)

  (* Address-of `&e` (§6.5.3.2): a pointer to the operand lvalue. *)
  and rval_addrof arg cont =
    let@ arg_lv = elab_lval arg in
    cont (Texpr.addrof arg_lv ~ty:(Type.ptr arg_lv.ty))

  (* An lvalue form used as an rvalue (`*p`, `a[i]`, `s.f`, `p->f`,
     a compound literal): elaborate the lvalue and apply the lvalue
     conversion (§6.3.2.1). *)
  and rval_of_lvalue e cont =
    let* tenv = M.gets Ctx.tenv in
    let* layout = M.gets Ctx.layout in
    let* dm = M.gets Ctx.dmodel in
    let@ lv = elab_lval e in
    cont (read_lval_rvalue layout tenv dm lv)

  (* Unary `+` / `-` (§6.5.3.3 ¶1): arithmetic operand,
     integer-promoted; result type follows the promoted operand. *)
  and rval_unary_arith op arg cont =
    let@ arg_rv = elab_rval arg in
    let* () =
      require_unary
        ~op:(Texpr.uop_symbol op)
        ~kind:"arithmetic type"
        ~p:EC.is_arithmetic arg_rv in
    let* tenv = M.gets Ctx.tenv in
    let* dm = M.gets Ctx.dmodel in
    let arg_rv = EC.promote_integer dm tenv arg_rv in
    cont (Texpr.unary ~op ~arg:arg_rv ~ty:arg_rv.ty)

  (* Bitwise complement `~` (§6.5.3.3 ¶4): integer operand,
     integer-promoted; result type follows the promoted operand. *)
  and rval_complement arg cont =
    let@ arg_rv = elab_rval arg in
    let* () =
      require_unary
        ~op:"~"
        ~kind:"integer type"
        ~p:EC.is_integer arg_rv in
    let* tenv = M.gets Ctx.tenv in
    let* dm = M.gets Ctx.dmodel in
    let arg_rv = EC.promote_integer dm tenv arg_rv in
    cont (Texpr.unary ~op:`not_ ~arg:arg_rv ~ty:arg_rv.ty)

  (* Logical `!` (§6.5.3.3 ¶5): scalar operand; result `int`. *)
  and rval_lnot arg cont =
    let@ arg_rv = elab_rval arg in
    let* () =
      require_unary
        ~op:"!"
        ~kind:"scalar type"
        ~p:EC.is_scalar arg_rv in
    cont (Texpr.unary ~op:`lnot_ ~arg:arg_rv ~ty:(Type.int_ ()))

  (* Pure binary operators (§6.5.5, §6.5.6, §6.5.7, §6.5.10–12):
     both arithmetic/integer/pointer per the op's rules, with the
     appropriate promotions and/or UAC.

     Delegates to `compute_binop` so compound assignment can reuse
     the same logic.
  *)
  and rval_binary op lhs rhs cont =
    let@ lhs_rv = elab_rval lhs in
    let@ rhs_rv = elab_rval rhs in
    compute_binop op lhs_rv rhs_rv >>= cont

  (* Comparison (§6.5.8 / §6.5.9): result is always `int`. UAC
     applies for arithmetic operands; pointer operands pass
     through. *)
  and rval_compare op lhs rhs cont =
    let@ lhs_rv = elab_rval lhs in
    let@ rhs_rv = elab_rval rhs in
    let is_equality = match op with
      | #Expr.eq -> true
      | _ -> false in
    let* () =
      require_comparison
        ~op:(Texpr.bop_symbol op)
        ~is_equality
        lhs_rv rhs_rv in
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let dm = Layout.dmodel layout in
    let lhs', rhs' =
      if EC.is_arithmetic tenv lhs_rv.ty
      && EC.is_arithmetic tenv rhs_rv.ty then
        let a, b, _ = EC.usual_arith_conv dm tenv lhs_rv rhs_rv in
        a, b
      else
        (* §6.5.9 ¶5: a null pointer constant compared for equality with a
           pointer is converted to the pointer's type. *)
        let eval = Eval.create_init layout in
        if EC.is_pointer tenv lhs_rv.ty
        && EC.is_null_pointer_constant eval rhs_rv then
          lhs_rv, Texpr.cast ~dst:lhs_rv.ty ~arg:rhs_rv
        else if EC.is_pointer tenv rhs_rv.ty
             && EC.is_null_pointer_constant eval lhs_rv then
          Texpr.cast ~dst:rhs_rv.ty ~arg:lhs_rv, rhs_rv
        else lhs_rv, rhs_rv in
    cont (Texpr.binary ~op ~lhs:lhs' ~rhs:rhs' ~ty:(Type.int_ ()))

  (* Explicit cast (§6.5.4): elaborate the destination type, then
     validate that the conversion is allowed. *)
  and rval_cast dst arg cont =
    let* dst_ty = ET.elab ~elab_size dst in
    let@ arg_rv = elab_rval arg in
    let* () = require_cast ~dst:dst_ty ~arg:arg_rv in
    cont (Texpr.cast ~dst:dst_ty ~arg:arg_rv)

  (* sizeof(T) (§6.5.3.4): elaborate the type name and report its
     size. *)
  and rval_sizeof_t ty cont =
    let* ty' = ET.elab ~elab_size ty in
    sizeof_of ty' >>= cont

  (* sizeof e (§6.5.3.4 ¶2): we recover the operand's type without
     the lvalue conversion (arrays and functions keep their real
     type), rolling back any temporaries a dry elaboration reserves.

     The lvalue type is taken first (it is undecayed); the rvalue
     type is the fallback for non-lvalue operands. `sizeof_of` then
     yields a constant for a non-VLA type or a runtime size for a
     VLA.

     The standard evaluates a VLA operand to fix its dimensions;
     those were already captured at the declaration, so the dry type
     recovery suffices.

     A function designator is an lvalue of function type (see
     `lval_name`), so it is recovered undecayed on the lvalue path and
     `sizeof_of` rejects it (§6.5.3.4 ¶1).
  *)
  and rval_sizeof_e operand cont =
    let* operand_ty =
      let@ () = Ctx.discarding_temps in
      M.catch
        (let+ _, lv = capture_lval operand in
         lv.Texpr.ty)
        (fun _ ->
           let+ _, rv = capture_rval operand in
           rv.Texpr.ty) in
    sizeof_of operand_ty >>= cont

  (* Increment / decrement (§6.5.2.4 / §6.5.3.1): scalar modifiable
     lvalue operand.

     The lvalue is read once into a temp, the increment is computed
     from the temp and written back to the lvalue.

     The postfix forms hand the saved old value to `cont`, the prefix
     forms hand the new (converted) value.
  *)
  and rval_incdec op arg cont =
    let@ arg_lv = elab_lval arg in
    let op_sym = Expr.uop_symbol (op :> Expr.uop) in
    let* tenv = M.gets Ctx.tenv in
    let* () =
      M.unless (EC.is_scalar tenv arg_lv.ty) @@ fun () ->
      Ctx.fatal "operand of '%s' must be scalar, got '%a'"
        op_sym pp_ty arg_lv.ty () in
    let* () = require_modifiable ~op:op_sym arg_lv in
    let bop : pure_binop = match op with
      | `preinc | `postinc -> `add
      | `predec | `postdec -> `sub in
    let arg_rv = EC.lvalue_to_rvalue tenv arg_lv in
    let* tmp_lv = Ctx.fresh_tlval arg_lv.ty in
    let save = Tstmt.assign ~lval:tmp_lv ~expr:arg_rv in
    let tmp_rv = EC.lvalue_to_rvalue tenv tmp_lv in
    let one = Texpr.int_ Bv.one ~ty:(Type.int_ ()) in
    let* incremented = compute_binop bop tmp_rv one in
    let* layout = M.gets Ctx.layout in
    let eval = Eval.create_init layout in
    let*? converted, w =
      EC.convert_for_assign tenv eval ~lhs:arg_lv.ty ~rhs:incremented in
    let* () = Ctx.warn_opt w in
    let store = Tstmt.assign ~lval:arg_lv ~expr:converted in
    let result_rv = match op with
      | `preinc | `predec -> converted
      | `postinc | `postdec -> tmp_rv in
    let+ tail = cont result_rv in
    mkblock [
      Bstmt (
        Sinstr [
          save;
          store;
        ]
      );
      Bstmt tail;
    ]

  (* Simple assignment (§6.5.16.1): modifiable lvalue receives the
     rhs after the implicit assignment conversion.

     The expression's value is the LHS after the assignment.
  *)
  and rval_assign lhs rhs cont =
    let@ lhs_lv = elab_lval lhs in
    let@ rhs_rv = elab_rval rhs in
    let* () = require_modifiable ~op:"=" lhs_lv in
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let eval = Eval.create_init layout in
    let*? converted, w =
      EC.convert_for_assign tenv eval ~lhs:lhs_lv.ty ~rhs:rhs_rv in
    let* () = Ctx.warn_opt w in
    (* §6.5.16.1: the assignment's value is the left operand _after_ the
       store.

       For a bit-field, the stored value is truncated to the field width and
       re-extended per its signedness. We store the converted RHS and re-read
       the field.

       For an ordinary lvalue, the value is the converted RHS, but it must first
       be snapshotted into a temporary location. This is because the RHS may read
       the very object the store modifies (e.g. `*p = *p < x`), so reusing the
       expression tree would re-evaluate it only after the store.
    *)
    if is_bitfield_lval layout tenv lhs_lv then
      let store = Tstmt.assign ~lval:lhs_lv ~expr:converted in
      let value = EC.lvalue_to_rvalue tenv lhs_lv in
      let+ tail = cont value in
      mkblock [
        Bstmt (Sinstr [store]);
        Bstmt tail;
      ]
    else
      let* tmp = Ctx.fresh_tlval lhs_lv.ty in
      let value = EC.lvalue_to_rvalue tenv tmp in
      let snapshot = Tstmt.assign ~lval:tmp ~expr:converted in
      let store = Tstmt.assign ~lval:lhs_lv ~expr:value in
      let+ tail = cont value in
      mkblock [
        Bstmt (Sinstr [snapshot; store]);
        Bstmt tail;
      ]

  (* Function call (§6.5.2.2).

     The callee must be a function or a pointer to a function (after
     array-to-pointer decay it always ends up as a function pointer).

     The call result, when used in an rvalue context, is materialized
     through a fresh temp.
  *)
  and rval_call callee args cont =
    let@ fn_rv, converted_args, result_ty = with_call_parts callee args in
    let* tenv = M.gets Ctx.tenv in
    let* () =
      M.when_ (EC.is_void tenv result_ty) @@ fun () ->
      Ctx.fatal
        "value of a void-returning call cannot be used as an rvalue" () in
    let* tmp = Ctx.fresh_tlval result_ty in
    let call = Tstmt.call ~lval:tmp ~fn:fn_rv ~args:converted_args () in
    let result_rv = EC.lvalue_to_rvalue tenv tmp in
    let+ tail = cont result_rv in
    mkblock [
      Bstmt (Sinstr [call]);
      Bstmt tail;
    ]

  (* A compiler builtin used as an rvalue.

     Simple builtins (bit-counting and the like) are described uniformly by
     the `Builtins` registry; only the variadic `__builtin_va_*` family, which
     needs the ABI, is special-cased below.
  *)
  and rval_builtin name args cont = match Builtins.find name with
    | Some desc -> rval_simple_builtin name desc args cont
    | None -> match name, args with
      | ( "__builtin_parity"
        | "__builtin_parityl"
        | "__builtin_parityll" ), [Expr.BAexpr arg] ->
        rval_parity_builtin name arg cont
      | ( "__builtin_ffs"
        | "__builtin_ffsl"
        | "__builtin_ffsll" ), [Expr.BAexpr arg] ->
        rval_ffs_builtin name arg cont
      | "__builtin_va_arg", [Expr.BAexpr ap; Expr.BAtype ty] ->
        let* ty' = ET.elab ~elab_size ty in
        let@ ap_rv = elab_rval ap in
        let* tmp = Ctx.fresh_tlval ty' in
        let bi = Tstmt.builtin ~lval:tmp ~name ~args:[ap_rv] () in
        let* tenv = M.gets Ctx.tenv in
        let result_rv = EC.lvalue_to_rvalue tenv tmp in
        let+ tail = cont result_rv in
        mkblock [Bstmt (Sinstr [bi]); Bstmt tail]
      | "__builtin_va_arg", _ ->
        Ctx.fatal "__builtin_va_arg expects a va_list and a type" ()
      | ( "__builtin_va_start"
        | "__builtin_va_end"
        ), _ ->
        Ctx.fatal "'%s' does not produce a value" name ()
      | _ -> Ctx.fatal "unsupported builtin '%s'" name ()

  and rval_simple_builtin name (desc : Builtins.t) args cont =
    match args with
    | [Expr.BAexpr arg] ->
      let@ arg_rv = elab_rval arg in
      let* () =
        require_unary ~op:name ~kind:"integer type"
          ~p:EC.is_integer arg_rv in
      let arg_rv = Texpr.cast ~dst:desc.Builtins.operand ~arg:arg_rv in
      let* tmp = Ctx.fresh_tlval desc.Builtins.result in
      let bi = Tstmt.builtin ~lval:tmp ~name ~args:[arg_rv] () in
      let* tenv = M.gets Ctx.tenv in
      let result_rv = EC.lvalue_to_rvalue tenv tmp in
      let+ tail = cont result_rv in
      mkblock [Bstmt (Sinstr [bi]); Bstmt tail]
    | _ ->
      Ctx.fatal "'%s' expects one integer argument" name ()

  (* parity(x) = popcount(x) & 1: reuse the population count, then mask. *)
  and rval_parity_builtin name arg cont =
    let pop = match name with
      | "__builtin_parityll" -> "__builtin_popcountll"
      | "__builtin_parityl" -> "__builtin_popcountl"
      | _ -> "__builtin_popcount" in
    let desc = Option.value_exn (Builtins.find pop) in
    let@ pc = rval_simple_builtin pop desc [Expr.BAexpr arg] in
    let one = Texpr.int_ Bv.one ~ty:(Type.int_ ()) in
    cont (Texpr.binary ~op:`and_ ~lhs:pc ~rhs:one ~ty:(Type.int_ ()))

  (* ffs(x) = x ? ctz(x) + 1 : 0.

     The argument is snapshotted so it is evaluated once. `ctz(0)` is
     unspecified but never traps, so its result is simply discarded on
     the zero path.
  *)
  and rval_ffs_builtin name arg cont =
    let ctz = match name with
      | "__builtin_ffsll" -> "__builtin_ctzll"
      | "__builtin_ffsl" -> "__builtin_ctzl"
      | _ -> "__builtin_ctz" in
    let desc = Option.value_exn (Builtins.find ctz) in
    let@ arg_rv = elab_rval arg in
    let* () =
      require_unary
        ~op:name
        ~kind:"integer type"
        ~p:EC.is_integer arg_rv in
    let* xt = Ctx.fresh_tlval arg_rv.ty in
    let snapshot = Tstmt.assign ~lval:xt ~expr:arg_rv in
    let* tenv = M.gets Ctx.tenv in
    let x_rv = EC.lvalue_to_rvalue tenv xt in
    let cast_x = Texpr.cast ~dst:desc.Builtins.operand ~arg:x_rv in
    let* ct = Ctx.fresh_tlval desc.Builtins.result in
    let bi = Tstmt.builtin ~lval:ct ~name:ctz ~args:[cast_x] () in
    let ct_rv = EC.lvalue_to_rvalue tenv ct in
    let int_ = Type.int_ () in
    let one = Texpr.int_ Bv.one ~ty:int_ in
    let zero = Texpr.int_ Bv.zero ~ty:int_ in
    let ctz1 = Texpr.binary ~op:`add ~lhs:ct_rv ~rhs:one ~ty:int_ in
    let guard = truth_value x_rv in
    let result = Texpr.cond ~cond:guard ~then_:ctz1 ~else_:zero ~ty:int_ in
    let+ tail = cont result in
    mkblock [Bstmt (Sinstr [snapshot; bi]); Bstmt tail]

  (* `va_start`/`va_end` in statement (void) context.

     The va_list operand is its first argument; `va_start`'s
     named-parameter operand is not needed by the backend's `vastart`,
     so it is dropped.
  *)
  and void_va name ap =
    let@ ap_rv = elab_rval ap in
    !!(Tstmt.Sinstr [Tstmt.builtin ~name ~args:[ap_rv] ()])

  (* Elaborate `e` only to validate it (name resolution, type checking),
     emitting nothing and rolling back any temporaries. Used for the
     named-parameter operand of `va_start`, which the backend does not
     need but which must still be a well-formed expression. *)
  and check_expr e =
    let@ () = Ctx.discarding_temps in
    let+ _stmt, _rv = capture_rval e in
    ()

  (* Logical `&&` / `||` (§6.5.13 / §6.5.14): both operands scalar,
     result is `int` 0/1.

     Evaluation short-circuits (§6.5.13 ¶4, §6.5.14 ¶4): the rhs is
     evaluated only when the lhs does not already determine the result.

     When the rhs has no side effects we keep the operator as a pure
     expression, but still lazily, by lowering to the conditional:

     ```
     (a && b) becomes (a ? (b != 0) : 0)
     (a || b) becomes (a ? 1 : (b != 0))
     ```

     The rhs sits inside a conditional arm, so it is evaluated only on
     the short-circuit-taken path. This is important in the case of
     a computation that can trap or trigger UB.

     A side-effecting rhs cannot stay in expression form, so it lowers
     to a fresh result temp assigned under an `if`: the rhs branch runs
     b's side effects then records its truth value, and the other arm
     records the short-circuit constant.
  *)
  and rval_logical op lhs rhs cont =
    let what () =
      Format.sprintf "operand of %S" @@
      Expr.bop_symbol (op :> Expr.bop) in
    let@ a_rv = elab_rval lhs in
    let* () = require_scalar ~what a_rv in
    let* b_stmt, b_rv = capture_rval rhs in
    let* () = require_scalar ~what b_rv in
    let* eval = M.gets (fun c -> Eval.create_init (Ctx.layout c)) in
    let int_ = Type.int_ () in
    let zero = Texpr.int_ Bv.zero ~ty:int_ in
    let one = Texpr.int_ Bv.one ~ty:int_ in
    (* The pure form lowers to an eager `sel`, so only take it when the rhs
       has no side effects and cannot fault; otherwise short-circuit with a
       real branch so the rhs runs only on the taken path. *)
    if stmt_is_empty b_stmt && not (can_trap eval b_rv) then
      let tv = truth_value b_rv in
      cont @@ match op with
      | `land_ -> Texpr.cond ~cond:a_rv ~then_:tv ~else_:zero ~ty:int_
      | `lor_  -> Texpr.cond ~cond:a_rv ~then_:one ~else_:tv ~ty:int_
    else
      let* tenv = M.gets Ctx.tenv in
      let* result = Ctx.fresh_tlval int_ in
      let set v = Tstmt.Sinstr [Tstmt.assign ~lval:result ~expr:v] in
      (* The rhs branch runs b's side effects then records its
         truth value. *)
      let rhs_branch =
        mkblock [
          Bstmt b_stmt;
          Bstmt (set (truth_value b_rv));
        ] in
      let main = match op with
        | `land_ -> Tstmt.if_ ~cond:a_rv ~then_:rhs_branch ~else_:(set zero) ()
        | `lor_  -> Tstmt.if_ ~cond:a_rv ~then_:(set one) ~else_:rhs_branch () in
      let result_rv = EC.lvalue_to_rvalue tenv result in
      let+ tail = cont result_rv in
      mkblock [
        Bstmt main;
        Bstmt tail;
      ]

  (* Conditional `?:` (§6.5.15): scalar controlling operand; the
     result type is determined from the two arms.

     Lowered to a fresh result temp assigned in each branch, so
     side effects in an arm stay confined to that branch.
  *)
  and rval_cond cond then_ else_ cont =
    let@ cond_rv = elab_rval cond in
    let* () =
      require_scalar
        ~what:(fun () -> "the controlling operand of '?:'")
        cond_rv in
    let* then_stmt, then_rv = capture_rval then_ in
    let* else_stmt, else_rv = capture_rval else_ in
    let* result_ty = cond_result_type then_rv else_rv in
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let eval = Eval.create_init layout in
    let convert rv =
      let*? e, w = EC.convert_for_assign tenv eval ~lhs:result_ty ~rhs:rv in
      let+ () = Ctx.warn_opt w in
      e in
    (* When neither arm has side effects and neither can fault, the
       conditional is a pure expression: emit `Texpr.cond` directly with no
       temp (it lowers to an eager `sel`). An arm that loads memory or
       divides must instead run only on its taken branch. *)
    if stmt_is_empty then_stmt
    && stmt_is_empty else_stmt
    && not (can_trap eval then_rv)
    && not (can_trap eval else_rv)
    then
      let* then_e = convert then_rv in
      let* else_e = convert else_rv in
      cont @@ Texpr.cond
        ~cond:cond_rv
        ~then_:then_e
        ~else_:else_e
        ~ty:result_ty
    else
      let* tmp = Ctx.fresh_tlval result_ty in
      let arm stmt rv =
        let+ converted = convert rv in
        let assign = Tstmt.assign ~lval:tmp ~expr:converted in
        mkblock [
          Bstmt stmt;
          Bstmt (Sinstr [assign]);
        ] in
      let* then_branch = arm then_stmt then_rv in
      let* else_branch = arm else_stmt else_rv in
      let main =
        Tstmt.if_
          ~cond:cond_rv
          ~then_:then_branch
          ~else_:else_branch
          () in
      let result_rv = EC.lvalue_to_rvalue tenv tmp in
      let+ tail = cont result_rv in
      mkblock [
        Bstmt main;
        Bstmt tail;
      ]

  (* Comma operator (§6.5.17): evaluate the lhs for its side
     effects, discard its value, then yield the rhs. *)
  and rval_comma lhs rhs cont =
    let@ _ = elab_rval lhs in
    elab_rval rhs cont

  and elab_lval (e : A.ann Expr.t) cont =
    let@ () = Ctx.with_location_of e.ann in
    match e.node with
    | Ename name -> lval_name name cont
    | Eunary {op = `deref; arg} -> lval_deref arg cont
    | Eindex {arr; idx} -> lval_index arr idx cont
    | Emember {obj; field} -> lval_member obj field cont
    | Earrow {obj; field} -> lval_arrow obj field cont
    | Ecompound {ty; init} -> lval_compound ty init cont
    | Eunary {op = `addr; _} ->
      Ctx.fatal "the result of '&' is not an lvalue" ()
    (* Any other expression form (constants, arithmetic, calls,
       casts, &c.) is not an lvalue. *)
    | _ ->
      Ctx.fatal "expression is not an lvalue" ()

  (* An identifier naming an object (§6.5.1). Functions and enum
     constants are not assignable.

     Note: a function designator is an lvalue of function type (its
     address is the function symbol). It is not modifiable, but `&func`
     and `sizeof func` need its undecayed type, and `require_modifiable`
     rejects it in assignment/increment contexts.
  *)
  and lval_name name cont =
    predefined_func_name name >>= function
    | Some _ -> Ctx.fatal "'%s' cannot be used as an lvalue" name ()
    | None -> resolve_name name >>= function
      | Rlocal (n, ty)
      | Rglobal (n, ty)
      | Rfunc (n, ty)
        -> cont (Texpr.lvar n ~ty)
      | Renum e ->
        Ctx.fatal "enum constant '%s' is not assignable" (EE.name e) ()

  (* Indirection `*p` (§6.5.3.2): the object the pointer designates. *)
  and lval_deref arg cont =
    let@ arg_rv = elab_rval arg in
    let* tenv = M.gets Ctx.tenv in
    match ET0.normalize tenv arg_rv.ty with
    | Tptr {pointee; _} ->
      cont (Texpr.lderef arg_rv ~ty:pointee)
    | _ ->
      Ctx.fatal "dereference of non-pointer type '%a'" pp_ty arg_rv.ty ()

  (* Subscripting `a[i]` (§6.5.2.1): equivalent to `*(a + i)`; an
     lvalue of the element type (carrying the array's cv-qualifiers). *)
  and lval_index arr idx cont =
    let@ arr_lv = elab_lval arr in
    let@ idx_rv = elab_rval idx in
    let* tenv = M.gets Ctx.tenv in
    let* ty = match ET0.normalize tenv arr_lv.ty with
      | Tarray {elem; cv; _} ->
        let combined = Type.Cv.combine cv (Type.cv_of elem) in
        !!(Type.with_cv combined elem)
      | Tptr {pointee; _} -> !!pointee
      | _ ->
        Ctx.fatal
          "subscript on non-array/pointer type '%a'"
          pp_ty arr_lv.ty () in
    cont (Texpr.lindex ~lval:arr_lv ~index:idx_rv ~ty)

  (* Direct member access `s.f` (§6.5.2.3): an lvalue. *)
  and lval_member obj field cont =
    let@ obj_lv = elab_lval obj in
    let* fty = lookup_field ~parent_ty:obj_lv.ty ~field in
    cont (Texpr.lmember ~lval:obj_lv ~field ~ty:fty)

  (* Member access through a pointer `p->f` (§6.5.2.3): `\(\*p).f`. *)
  and lval_arrow obj field cont =
    let@ obj_rv = elab_rval obj in
    let* tenv = M.gets Ctx.tenv in
    match ET0.normalize tenv obj_rv.ty with
    | Tptr {pointee; _} ->
      let* fty = lookup_field ~parent_ty:pointee ~field in
      let lv_struct = Texpr.lderef obj_rv ~ty:pointee in
      cont (Texpr.lmember ~lval:lv_struct ~field ~ty:fty)
    | _ ->
      Ctx.fatal "arrow on non-pointer type '%a'" pp_ty obj_rv.ty ()

  (* Compound literal (§6.5.2.5): `(T){init}` designates an unnamed
     object (an lvalue).

     We materialize it as a fresh local carrying the flattened
     initializer. Any side effects of the initializer's leaves
     are sequenced before the use.
  *)
  and lval_compound ty init cont =
    let* target = ET.elab ~elab_size ty in
    let* fname = M.gets Ctx.func_name in
    match fname with
    | None ->
      (* §6.5.2.5 ¶6: a compound literal that occurs outside the body of a
         function has static storage duration. Hoist it to a private global
         and designate that object, so its address is a constant usable in a
         static initializer (e.g. `static int *p = (int[]){1,2,3}`). Its
         initializer must itself be constant. *)
      let* _prefix, completed_ty, flat =
        EI.elab ~require_const:true ~elab_rval ~ty:target init in
      let* sym = Ctx.fresh_static_sym ~source:"compound" in
      let* () = Ctx.add_global ~name:sym ~ty:completed_ty in
      let* () =
        Ctx.hoist_global @@
        Tdecl.global ()
          ~init:flat
          ~name:sym
          ~ty:completed_ty
          ~linkage:Tdecl.Lstatic
          ~tls:false in
      cont (Texpr.lvar sym ~ty:completed_ty)
    | Some _ ->
      (* Inside a function: automatic storage, a block-local temporary. *)
      let* prefix, completed_ty, flat =
        EI.elab ~elab_rval ~ty:target init in
      let* tmp = Ctx.fresh_tlval ~init:flat completed_ty in
      let+ tail = cont tmp in
      mkblock [
        Bstmt prefix;
        Bstmt tail;
      ]

  (* `+` / `-` (§6.5.6): pointer +/- integer, integer +/- pointer,
     pointer - pointer (yields ptrdiff_t, represented here as signed
     long), or arithmetic UAC.

     Returns the resulting rvalue so it can be reused by compound
     assignment.
  *)
  and compute_addsub op tenv dm (lhs : Texpr.t) (rhs : Texpr.t) =
    let lp = EC.is_pointer tenv lhs.ty in
    let rp = EC.is_pointer tenv rhs.ty in
    match op, lp, rp with
    | `add, true, false ->
      let rhs = EC.promote_integer dm tenv rhs in
      Texpr.binary ~op:`add ~lhs ~rhs ~ty:lhs.ty
    | `add, false, true ->
      let lhs = EC.promote_integer dm tenv lhs in
      Texpr.binary ~op:`add ~lhs ~rhs ~ty:rhs.ty
    | `sub, true, true ->
      Texpr.binary ~op:`sub ~lhs ~rhs ~ty:(DM.ptrdiff_t dm)
    | `sub, true, false ->
      let rhs = EC.promote_integer dm tenv rhs in
      Texpr.binary ~op:`sub ~lhs ~rhs ~ty:lhs.ty
    | _ ->
      let lhs, rhs, dst = EC.usual_arith_conv dm tenv lhs rhs in
      Texpr.binary ~op ~lhs ~rhs ~ty:dst

  (* Compute the rvalue produced by a pure binary operator (no
     short-circuit, no assignment) on already-elaborated operands,
     applying the §6.5 constraint checks and the appropriate
     promotions and/or UAC. *)
  and compute_binop (op : pure_binop) lhs rhs =
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let dm = Layout.dmodel layout in
    match op with
    | `mul | `div as op ->
      let+ () =
        require_binary
          ~op:(Texpr.bop_symbol op)
          ~kind:"arithmetic"
          ~p:EC.is_arithmetic
          lhs rhs in
      let l, r, dst = EC.usual_arith_conv dm tenv lhs rhs in
      Texpr.binary ~op ~lhs:l ~rhs:r ~ty:dst
    | `mod_ ->
      let+ () =
        require_binary
          ~op:"%"
          ~kind:"integer"
          ~p:EC.is_integer
          lhs rhs in
      let l, r, dst = EC.usual_arith_conv dm tenv lhs rhs in
      Texpr.binary ~op:`mod_ ~lhs:l ~rhs:r ~ty:dst
    | `add | `sub as op ->
      !!(compute_addsub op tenv dm lhs rhs)
    | `and_ | `or_ | `xor as op ->
      let+ () =
        require_binary
          ~op:(Texpr.bop_symbol op)
          ~kind:"integer"
          ~p:EC.is_integer
          lhs rhs in
      let l, r, dst = EC.usual_arith_conv dm tenv lhs rhs in
      Texpr.binary ~op ~lhs:l ~rhs:r ~ty:dst
    | `shl | `shr as op ->
      let+ () =
        require_binary
          ~op:(Texpr.bop_symbol op)
          ~kind:"integer"
          ~p:EC.is_integer
          lhs rhs in
      let lhs' = EC.promote_integer dm tenv lhs in
      let rhs' = EC.promote_integer dm tenv rhs in
      Texpr.binary ~op ~lhs:lhs' ~rhs:rhs' ~ty:lhs'.ty

  (* Elaborate `e` as an rvalue, capturing both the statement that
     carries its side effects and the resulting rvalue.

     Used by the branching forms, where an arm's side effects must
     be confined to its branch but the arm's type/value is needed
     to build the enclosing construct.
  *)
  and capture_rval e =
    let slot = ref None in
    let+ stmt = elab_rval e @@ fun rv ->
      slot := Some rv;
      !!(Tstmt.Sinstr []) in
    match !slot with
    | Some rv -> stmt, rv
    | None -> failwith "Elab_expr.capture_rval: continuation not invoked"

  (* Like `capture_rval`, but for the lvalue interpretation. Used by
     `sizeof e` to recover the operand's undecayed (lvalue) type. *)
  and capture_lval e =
    let slot = ref None in
    let+ stmt = elab_lval e @@ fun lv ->
      slot := Some lv;
      !!(Tstmt.Sinstr []) in
    match !slot with
    | Some lv -> stmt, lv
    | None -> failwith "Elab_expr.capture_lval: continuation not invoked"

  (* Elaborate a constant expression appearing inside a type (array
     size, sizeof operand). Drives `elab_rval` with a side-effect-
     capturing continuation and discards the synthetic statement.

     Pure expressions (the only valid form here per §6.6) leak no
     temps; an impure expression would leak side effects, but that's
     a constraint violation we'd reject earlier in a stricter mode.
  *)
  and elab_size e = capture_rval e >>| snd

  (* Result type of the conditional operator (§6.5.15 ¶3–6):

     - both arithmetic: usual arithmetic conversions;
     - both void: void;
     - one pointer, the other a null pointer constant: the pointer
       type;
     - both pointers: pointer to the composite, with the union of the
       two pointees' qualifiers; if either points to void, the result
       is a (qualified) pointer to void;
     - both the same struct/union: that type.
  *)
  and cond_result_type (a : Texpr.t) (b : Texpr.t) =
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let dm = Layout.dmodel layout in
    let eval = Eval.create_init layout in
    let na = ET0.normalize tenv a.ty in
    let nb = ET0.normalize tenv b.ty in
    if EC.is_arithmetic tenv a.ty && EC.is_arithmetic tenv b.ty then
      let _, _, dst = EC.usual_arith_conv dm tenv a b in
      !!dst
    else if Type.is_void na && Type.is_void nb then
      !!(Type.void ())
    else if EC.is_pointer tenv a.ty && EC.is_null_pointer_constant eval b then
      !!(a.ty)
    else if EC.is_pointer tenv b.ty && EC.is_null_pointer_constant eval a then
      !!(b.ty)
    else match na, nb with
      | Tptr {pointee = pa; _}, Tptr {pointee = pb; _} ->
        let cv = Type.Cv.combine (Type.cv_of pa) (Type.cv_of pb) in
        if EC.is_void tenv pa || EC.is_void tenv pb then
          !!(Type.ptr ~cv (Type.void ()))
        else if EC.pointee_compatible tenv eval pa pb then
          !!(Type.ptr (Type.with_cv cv (Type.unqualified pa)))
        else
          Ctx.fatal "pointer type mismatch in '?:': '%a' and '%a'"
            pp_ty a.ty pp_ty b.ty ()
      | Tnamed {kind = #Type.compound; name = ta; _},
        Tnamed {kind = #Type.compound; name = tb; _}
        when String.(ta = tb) -> !!(a.ty)
      | _ ->
        Ctx.fatal "incompatible operand types in '?:': '%a' and '%a'"
          pp_ty a.ty pp_ty b.ty ()

  (* Compound assignment (§6.5.16.2). The lhs is evaluated once,
     read into a temporary, the underlying binary op is applied,
     the result is converted back to the lhs's type, and stored.

     This is the shared core of a compound assignment `LHS op= RHS` (§6.5.16.2).
     The basic operation is to read the LHS once into a temporary location,
     compute `tmp op RHS`, and finally provide the continuation with:

     - the LHS lvalue
     - the `save` of the old value
     - the converted new value to `k`
  *)
  and compound_parts (op : pure_binop) lhs rhs k =
    let@ lhs_lv = elab_lval lhs in
    let@ rhs_rv = elab_rval rhs in
    let op_sym = Texpr.bop_symbol (op :> Texpr.bop) ^ "=" in
    let* () = require_modifiable ~op:op_sym lhs_lv in
    let* tenv = M.gets Ctx.tenv in
    let lhs_rv = EC.lvalue_to_rvalue tenv lhs_lv in
    let* tmp_lv = Ctx.fresh_tlval lhs_lv.ty in
    let save = Tstmt.assign ~lval:tmp_lv ~expr:lhs_rv in
    let tmp_rv = EC.lvalue_to_rvalue tenv tmp_lv in
    let* result = compute_binop op tmp_rv rhs_rv in
    let* layout = M.gets Ctx.layout in
    let eval = Eval.create_init layout in
    let*? converted, w = EC.convert_for_assign tenv eval ~lhs:lhs_lv.ty ~rhs:result in
    let* () = Ctx.warn_opt w in
    k ~lhs_lv ~save ~converted ~tenv

  and compound_assign (op : pure_binop) lhs rhs cont =
    compound_parts op lhs rhs @@ fun ~lhs_lv ~save ~converted ~tenv ->
    let* layout = M.gets Ctx.layout in
    (* §6.5.16.1: the value is the left operand after the store, evaluated
       once.

       For a bit-field, re-read the (truncated) field.

       For a normal lvalue, snapshot the new value into a temp (mirrored in
       `rval_assign`), since reusing `converted` would re-evaluate the RHS
       after the store.
    *)
    if is_bitfield_lval layout tenv lhs_lv then
      let store = Tstmt.assign ~lval:lhs_lv ~expr:converted in
      let value = EC.lvalue_to_rvalue tenv lhs_lv in
      let+ tail = cont value in
      mkblock [
        Bstmt (Sinstr [save; store]);
        Bstmt tail;
      ]
    else
      let* res_lv = Ctx.fresh_tlval lhs_lv.ty in
      let snapshot = Tstmt.assign ~lval:res_lv ~expr:converted in
      let res_rv = EC.lvalue_to_rvalue tenv res_lv in
      let store = Tstmt.assign ~lval:lhs_lv ~expr:res_rv in
      let+ tail = cont res_rv in
      mkblock [
        Bstmt (Sinstr [save; snapshot; store]);
        Bstmt tail;
      ]

  (* A compound assignment whose value is discarded is just the read-modify-
     write; no snapshot temp is needed (cf. `compound_assign`). *)
  and compound_void (op : pure_binop) lhs rhs =
    compound_parts op lhs rhs @@ fun ~lhs_lv ~save ~converted ~tenv:_ ->
    let store = Tstmt.assign ~lval:lhs_lv ~expr:converted in
    !!(Tstmt.Sinstr [save; store])

  (* Convert the argument rvalues for a call (§6.5.2.2):

     - Prototyped parameters receive the assignment conversion to
       each parameter's type
     - Positions beyond the prototype's fixed parameters (variadic)
       and every argument of a K&R callee receive the default-argument
       promotions.
  *)
  and convert_call_args ~params ~variadic ~tenv ~dm ~eval args =
    match params with
    | None ->
      !!(List.map args ~f:(fun a -> EC.default_arg_promote dm tenv a))
    | Some ps ->
      let n_params = List.length ps in
      let n_args = List.length args in
      let* () =
        if variadic then
          M.when_ (n_args < n_params) @@ fun () ->
          Ctx.fatal
            "too few arguments to variadic function: got %d, expected \
             at least %d" n_args n_params ()
        else
          M.unless (n_args = n_params) @@ fun () ->
          Ctx.fatal
            "wrong number of arguments: got %d, expected %d"
            n_args n_params () in
      let rec convert ps args = match ps, args with
        | [], [] -> !![]
        | [], extra ->
          !!(List.map extra ~f:(EC.default_arg_promote dm tenv))
        | p :: ps_rest, a :: args_rest ->
          let*? converted, w =
            EC.convert_for_assign tenv eval ~lhs:p.Type.ptype ~rhs:a in
          let* () = Ctx.warn_opt w in
          convert ps_rest args_rest >>|
          List.cons converted
        | _ :: _, [] -> assert false in
      convert ps args

  (* Shared core of a function call (§6.5.2.2): elaborate the callee
     (which must be a function or pointer to function), elaborate and
     convert the arguments, and hand `(fn, converted_args, result_ty)`
     to `k`.

     Both the rvalue use (which stores the result) and the void use
     (which discards it) build on this.
  *)
  and with_call_parts callee args k =
    let@ fn_rv = elab_rval callee in
    let* tenv = M.gets Ctx.tenv in
    let* fty = match ET0.normalize tenv fn_rv.ty with
      | Tptr {pointee; _} ->
        begin match ET0.normalize tenv pointee with
          | Tfun _ as f -> !!f
          | _ ->
            Ctx.fatal "called object has non-function type '%a'"
              pp_ty fn_rv.ty ()
        end
      | Tfun _ as f -> !!f
      | _ ->
        Ctx.fatal "called object has non-function type '%a'"
          pp_ty fn_rv.ty () in
    let result_ty, params, variadic = match fty with
      | Tfun {result; params; variadic} -> result, params, variadic
      | _ -> assert false in
    let@ arg_rvs = elab_rvals elab_rval args in
    let* dm = M.gets Ctx.dmodel in
    let* layout = M.gets Ctx.layout in
    let eval = Eval.create_init layout in
    let* converted_args =
      convert_call_args ~params ~variadic ~tenv ~dm ~eval arg_rvs in
    k (fn_rv, converted_args, result_ty)

  (* Elaborate `e` in a void (statement) context: its value is
     discarded.

     The void-typed forms are:
     - void-returning call
     - conditional whose value is unused
     - comma

     These are handled directly here so they never hit the rvalue
     path's rejection of void values. Everything else is elaborated
     as an rvalue whose result is dropped (side effects are retained).
  *)
  and elab_void (e : A.ann Expr.t) =
    let@ () = Ctx.with_location_of e.ann in
    match e.node with
    | Ecomma {lhs; rhs} ->
      let@ _ = elab_rval lhs in
      elab_void rhs
    | Econd {cond; then_; else_} ->
      let@ cond_rv = elab_rval cond in
      let* () =
        require_scalar
          ~what:(fun () -> "the controlling operand of '?:'")
          cond_rv in
      let* then_s = elab_void then_ in
      let+ else_s = elab_void else_ in
      Tstmt.if_ ~cond:cond_rv ~then_:then_s ~else_:else_s ()
    | Ecall {callee; args} ->
      let@ fn_rv, converted_args, _result_ty = with_call_parts callee args in
      !!(Tstmt.Sinstr [Tstmt.call ~fn:fn_rv ~args:converted_args ()])
    | Ebuiltin {name = "__builtin_va_start"; args = [BAexpr ap; BAexpr last]} ->
      let* () = check_expr last in
      void_va "__builtin_va_start" ap
    | Ebuiltin {name = "__builtin_va_end"; args = [BAexpr ap]} ->
      void_va "__builtin_va_end" ap
    | Ebuiltin {name = "__builtin_va_start"; _} ->
      Ctx.fatal "builtin_va_start expects a 'va_list' and the last named parameter" ()
    | Ebuiltin {name = "__builtin_va_end"; _} ->
      Ctx.fatal "__builtin_va_end expects a 'va_list'" ()
    | Ebinary {op = `assign; lhs; rhs} ->
      (* We don't need to snapshot the result to a temporary location
         here, because the assignment is in a context where the result
         is simply discarded. *)
      let@ lhs_lv = elab_lval lhs in
      let@ rhs_rv = elab_rval rhs in
      let* () = require_modifiable ~op:"=" lhs_lv in
      let* layout = M.gets Ctx.layout in
      let tenv = Layout.tenv layout in
      let eval = Eval.create_init layout in
      let*? converted, w =
        EC.convert_for_assign tenv eval ~lhs:lhs_lv.ty ~rhs:rhs_rv in
      let+ () = Ctx.warn_opt w in
      Tstmt.Sinstr [Tstmt.assign ~lval:lhs_lv ~expr:converted]
    | Ebinary {op = `assign_arith op_a; lhs; rhs} ->
      compound_void (op_a :> pure_binop) lhs rhs
    | Ebinary {op = `assign_bitwise op_b; lhs; rhs} ->
      compound_void (op_b :> pure_binop) lhs rhs
    | _ ->
      let@ _ = elab_rval e in
      !!(Tstmt.Sinstr [])

  (* Elaborate `e` and assign its rvalue into `dest`, applying the
     usual assignment conversion. *)
  and elab_into ~(dest : Texpr.tlval) e =
    let@ rv = elab_rval e in
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let eval = Eval.create_init layout in
    let* converted, w = Ctx.lift_err @@
      EC.convert_for_assign tenv eval ~lhs:dest.ty ~rhs:rv in
    let* () = Ctx.warn_opt w in
    !!(Tstmt.Sinstr [Tstmt.assign ~lval:dest ~expr:converted])
end
