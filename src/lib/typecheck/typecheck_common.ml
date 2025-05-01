open Core
open Virtual

module Env = Typecheck_env

let unify_fail = Env.unify_fail

type env = Env.t

type ctx = {
  env : env;
  fn  : func option;
  blk : blk option;
  ins : Label.t option;
}

module M = Sm.Make(struct
    type state = ctx
    let error_prefix = "Type error"
  end)

include M.Syntax

type 'a t = 'a M.m

(* Helper functions. *)

let getenv = M.gets @@ fun ctx -> ctx.env

let getfn = M.gets @@ fun ctx -> match ctx.fn with
  | None -> assert false
  | Some fn -> fn

let getblk = M.gets @@ fun ctx -> match ctx.blk with
  | None -> assert false
  | Some blk -> blk

let getins = M.gets @@ fun ctx -> match ctx.ins with
  | None -> assert false
  | Some ins -> ins

let target =
  let+ env = getenv in
  env.target

let updenv env = M.update @@ fun ctx -> {ctx with env}

let max_i8  = Bv.of_string "0xff"
let max_i16 = Bv.of_string "0xffff"
let max_i32 = Bv.of_string "0xffffffff"
let max_i64 = Bv.of_string "0xffffffffffffffff"

let max_of_imm : Type.imm -> Bv.t = function
  | `i8  -> max_i8
  | `i16 -> max_i16
  | `i32 -> max_i32
  | `i64 -> max_i64

let check_max i t =
  let m = max_of_imm t in
  if Bv.(i > m) then
    M.failf "Integer %a does not fit in type %a \
             (maximum value is %a)"
      Bv.pp i Type.pp_imm t Bv.pp m ()
  else !!(t :> Type.t)

let typeof_const : const -> Type.t t = function
  | `bool _ -> !!`flag
  | `int (i, t) -> check_max i t
  | `float _ -> !!`f32
  | `double _ -> !!`f64
  | `sym _ ->
    let+ t = target in
    (Target.word t :> Type.t)

let typeof_arg fn env : operand -> Type.t t = function
  | #const as c -> typeof_const c
  | `var v -> M.lift_err @@ Env.typeof_var fn v env

let typeof_type_arg env : Type.arg -> Type.t t = function
  | #Type.basic as t -> !!(t :> Type.t)
  | `name n ->
    let*? t = Env.typeof_typ n env in
    !!(t :> Type.t)

let typeof_type_ret env : Type.ret -> Type.t t = function
  | #Type.basic as t -> !!(t :> Type.t)
  | `si8 -> !!`i8
  | `si16 -> !!`i16
  | `si32 -> !!`i32
  | `name n ->
    let*? t = Env.typeof_typ n env in
    !!(t :> Type.t)
