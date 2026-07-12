(** Registry of compiler builtins that produce a value from expression
    arguments *)

(** A raw IR primitive over one integer operand. *)
type op =
  | Clz       (** count leading zeros (undefined at zero) *)
  | Ctz       (** count trailing zeros (undefined at zero) *)
  | Popcount  (** population count *)
  | Bswap     (** reverse byte order *)

(** A builtin that emits a single IR primitive. *)
type prim = private {
  operand : Texpr.ty;
  (** The argument is converted to this type *)
  result : Texpr.ty;
  (** The type of the call's result *)
  op : op;
  (** The IR primitive to emit *)
}

(** How a value builtin is elaborated. *)
type t =
  | Prim of prim
  (** Emit the primitive over the single (converted) operand. *)
  | Parity of string
  (** [popcount(x) & 1]; carries the delegate [__builtin_popcount*] name. *)
  | Ffs of string
  (** [x ? ctz(x) + 1 : 0]; carries the delegate [__builtin_ctz*] name. *)
  | Expect
  (** The value of the first argument; the second is validated and then
      discarded (a branch-prediction hint we cannot consume). *)

(** [find name] describes the value builtin spelled [name] (its full
    ["__builtin_*"] identifier), or [None] if it is not one. *)
val find : string -> t option

(** [prim_exn name] is the {!prim} of a registered primitive builtin, used
    by derived builtins that delegate to one. Raises if [name] is not a
    registered {!Prim}. *)
val prim_exn : string -> prim
