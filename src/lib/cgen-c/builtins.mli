(** Registry of "simple" compiler builtins: pure, fixed-arity
    operations that lower to a single Structured IR primitive.

    Elaboration and lowering both consult {!find}. However, the
    [__builtin_va_*] family is a special case and is not described
    here.
*)

(** The IR primitive a simple builtin lowers to. *)
type op =
  | Clz       (** count leading zeros (undefined at zero) *)
  | Ctz       (** count trailing zeros (undefined at zero) *)
  | Popcount  (** population count *)
  | Bswap     (** reverse byte order *)

type t = private {
  operand : Texpr.ty;
  (** The argument is converted to this type *)
  result : Texpr.ty;
  (** The type of the call's result *)
  op : op;
  (** The IR primitive to emit *)
}

(** [find name] describes the simple builtin spelled [name] (its full
    ["__builtin_*"] identifier), or [None] if it is not one. *)
val find : string -> t option
