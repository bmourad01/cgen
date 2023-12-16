(** The target machine implementations. *)

(** The x86 family of targets. *)
module X86 : sig
  (** AMD64 for System V platforms. *)
  module Amd64_sysv : sig
    val target : Target.t
  end
end
