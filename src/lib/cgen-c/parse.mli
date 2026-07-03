(** Parser for C translation units.

    Lexes and parses C source into a {!Cunit.t} annotated with source
    {!Cgen_utils.Location.t}, returning a structured
    {!Cgen_utils.Diagnostic.t} on failure.

    The lexer honors preprocessor line markers, so the input may be raw
    C or the output of a preprocessor. Each entry point optionally runs a
    preprocessor over the input first (see {!Cpp}); locations refer to the
    original source in either case.
*)

open Cgen_utils

(** Preprocessor configuration. *)
module Cpp : sig
  (** A preprocessor invocation: a program and its fixed leading arguments.

      The input specifier (a file name, or ["-"] for standard input) is
      appended when the preprocessor is run.
  *)
  type t

  (** A bare preprocessor invoked as [cpp -undef]: it strips the host
      compiler's predefined macros so that cgen can supply its own
      target-derived identity (see {!Predef}) rather than inherit the host's.
      The standard-mandated macros survive [-undef]. *)
  val default : t

  (** [create ~prog ?args ()] runs [prog] with fixed leading arguments [args]
      (default none). *)
  val create : prog:string -> ?args:string list -> unit -> t

  (** [add_args t extra] appends [extra] to the fixed arguments of [t]. *)
  val add_args : t -> string list -> t

  (** Parse a command line into a configuration: the first whitespace-separated
      token is the program, the rest are fixed arguments. Quoting is not
      interpreted.

      Example: [of_command "clang -E -I inc"] runs [clang -E -I inc <input>].
  *)
  val of_command : string -> t
end

(** Parse a raw string (the source name is reported as [<input>]); never
    preprocessed. *)
val from_string : string -> (Location.t Cunit.t, Diagnostic.t) result

(** Parse a file by name.

    With [?cpp], the preprocessor reads the file directly and its output
    is parsed. Without it, the file is parsed as-is (assumed already
    preprocessed).
*)
val from_file :
  ?cpp:Cpp.t ->
  string ->
  (Location.t Cunit.t, Diagnostic.t) result

(** Parse from an input channel, reported under [?file] (default [<stdin>]).

    With [?cpp], the channel's contents are fed to the preprocessor on
    standard input and its output is parsed. Without it, the channel is
    parsed as-is.
*)
val from_channel :
  ?cpp:Cpp.t ->
  ?file:string ->
  Core.In_channel.t ->
  (Location.t Cunit.t, Diagnostic.t) result

(** Parse from standard input; a specialization of {!from_channel}. *)
val from_stdin :
  ?cpp:Cpp.t ->
  unit ->
  (Location.t Cunit.t, Diagnostic.t) result
