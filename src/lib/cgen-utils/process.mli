(** Running subprocesses and capturing their output.

    A thin wrapper over the process library that captures a command's exit
    status together with the full contents of its standard output and error.
    Capture goes through temporary files (created and removed automatically),
    rather than pipes, so a process emitting a lot of output cannot deadlock
    against a full pipe buffer.
*)

(** The captured result of a subprocess. *)
type t = {
  code   : Shexp_process.Exit_status.t;
  stdout : string;
  stderr : string;
}

(** [run ?stdin prog args] runs [prog] with [args] and captures its result.
    [stdin], if given, is fed to the process on standard input. *)
val run : ?stdin:string -> string -> string list -> t
