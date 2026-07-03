(** Structured diagnostics emitted by elaboration (and, later, by
    the parser).

    A [Diagnostic.t] carries a severity, an optional source location,
    and a human-readable message. Clients that just want the
    [Or_error.t] form can use {!to_error}; clients that want to
    inspect or format it themselves (LSP output, IDE squiggles,
    severity-filtered reports) can pattern-match on it directly.
*)

open Core

(** Diagnostic severity. *)
type severity =
  | Error
  | Warning
  | Note
[@@deriving compare, equal, hash, sexp]

(** A diagnostic record. *)
type t [@@deriving compare, equal, hash, sexp]

(** {1 Constructors} *)

(** Build an [Error]-severity diagnostic. *)
val error : ?location:Location.t -> string -> t

(** Build a [Warning]-severity diagnostic. *)
val warning : ?location:Location.t -> string -> t

(** Build a [Note]-severity diagnostic. *)
val note : ?location:Location.t -> string -> t

val errorf   : ?location:Location.t -> ('a, Format.formatter, unit, unit -> t) format4 -> 'a
val warningf : ?location:Location.t -> ('a, Format.formatter, unit, unit -> t) format4 -> 'a
val notef    : ?location:Location.t -> ('a, Format.formatter, unit, unit -> t) format4 -> 'a

(** {1 Accessors} *)

val severity : t -> severity
val location : t -> Location.t option
val message  : t -> string

(** {1 Display} *)

(** Format a diagnostic as ["file:line:col: <severity>: <message>"]
    (the location prefix is elided when [location] is [None]). *)
val pp : Format.formatter -> t -> unit

(** [to_string t] is [pp] rendered to a string. *)
val to_string : t -> string

(** [pp_with_source ?color source ppf t] is iike {!pp}, but when the
    diagnostic has a location whose file is known to [source], append
    the offending source line followed by a caret underline of the
    location's column range:

    {v
    foo.c:3:11: error: use of undeclared identifier 'bar'
      3 |   return bar + 1;
        |          ^~~
    v}

    Falls back to the {!pp} header alone when the location is absent or the
    file cannot be read.

    When [color] is [true], severity and caret are styled with ANSI escapes.
    Default is [false], suitable for pipes and golden output.
*)
val pp_with_source : ?color:bool -> Source_map.t -> Format.formatter -> t -> unit

(** [to_string_with_source] is {!pp_with_source} rendered to a string. *)
val to_string_with_source : ?color:bool -> Source_map.t -> t -> string

(** {1 Conversions} *)

(** Lift to [Core.Error.t] for callers that want the [Or_error.t]
    form. *)
val to_error : t -> Error.t

(** Demote from [Core.Error.t]. Used as [Sm.S.of_or_error] so the
    monadic [failf] / [lift_err] helpers produce [Diagnostic.t]
    errors. The resulting diagnostic has [severity = Error] and
    no [location]. *)
val of_error : Error.t -> t
