(** Maps lexing positions to source {!Location.t} values.

    When the input being lexed is preprocessor output, the lexbuf's byte
    offsets index the preprocessed stream rather than the original
    source.

    Given the original file name (carried on each position via line markers),
    this module reconstructs the byte offset against the original file, so
    {!Location.byte} stays faithful to the source.

    For files that cannot be read, the raw stream offset is used as a fallback.
*)

(** A source map. Holds a lazily-populated, per-file line index. *)
type t

(** Creates an empty source map. *)
val create : unit -> t

(** [location_of t start end_] is the source range spanning the lexing
    positions [start] and [end_], with byte offsets reconstructed against
    the original file. *)
val location_of : t -> Lexing.position -> Lexing.position -> Location.t

(** [line_text t ~file n] is the text of the 1-indexed line [n] of [file]
    (excluding the line terminator), or [None] if [file] cannot be read or
    [n] is out of range.

    The file is read (and cached) on demand, so a fresh source map suffices
    to render an excerpt for any {!Location.t} whose file exists on disk.
*)
val line_text : t -> file:string -> int -> string option
