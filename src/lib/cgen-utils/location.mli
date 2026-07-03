(** Source locations.

    A [Location.t] describes a half-open byte range within a single
    source file, with matching line and column information for
    diagnostics. The [byte] offset is the authoritative coordinate for
    ordering and merging; [line] and [column] are derived bookkeeping
    suitable for display.
*)

open Core

(** A position within a source file. *)
type pos [@@deriving bin_io, compare, equal, hash, sexp]

(** A source range within a single file. *)
type t [@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Accessors} *)

(** Byte offset of [p] within its source file. *)
val byte : pos -> int

(** Line number of [p], 1-indexed by convention. *)
val line : pos -> int

(** Column number of [p], 1-indexed by convention. *)
val column : pos -> int

(** Source file containing the range. *)
val file : t -> string

(** Starting position of the range. *)
val start : t -> pos

(** Ending position of the range. *)
val end_ : t -> pos

(** {1 Smart constructors}

    Each constructor comes in two flavours: an [Or_error.t] variant
    suitable for use inside the [Or_error] monad, and an [_exn]
    variant that raises [Invalid_argument] on ill-formed input.
*)

(** Builds a position. Each of [byte], [line], and [column] must be
    non-negative. *)
val create_pos : byte:int -> line:int -> column:int -> pos Or_error.t

(** Like [create_pos], but raises [Invalid_argument] on bad input. *)
val create_pos_exn : byte:int -> line:int -> column:int -> pos

(** Builds a range. The [start] position must not come after [end_]
    by byte offset. *)
val create : file:string -> start:pos -> end_:pos -> t Or_error.t

(** Like [create], but raises [Invalid_argument] on bad input. *)
val create_exn : file:string -> start:pos -> end_:pos -> t

(** {1 Helpers} *)

(** The smallest range covering both [a] and [b]. The [file] field is
    taken from [a]; [merge] is intended for locations within the same
    source file. *)
val merge : t -> t -> t

(** Formats a location as ["file:line:start_col-end_col"] when [start]
    and [end_] are on the same line, or ["file:start_line:start_col-end_line:end_col"]
    otherwise. *)
val pp : Format.formatter -> t -> unit

(** [to_string t] is [pp] rendered to a string. *)
val to_string : t -> string
