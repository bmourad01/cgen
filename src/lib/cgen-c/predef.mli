(** C preprocessor predefines for a target.

    Emits the [-D] flags a [-undef] preprocessor needs so that portable code
    and the host's system headers see the correct compiler identity, including:

    - type sizes and maxima
    - byte order
    - data model
    - architecture
    - host operating system

    All except the host operating system are derived from the target's data model
    rather than inherited from whatever compiler happens to provide the preprocessor.

    The standard-mandated macros ([__STDC__], [__STDC_VERSION__], [__FILE__], etc.)
    survive [-undef], so they are intentionally not included here.
*)

(** [defines target] is the list of [-D] preprocessor arguments for [target]. *)
val defines : Cgen.Target.t -> string list
