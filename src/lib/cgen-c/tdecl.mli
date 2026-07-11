(** Typed (elaborated) top-level declarations.

    Produced by elaboration from [Decl.t]. Storage-class specifiers
    are collapsed into [linkage], and fields/parameters carry typed
    representations.
*)

open Core

(** External linkage class. *)
type linkage =
  | Lextern
  (** External linkage (visible across translation units). *)
  | Lstatic
  (** Internal linkage (file-scope only). *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** A function parameter. *)
type param = {
  pname : string;
  pty   : Texpr.ty;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A field in a [struct] or [union]. *)
type field = {
  fname  : string;
  (** The name of the field. *)
  fty    : Texpr.ty;
  (** The type of the field. *)
  fbits  : int option;
  (** The optional bitfield width. *)
  fattrs : Attr.set;
  (** Member attributes (e.g. [aligned]). *)
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A typed top-level declaration. *)
type t =
  | Dfundef of {
      name     : string;
      params   : param list;
      variadic : bool;
      ret      : Texpr.ty;
      body     : Tstmt.t;
      linkage  : linkage;
      inline   : bool;
      noreturn : bool;
      attrs    : Attr.set;
      (** Attributes affecting emission (e.g. [section], [weak], [visibility]). *)
      labaddrs : string list;
      (** Address-taken labels (targets of a computed [goto *]), in the
          index order used by [&&label]. *)
    } (** A function definition. *)
  | Dfundecl of {
      name     : string;
      params   : param list;
      variadic : bool;
      ret      : Texpr.ty;
      linkage  : linkage;
      attrs    : Attr.set;
    } (** A function declaration (prototype, no body). *)
  | Dglobal of {
      name    : string;
      ty      : Texpr.ty;
      init    : Texpr.init option;
      linkage : linkage;
      tls     : bool;
      attrs   : Attr.set;
    } (** A global object definition. *)
  | Dextern of {
      name    : string;
      ty      : Texpr.ty;
      linkage : linkage;
      tls     : bool;
    } (** A declaration of an externally-defined object. *)
  | Dcompound of {
      kind   : Type.compound;
      tag    : string;
      fields : field list;
    } (** A [struct] or [union] definition. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors} *)

(** A function parameter. *)
val param : name:string -> ty:Texpr.ty -> param

(** A field. [bits] is the bit-field width when declared as one. *)
val field :
  ?bits:int ->
  ?attrs:Attr.set ->
  name:string ->
  ty:Texpr.ty ->
  unit ->
  field

(** A function definition.

    [variadic], [inline], and [noreturn] default to [false].

    [linkage] defaults to [Lextern].

    [labaddrs] defaults to [[]].
*)
val fundef :
  ?variadic:bool ->
  ?linkage:linkage ->
  ?inline:bool ->
  ?noreturn:bool ->
  ?attrs:Attr.set ->
  ?labaddrs:string list ->
  name:string ->
  params:param list ->
  ret:Texpr.ty ->
  body:Tstmt.t ->
  unit ->
  t

(** A function declaration.

    [variadic] defaults to [false].

    [linkage] defaults to [Lextern].
*)
val fundecl :
  ?variadic:bool ->
  ?linkage:linkage ->
  ?attrs:Attr.set ->
  name:string ->
  params:param list ->
  ret:Texpr.ty ->
  unit ->
  t

(** A global object definition.

    [linkage] defaults to [Lextern].

    [tls] defaults to [false].
*)
val global :
  ?init:Texpr.init ->
  ?linkage:linkage ->
  ?tls:bool ->
  ?attrs:Attr.set ->
  name:string ->
  ty:Texpr.ty ->
  unit ->
  t

(** A declaration of an externally-defined object.

    [linkage] defaults to [Lextern].

    [tls] defaults to [false].
*)
val extern :
  ?linkage:linkage ->
  ?tls:bool ->
  name:string ->
  ty:Texpr.ty ->
  unit ->
  t

(** A [struct] or [union] definition. *)
val compound :
  kind:Type.compound ->
  tag:string ->
  fields:field list ->
  t

(** {1 Pretty printers} *)

(** Renders a function parameter. *)
val pp_param : Format.formatter -> param -> unit

(** Renders a struct/union field declaration with trailing semicolon
    (and bitfield width when present). *)
val pp_field : Format.formatter -> field -> unit

(** Renders a top-level declaration in C syntax. *)
val pp : Format.formatter -> t -> unit

(** [to_string d] is [pp] rendered to a string. *)
val to_string : t -> string
