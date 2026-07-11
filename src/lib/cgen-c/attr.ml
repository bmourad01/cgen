open Core

type arg =
  | Aint  of int64
  | Astr  of string
  | Aname of string
[@@deriving bin_io, compare, equal, hash, sexp]

type visibility = Default | Hidden | Internal | Protected
[@@deriving bin_io, compare, equal, hash, sexp]

type t =
  | Aligned of int option
  | Packed
  | Noreturn
  | Always_inline
  | Noinline
  | Pure
  | Const
  | Malloc
  | Cold
  | Hot
  | Used
  | Unused
  | Deprecated of string option
  | Warn_unused_result
  | Returns_twice
  | Nothrow
  | Section of string
  | Visibility of visibility
  | Weak
  | Alias of string
  | Constructor of int option
  | Destructor of int option
  | Transparent_union
  | May_alias
  | Mode of string
  | Nonnull of int list
  | Format of string * int * int
  | Cleanup of string
  | Other of string * arg list
[@@deriving bin_io, compare, equal, hash, sexp]

type set = t list
[@@deriving bin_io, compare, equal, hash, sexp]

let empty = []
let is_empty = List.is_empty
let of_list = Fn.id
let to_list = Fn.id
let add a s = a :: s
let union = ( @ )

type 'a raw = {
  rname : string;
  rargs : 'a Expr.t list;
} [@@deriving bin_io, compare, equal, hash, sexp]

type 'a raws = 'a raw list
[@@deriving bin_io, compare, equal, hash, sexp]

let raw rname rargs = {rname; rargs}

(* GNU canonically spells attributes `__name__`. We strip a surrounding
   `__` so that `__aligned__`, `__aligned`, and `aligned` all match. *)
let normalize name =
  let s = Option.value (String.chop_prefix name ~prefix:"__") ~default:name in
  Option.value (String.chop_suffix s ~suffix:"__") ~default:s

let visibility_of_string = function
  | "default"   -> Some Default
  | "hidden"    -> Some Hidden
  | "internal"  -> Some Internal
  | "protected" -> Some Protected
  | _           -> None

let of_gnu_visibility v args = match visibility_of_string v with
  | Some vis -> Visibility vis
  | None -> Other ("visibility", args)

let of_gnu_format = function
  | [Aname a; Aint f; Aint v] ->
    Format (a, Int64.to_int_trunc f, Int64.to_int_trunc v)
  | args -> Other ("format", args)

let of_gnu name args =
  let ints = List.filter_map args ~f:(function
      | Aint n -> Some (Int64.to_int_trunc n)
      | _ -> None) in
  match normalize name, args with
  | "aligned", []           -> Aligned None
  | "aligned", [Aint n]     -> Aligned (Some (Int64.to_int_trunc n))
  | "packed", _             -> Packed
  | "noreturn", _           -> Noreturn
  | "always_inline", _      -> Always_inline
  | "noinline", _           -> Noinline
  | "pure", _               -> Pure
  | "const", _              -> Const
  | "malloc", _             -> Malloc
  | "cold", _               -> Cold
  | "hot", _                -> Hot
  | "used", _               -> Used
  | "unused", _             -> Unused
  | "deprecated", [Astr s]  -> Deprecated (Some s)
  | "deprecated", _         -> Deprecated None
  | "warn_unused_result", _ -> Warn_unused_result
  | "returns_twice", _      -> Returns_twice
  | "nothrow", _            -> Nothrow
  | "section", [Astr s]     -> Section s
  | "visibility", [Astr v]  -> of_gnu_visibility v args
  | "weak", _               -> Weak
  | "alias", [Astr s]       -> Alias s
  | "constructor", []       -> Constructor None
  | "constructor", [Aint n] -> Constructor (Some (Int64.to_int_trunc n))
  | "destructor", []        -> Destructor None
  | "destructor", [Aint n]  -> Destructor (Some (Int64.to_int_trunc n))
  | "transparent_union", _  -> Transparent_union
  | "may_alias", _          -> May_alias
  | "mode", [Aname m]       -> Mode m
  | "nonnull", _            -> Nonnull ints
  | "cleanup", [Aname f]    -> Cleanup f
  | "format", _             -> of_gnu_format args
  | nm, _                   -> Other (nm, args)

let exists s ~f = List.exists s ~f
let find_map s ~f = List.find_map s ~f

let noreturn s = exists s ~f:(function Noreturn -> true | _ -> false)
let packed   s = exists s ~f:(function Packed -> true | _ -> false)

let alignment s =
  find_map s ~f:(function
      | Aligned Some n -> Some n
      | Aligned None   -> Some 0
      | _              -> None)

let section       s = find_map s ~f:(function Section x -> Some x | _ -> None)
let visibility    s = find_map s ~f:(function Visibility v -> Some v | _ -> None)
let alias         s = find_map s ~f:(function Alias x -> Some x | _ -> None)
let weak          s = exists s ~f:(function Weak -> true | _ -> false)
let used          s = exists s ~f:(function Used -> true | _ -> false)
let unused        s = exists s ~f:(function Unused -> true | _ -> false)
let is_deprecated s = exists s ~f:(function Deprecated _ -> true | _ -> false)

let string_of_visibility = function
  | Default -> "default" | Hidden -> "hidden"
  | Internal -> "internal" | Protected -> "protected"

let pp_arg ppf = function
  | Aint n  -> Format.fprintf ppf "%Ld" n
  | Astr s  -> Format.fprintf ppf "%S" s
  | Aname s -> Format.pp_print_string ppf s

let pp_sep ppf () = Format.pp_print_string ppf ", "
let pp_args = Format.pp_print_list ~pp_sep pp_arg
let pp_ints = Format.pp_print_list ~pp_sep Format.pp_print_int

let pp ppf = function
  | Aligned None       -> Format.pp_print_string ppf "aligned"
  | Aligned (Some n)   -> Format.fprintf ppf "aligned(%d)" n
  | Packed             -> Format.pp_print_string ppf "packed"
  | Noreturn           -> Format.pp_print_string ppf "noreturn"
  | Always_inline      -> Format.pp_print_string ppf "always_inline"
  | Noinline           -> Format.pp_print_string ppf "noinline"
  | Pure               -> Format.pp_print_string ppf "pure"
  | Const              -> Format.pp_print_string ppf "const"
  | Malloc             -> Format.pp_print_string ppf "malloc"
  | Cold               -> Format.pp_print_string ppf "cold"
  | Hot                -> Format.pp_print_string ppf "hot"
  | Used               -> Format.pp_print_string ppf "used"
  | Unused             -> Format.pp_print_string ppf "unused"
  | Deprecated None    -> Format.pp_print_string ppf "deprecated"
  | Deprecated Some s  -> Format.fprintf ppf "deprecated(%S)" s
  | Warn_unused_result -> Format.pp_print_string ppf "warn_unused_result"
  | Returns_twice      -> Format.pp_print_string ppf "returns_twice"
  | Nothrow            -> Format.pp_print_string ppf "nothrow"
  | Section s          -> Format.fprintf ppf "section(%S)" s
  | Visibility v       -> Format.fprintf ppf "visibility(%S)" (string_of_visibility v)
  | Weak               -> Format.pp_print_string ppf "weak"
  | Alias s            -> Format.fprintf ppf "alias(%S)" s
  | Constructor None   -> Format.pp_print_string ppf "constructor"
  | Constructor Some n -> Format.fprintf ppf "constructor(%d)" n
  | Destructor None    -> Format.pp_print_string ppf "destructor"
  | Destructor Some n  -> Format.fprintf ppf "destructor(%d)" n
  | Transparent_union  -> Format.pp_print_string ppf "transparent_union"
  | May_alias          -> Format.pp_print_string ppf "may_alias"
  | Mode s             -> Format.fprintf ppf "mode(%s)" s
  | Nonnull []         -> Format.pp_print_string ppf "nonnull"
  | Nonnull l          -> Format.fprintf ppf "nonnull(%a)" pp_ints l
  | Format (a, f, v)   -> Format.fprintf ppf "format(%s, %d, %d)" a f v
  | Cleanup f          -> Format.fprintf ppf "cleanup(%s)" f
  | Other (nm, [])     -> Format.pp_print_string ppf nm
  | Other (nm, args)   -> Format.fprintf ppf "%s(%a)" nm pp_args args

(* Renders a non-empty set as a GNU `__attribute__((...))` specifier. *)
let pp_set ppf = function
  | [] -> ()
  | attrs ->
    Format.fprintf ppf "__attribute__((%a))"
      (Format.pp_print_list ~pp_sep pp) attrs

let pp_raw ppf {rname; rargs} = match rargs with
  | [] -> Format.pp_print_string ppf rname
  | _  -> Format.fprintf ppf "%s(%a)" rname
            (Format.pp_print_list ~pp_sep Expr.pp) rargs

let pp_raws ppf = function
  | [] -> ()
  | raws ->
    Format.fprintf ppf "__attribute__((%a))"
      (Format.pp_print_list ~pp_sep pp_raw) raws
