open Core
open Regular.Std

include Var_internal

let is_temp x = match x with
  | Temp _ -> true
  | Name _ -> false

let is_named x = match x with
  | Temp _ -> false
  | Name _ -> true

let name x = match x with
  | Temp _ -> None
  | Name (n, _) -> Some n

let index x = match x with
  | Temp (_, i) | Name (_, i) -> i

let with_index x i = match x with
  | Temp (t, _) -> Temp (t, i)
  | Name (n, _) -> Name (n, i)

let base x = with_index x 0

let same x y = match x, y with
  | Temp (ix, _), Temp (iy, _) -> Int63.(ix = iy)
  | Name (nx, _), Name (ny, _) -> String.(nx = ny)
  | _ -> false

let valid_first_char = function
  | '0'..'9' | '%' | '@' | '$' -> false
  | _ -> true

let mangle = function
  | "" -> "_"
  | s when valid_first_char s.[0] -> s
  | s -> "_" ^ s

let create ?(index = 0) name = Name (mangle name, index)

let pp ppf x = match x with
  | Temp (id, 0) -> Format.fprintf ppf "%%%a" Int63.pp id
  | Temp (id, index) -> Format.fprintf ppf "%%%a.%u" Int63.pp id index
  | Name (n, 0) -> Format.fprintf ppf "%%%s" n
  | Name (n, index) -> Format.fprintf ppf "%%%s.%u" n index

include Regular.Make(struct
    include Var_internal
    let pp = pp
    let version = "0.1"
    let hash = hash
    let module_name = Some "Cgen.Var"
  end)
