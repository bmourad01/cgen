open Core

type op =
  | Clz
  | Ctz
  | Popcount
  | Bswap

type prim = {
  operand : Texpr.ty;
  result  : Texpr.ty;
  op      : op;
}

type t =
  | Prim of prim
  | Parity of string
  | Ffs of string
  | Expect

let int_ = Type.int_ ()
let ushort = Type.short_ ~sign:Type.Sunsigned ()
let uint = Type.int_ ~sign:Type.Sunsigned ()
let ulong = Type.long_ ~sign:Type.Sunsigned ()
let ullong = Type.longlong_ ~sign:Type.Sunsigned ()

let count ~operand op = {operand; result = int_; op}
let swap ~ty = {operand = ty; result = ty; op = Bswap}

let table =
  String.Table.of_alist_exn [
    "__builtin_clz",        Prim (count ~operand:uint Clz);
    "__builtin_clzl",       Prim (count ~operand:ulong Clz);
    "__builtin_clzll",      Prim (count ~operand:ullong Clz);
    "__builtin_ctz",        Prim (count ~operand:uint Ctz);
    "__builtin_ctzl",       Prim (count ~operand:ulong Ctz);
    "__builtin_ctzll",      Prim (count ~operand:ullong Ctz);
    "__builtin_popcount",   Prim (count ~operand:uint Popcount);
    "__builtin_popcountl",  Prim (count ~operand:ulong Popcount);
    "__builtin_popcountll", Prim (count ~operand:ullong Popcount);
    "__builtin_bswap16",    Prim (swap ~ty:ushort);
    "__builtin_bswap32",    Prim (swap ~ty:uint);
    "__builtin_bswap64",    Prim (swap ~ty:ulong);
    "__builtin_parity",     Parity "__builtin_popcount";
    "__builtin_parityl",    Parity "__builtin_popcountl";
    "__builtin_parityll",   Parity "__builtin_popcountll";
    "__builtin_ffs",        Ffs "__builtin_ctz";
    "__builtin_ffsl",       Ffs "__builtin_ctzl";
    "__builtin_ffsll",      Ffs "__builtin_ctzll";
    "__builtin_expect",     Expect;
  ]

let find name = Hashtbl.find table name

let prim_exn name = match find name with
  | Some (Prim p) -> p
  | _ -> failwithf "Builtins.prim_exn: '%s' is not a primitive builtin" name ()
