open Core

type op =
  | Clz
  | Ctz
  | Popcount
  | Bswap

type t = {
  operand : Texpr.ty;
  result  : Texpr.ty;
  op      : op;
}

let int_ = Type.int_ ()
let ushort = Type.short_ ~sign:Type.Sunsigned ()
let uint = Type.int_ ~sign:Type.Sunsigned ()
let ulong = Type.long_ ~sign:Type.Sunsigned ()
let ullong = Type.longlong_ ~sign:Type.Sunsigned ()

let count ~operand op = {operand; result = int_; op}
let swap ~ty = {operand = ty; result = ty; op = Bswap}

let table =
  String.Table.of_alist_exn [
    "__builtin_clz",        count ~operand:uint Clz;
    "__builtin_clzl",       count ~operand:ulong Clz;
    "__builtin_clzll",      count ~operand:ullong Clz;
    "__builtin_ctz",        count ~operand:uint Ctz;
    "__builtin_ctzl",       count ~operand:ulong Ctz;
    "__builtin_ctzll",      count ~operand:ullong Ctz;
    "__builtin_popcount",   count ~operand:uint Popcount;
    "__builtin_popcountl",  count ~operand:ulong Popcount;
    "__builtin_popcountll", count ~operand:ullong Popcount;
    "__builtin_bswap16",    swap ~ty:ushort;
    "__builtin_bswap32",    swap ~ty:uint;
    "__builtin_bswap64",    swap ~ty:ulong;
  ]

let find name = Hashtbl.find table name
