(* State shared between the parse driver and the generated parser's
   semantic actions.

   The parser builds each AST node's `Location.t` from the lexer's
   positions via the active source map. Like `Lexer_hack`, this is a
   single mutable cell reset per parse (the driver is single-threaded).
*)

open Core
open Cgen_utils

let source_map = ref (Source_map.create ())

(* Set when the declaration-specifiers currently being reduced include
   `typedef`, so that an init-declarator can register its name as a
   typedef (rather than a variable) the moment it is parsed. Declaration
   specifiers always reduce before their init-declarators. *)
let cur_typedef = ref false

(* Build a location spanning two lexing positions, used pervasively in
   the grammar's semantic actions as `loc $startpos $endpos`. *)
let loc startp endp = Source_map.location_of !source_map startp endp

(* Fresh synthetic tag for an anonymous struct/union/enum. *)
let anon_counter = ref 0

let fresh_anon_tag kind =
  incr anon_counter;
  Format.sprintf "__anon_%s_%d" kind !anon_counter
