(* The "lexer hack" state shared between the C lexer and parser.

   C is not context-free at the token level: in `A * B;`, whether `A` is
   a type (making this a declaration) or a value (making it a
   multiplication expression statement) depends on whether `A` was
   introduced by a `typedef`. The lexer therefore emits `TYPEDEF_NAME`
   for identifiers currently bound as typedef names and `IDENT`
   otherwise, consulting the scoped table maintained here.

   Parser semantic actions keep the table in sync: they register typedef
   names as declarators are reduced, shadow them with ordinary
   identifiers where the same name is redeclared as a variable, and
   push/pop scopes at block, function, prototype, and struct/union
   boundaries.

   This is a single mutable stack, reset at the start of each parse. It
   is not thread-safe, which matches the single-threaded parser driver.
*)

open Core

(* Each scope maps a name to whether it currently denotes a typedef.

   An ordinary-identifier binding records `false` so it shadows an
   outer typedef of the same name (C99 §6.2.1).
*)
type scope = bool String.Table.t

(* Innermost scope at the head.

   Never empty between `reset` calls. The file scope sits at the bottom.
*)
let scopes : scope list ref = ref [String.Table.create ()]

let reset () = scopes := [String.Table.create ()]
let push_scope () = scopes := String.Table.create () :: !scopes

let pop_scope () = match !scopes with
  | [] | [_] ->
    (* The file scope must remain; a stray pop is a parser bug. *)
    failwith "Lexer_hack.pop_scope: no enclosing scope"
  | _ :: rest -> scopes := rest

let define ~is_typedef name = match !scopes with
  | [] -> failwith "Lexer_hack.define: no scope"
  | scope :: _ -> Hashtbl.set scope ~key:name ~data:is_typedef

let define_typedef name = define ~is_typedef:true name
let define_var name = define ~is_typedef:false name

(* Resolve a name innermost-out.

   The first scope that binds it decides, so a variable binding
   shadows an outer typedef. An unbound name is not a typedef.
*)
let is_typedef name =
  List.find_map !scopes ~f:(fun scope -> Hashtbl.find scope name) |>
  Option.value ~default:false
