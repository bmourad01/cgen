{
  open Lexing
  open C_parser

  (* Raised on a lexing error; the parse driver turns it into a
     diagnostic carrying the current position. *)
  exception Lex_error of string

  (* Advance the position past a newline that was just consumed. *)
  let newline lexbuf =
    let p = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {
      p with
      pos_lnum = p.pos_lnum + 1;
      pos_bol = p.pos_cnum;
    }

  (* Apply a preprocessor line marker (`# N "file"` or `#line N "file"`)
     consumed up to and including its terminating newline: the next line
     is line `n` of `file`. *)
  let set_line lexbuf n file =
    let p = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {
      p with
      pos_fname = (match file with Some f -> f | None -> p.pos_fname);
      pos_lnum = n;
      pos_bol = p.pos_cnum;
    }

  (* C simple escape sequences (§6.4.4.4); the octal/hex forms are
     handled separately. *)
  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | 'f' -> '\012'
    | 'v' -> '\011'
    | 'a' -> '\007'
    | c   -> c   (* backslash, single-quote, double-quote, question mark *)

  let char_of_code n = Char.chr (n land 0xff)

  (* The integer-suffix as written, canonicalized (§6.4.4.1). *)
  let int_suffix s =
    let s = String.lowercase_ascii s in
    let has_u = String.contains s 'u' in
    let ls = String.fold_left (fun n c -> if c = 'l' then n + 1 else n) 0 s in
    match has_u, ls with
    | false, 0 -> None
    | true,  0 -> Some `u
    | false, 1 -> Some `l
    | true,  1 -> Some `ul
    | false, _ -> Some `ll
    | true,  _ -> Some `ull

  (* Parse an integer token (digits plus an optional u/l suffix) into an
     `Expr.const`. *)
  let int_const tok =
    let n = String.length tok in
    let i = ref n in
    let ok_suff () = match tok.[!i - 1] with
      | 'u' | 'U' | 'l' | 'L' -> true
      | _ -> false in
    while !i > 0 && ok_suff () do decr i done;
    let num = String.sub tok 0 !i in
    let suf = String.sub tok !i (n - !i) in
    let len = String.length num in
    let base, value =
      if len >= 2 && num.[0] = '0' && (num.[1] = 'x' || num.[1] = 'X')
      then `hex, Cgen.Bv.of_string_base 16 (String.sub num 2 (len - 2))
      else if len >= 2 && num.[0] = '0' && (num.[1] = 'b' || num.[1] = 'B')
      then `bin, Cgen.Bv.of_string_base 2 (String.sub num 2 (len - 2))
      else if len >= 2 && num.[0] = '0'
      then `oct, Cgen.Bv.of_string_base 8 num
      else `dec, Cgen.Bv.of_string_base 10 num in
    Expr.Cint {value; suffix = int_suffix suf; base}
}

let digit = ['0'-'9']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']
let octdigit = ['0'-'7']
let alpha = ['a'-'z' 'A'-'Z' '_']
let ident = alpha (alpha | digit)*

let hexnum = '0' ['x' 'X'] hexdigit+
let binnum = '0' ['b' 'B'] ['0'-'1']+
let octnum = '0' octdigit*
let decnum = ['1'-'9'] digit*
let isuf = ['u' 'U' 'l' 'L']*

let exp = ['e' 'E'] ['+' '-']? digit+
let fnum = (digit* '.' digit+ | digit+ '.') exp? | digit+ exp

(* Hexadecimal floating constants (§6.4.4.2): a hex mantissa (with an optional
   point) followed by a mandatory binary exponent whose digits are decimal,
   e.g. `0x1.8p3`, `0x1p-100`, `0x.8p1`. The value still round-trips through
   `float_of_string` / `Float32.of_string`, which accept this syntax. *)
let binexp = ['p' 'P'] ['+' '-']? digit+
let hexfnum = '0' ['x' 'X'] (hexdigit* '.' hexdigit+ | hexdigit+ '.'?) binexp

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n' { newline lexbuf; token lexbuf }
  | "/*" { block_comment lexbuf; token lexbuf }
  | "//" [^ '\n']* { token lexbuf }

  (* GNU line marker: `# N "file" flags...` *)
  | '#' [' ' '\t']* (digit+ as n) [' ' '\t']+ '"' ([^ '"' '\n']* as f) '"' [^ '\n']* '\n'
    { set_line lexbuf (int_of_string n) (Some f); token lexbuf }
  (* `#line N "file"` *)
  | '#' [' ' '\t']* "line" [' ' '\t']+ (digit+ as n) [' ' '\t']+ '"' ([^ '"' '\n']* as f) '"' [^ '\n']* '\n'
    { set_line lexbuf (int_of_string n) (Some f); token lexbuf }
  (* `#line N` *)
  | '#' [' ' '\t']* "line" [' ' '\t']+ (digit+ as n) [^ '\n']* '\n'
    { set_line lexbuf (int_of_string n) None; token lexbuf }
  (* Any other directive that survived preprocessing (e.g. #pragma). *)
  | '#' [^ '\n']* '\n' { newline lexbuf; token lexbuf }

  (* Keywords. *)
  | "auto" { AUTO }
  | "break" { BREAK }
  | "case" { CASE }
  | "char" { CHAR }
  | "const" { CONST }
  | "continue" { CONTINUE }
  | "default" { DEFAULT }
  | "do" { DO }
  | "double" { DOUBLE }
  | "else" { ELSE }
  | "enum" { ENUM }
  | "extern" { EXTERN }
  | "float" { FLOAT }
  | "for" { FOR }
  | "goto" { GOTO }
  | "if" { IF }
  | "inline" | "__inline" | "__inline__" { INLINE }
  | "int" { INT }
  | "long" { LONG }
  | "register" { REGISTER }
  | "restrict" | "__restrict" | "__restrict__" { RESTRICT }
  | "return" { RETURN }
  | "short" { SHORT }
  | "signed" { SIGNED }
  | "sizeof" { SIZEOF }
  | "static" { STATIC }
  | "struct" { STRUCT }
  | "switch" { SWITCH }
  | "typedef" { TYPEDEF }
  | "union" { UNION }
  | "unsigned" { UNSIGNED }
  | "void" { VOID }
  | "volatile" { VOLATILE }
  | "while" { WHILE }
  | "_Bool" { BOOL }
  | "_Noreturn" { NORETURN }
  | "_Thread_local" { THREAD_LOCAL }

  (* Floating constants. The hex forms must out-munch the `0x…` integer rule,
     which longest match guarantees since they consume the binary exponent. *)
  | (hexfnum as f) ['f' 'F'] { CONSTANT (Expr.Cfloat (Cgen_utils.Float32.of_string f)) }
  | (hexfnum as f) ['l' 'L'] { CONSTANT (Expr.Cdouble (float_of_string f)) }
  | (hexfnum as f) { CONSTANT (Expr.Cdouble (float_of_string f)) }
  | (fnum as f) ['f' 'F'] { CONSTANT (Expr.Cfloat (Cgen_utils.Float32.of_string f)) }
  | (fnum as f) ['l' 'L'] { CONSTANT (Expr.Cdouble (float_of_string f)) }
  | (fnum as f) { CONSTANT (Expr.Cdouble (float_of_string f)) }

  (* Integer constants. *)
  | (hexnum isuf) as tok { CONSTANT (int_const tok) }
  | (binnum isuf) as tok { CONSTANT (int_const tok) }
  | (octnum isuf) as tok { CONSTANT (int_const tok) }
  | (decnum isuf) as tok { CONSTANT (int_const tok) }

  (* Character constants. *)
  | "'" '\\' 'x' (hexdigit+ as h) "'"
    { CONSTANT (Expr.Cchar (char_of_code (int_of_string ("0x" ^ h)))) }
  | "'" '\\' (octdigit+ as o) "'"
    { CONSTANT (Expr.Cchar (char_of_code (int_of_string ("0o" ^ o)))) }
  | "'" '\\' (_ as e) "'"
    { CONSTANT (Expr.Cchar (char_for_backslash e)) }
  | "'" ([^ '\\' '\'' '\n'] as c) "'"
    { CONSTANT (Expr.Cchar c) }

  (* String literals. *)
  | '"'
    { 
      (* The string sub-rule re-matches lexemes, each clobbering
         lex_start_p; save the opening quote's position and restore
         it so the STRING token spans from the opening quote. *)
      let start = lexbuf.lex_start_p in
      let buf = Buffer.create 32 in
      string buf lexbuf;
      lexbuf.lex_start_p <- start;
      STRING (Buffer.contents buf)
    }

  (* Punctuation and operators (multi-char before single-char). *)
  | "..." { ELLIPSIS }
  | "->" { ARROW }
  | "++" { INCR }
  | "--" { DECR }
  | "<<=" { SHL_ASSIGN }
  | ">>=" { SHR_ASSIGN }
  | "<<" { SHL }
  | ">>" { SHR }
  | "<=" { LE }
  | ">=" { GE }
  | "==" { EQ }
  | "!=" { NE }
  | "&&" { ANDAND }
  | "||" { OROR }
  | "+=" { ADD_ASSIGN }
  | "-=" { SUB_ASSIGN }
  | "*=" { MUL_ASSIGN }
  | "/=" { DIV_ASSIGN }
  | "%=" { MOD_ASSIGN }
  | "&=" { AND_ASSIGN }
  | "|=" { OR_ASSIGN }
  | "^=" { XOR_ASSIGN }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | ";" { SEMI }
  | "," { COMMA }
  | "." { DOT }
  | ":" { COLON }
  | "?" { QUESTION }
  | "=" { ASSIGN }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { STAR }
  | "/" { SLASH }
  | "%" { PERCENT }
  | "&" { AMP }
  | "|" { PIPE }
  | "^" { CARET }
  | "~" { TILDE }
  | "!" { BANG }
  | "<" { LT }
  | ">" { GT }

  | ident as name
    {
      (* Compiler builtins live in the reserved `__builtin_` namespace.

         `__builtin_va_arg` needs bespoke grammar (a type argument), so it
         gets its own token.

         `__builtin_va_list` is a predefined typedef (seeded at parse start),
         so the typedef check below catches it.

         Every other `__builtin_*` is an ordinary-looking call handled
         generically via the `BUILTIN` token.
      *)
      match name with
      | "__builtin_va_arg" -> BUILTIN_VA_ARG
      | _ when Lexer_hack.is_typedef name -> TYPEDEF_NAME name
      | _ when String.starts_with ~prefix:"__builtin_" name -> BUILTIN name
      | _ -> IDENT name
    }

  | eof { EOF }
  | _ as c { raise (Lex_error (Printf.sprintf "unexpected character %C" c)) }

(* Block comments do not nest in C; track newlines so positions stay
   accurate. *)
and block_comment = parse
  | "*/" { () }
  | '\n' { newline lexbuf; block_comment lexbuf }
  | eof { raise (Lex_error "unterminated comment") }
  | _ { block_comment lexbuf }

and string buf = parse
  | '"' { () }
  | '\\' 'x' (hexdigit+ as h)
    {
      Buffer.add_char buf (char_of_code (int_of_string ("0x" ^ h)));
      string buf lexbuf
    }
  | '\\' (octdigit+ as o)
    {
      Buffer.add_char buf (char_of_code (int_of_string ("0o" ^ o)));
      string buf lexbuf
    }
  | '\\' (_ as e)
    {
      Buffer.add_char buf (char_for_backslash e);
      string buf lexbuf
    }
  | '\n' 
    {
      newline lexbuf;
      Buffer.add_char buf '\n';
      string buf lexbuf
    }
  | [^ '"' '\\' '\n']+ as s
    {
      Buffer.add_string buf s;
      string buf lexbuf
    }
  | eof { raise (Lex_error "unterminated string literal") }
