{
  open Lexing
  open Structured_parser

  let char_for_backslash = function
    | 'n' -> '\010'
    | 'r' -> '\013'
    | 'b' -> '\008'
    | 't' -> '\009'
    | c   -> c

  let newline lexbuf =    
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- {
      pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }

  let imm_of_char : char -> Type.imm = function
    | 'w' -> `i32
    | 'l' -> `i64
    | 'b' -> `i8
    | 'h' -> `i16
    | _ -> raise Error

  let imm_base_of_char : char -> Type.imm_base = function
    | 'w' -> `i32
    | 'l' -> `i64
    | _ -> raise Error

  let fp_of_char : char -> Type.fp = function
    | 's' -> `f32
    | 'd' -> `f64
    | _ -> raise Error
   
  let basic_of_char : char -> Type.basic = function
    | ('w' | 'l' | 'b' | 'h') as c -> (imm_of_char c :> Type.basic)
    | ('s' | 'd') as c -> (fp_of_char c :> Type.basic)
    | _ -> raise Error
}

let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha | '_') (alpha | '_' | digit)*
let integer = digit+
let ninteger = '-' integer
let hinteger = "0x" ['0'-'9' 'a'-'f' 'A'-'F']+
let ointeger = "0o" ['0'-'7']+
let binteger = "0b" ['0'-'1']+
let posints = (integer | hinteger | ointeger | binteger)
let exp = ('E' | 'e') (integer | ninteger)
let inf = ("INF" | "inf" | "INFINITY" | "infinity")
let nan = ("NAN" | "NaN" | "nan")
let flt = ('-'? digit+ '.' digit+ exp?) | ('-'? inf) | ('-'? nan)
let backslash_escapes = ['\\' '\'' '"' 'n' 't' 'b' 'r']
let imm = ['w' 'l' 'b' 'h']
let imm_base = ['w' 'l']
let fp = ['s' 'd']
let basic = (imm | fp)
let special = ['m' 'f']
let typ = (basic | special)

rule token = parse
  | "/*" { block_comment 0 lexbuf; token lexbuf }
  | "//" { line_comment lexbuf; token lexbuf }
  | '\n' { newline lexbuf; token lexbuf }
  | space { token lexbuf }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '+' { PLUS }
  | '-' { MINUS }
  | ':' (ident as id) { TYPENAME id }
  | ':' { COLON }
  | ';' { SEMI }
  | '$' (ident as id) { SYM id }
  | '@' (ident as id) { LABEL id }
  | '@' (integer as id) { LABEL id }
  | '%' (ident as id) '.' (integer as i) { VAR (id, int_of_string i) }
  | '%' (ident as id) { IDENT id }
  | '%' (integer as id) { TEMP id }
  | '%' (integer as id) '.' (integer as i) { TEMPI (id, int_of_string i) }
  | "module" space+ (ident as id) { MODULE id }
  | "align" { ALIGN }
  | "const" { CONST () }
  | "type" { TYPE }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | ',' { COMMA }
  | '=' { EQUALS }
  | "..." { ELLIPSIS }
  | "sb" { SB }
  | "sh" { SH }
  | "sw" { SW }
  | 'w' { W }
  | 'l' { L }
  | 'b' { B }
  | 'h' { H }
  | 's' { S }
  | 'd' { D }
  | 'z' { Z }
  | "nop" { NOP }
  | "add" '.' (basic as t) { ADD (basic_of_char t) }
  | "div" '.' (basic as t) { DIV (basic_of_char t) }
  | "mul" '.' (basic as t) { MUL (basic_of_char t) }
  | "mulh" '.' (imm as t) { MULH (imm_of_char t) }
  | "umulh" '.' (imm as t) { UMULH (imm_of_char t) }
  | "rem" '.' (imm as t) { REM (imm_of_char t) }
  | "sub" '.' (basic as t) { SUB (basic_of_char t) }
  | "udiv" '.' (imm as t) { UDIV (imm_of_char t) }
  | "urem" '.' (imm as t) { UREM (imm_of_char t) }
  | "neg" '.' (basic as t) { NEG (basic_of_char t) }
  | "and" '.' (imm as t) { AND (imm_of_char t) }
  | "or" '.' (imm as t) { OR (imm_of_char t) }
  | "asr" '.' (imm as t) { ASR (imm_of_char t) }
  | "lsl" '.' (imm as t) { LSL (imm_of_char t) }
  | "lsr" '.' (imm as t) { LSR (imm_of_char t) }
  | "rol" '.' (imm as t) { ROL (imm_of_char t) }
  | "ror" '.' (imm as t) { ROR (imm_of_char t) }
  | "xor" '.' (imm as t) { XOR (imm_of_char t) }
  | "clz" '.' (imm as t) { CLZ (imm_of_char t) }
  | "ctz" '.' (imm as t) { CTZ (imm_of_char t) }
  | "popcnt" '.' (imm as t) { POPCNT (imm_of_char t) }
  | "not" '.' (imm as t) { NOT (imm_of_char t) }
  | "slot" { SLOT }
  | "ld" '.' (basic as t) { LOAD (basic_of_char t :> Type.arg) }
  | "ld" ':' (ident as id) { LOAD (`name id) }
  | "st" '.' (basic as t) { STORE (basic_of_char t :> Type.arg) }
  | "st" ':' (ident as id) { STORE (`name id) }
  | "eq" '.' (basic as t) { EQ (basic_of_char t) }
  | "ge" '.' (basic as t) { GE (basic_of_char t) }
  | "gt" '.' (basic as t) { GT (basic_of_char t) }
  | "le" '.' (basic as t) { LE (basic_of_char t) }
  | "lt" '.' (basic as t) { LT (basic_of_char t) }
  | "ne" '.' (basic as t) { NE (basic_of_char t) }
  | "o" '.' (fp as t) { O (fp_of_char t) }
  | "sge" '.' (imm as t) { SGE (imm_of_char t) }
  | "sgt" '.' (imm as t) { SGT (imm_of_char t) }
  | "sle" '.' (imm as t) { SLE (imm_of_char t) }
  | "slt" '.' (imm as t) { SLT (imm_of_char t) }
  | "uo" '.' (fp as t) { UO (fp_of_char t) }
  | "fext" '.' (fp as t) { FEXT (fp_of_char t) }
  | "fibits" '.' (fp as t) { FEXT (fp_of_char t) }
  | "flag" '.' (imm as t) { FLAG (imm_of_char t) }
  | "ftosi" '.' (fp as t) '.' (imm as i) {
    FTOSI (fp_of_char t, imm_of_char i)
  }
  | "ftoui" '.' (fp as t) '.' (imm as i) {
    FTOUI (fp_of_char t, imm_of_char i)
  }
  | "ftrunc" '.' (fp as t) { FTRUNC (fp_of_char t) }
  | "ifbits" '.' (imm_base as t) { IFBITS (imm_base_of_char t) }
  | "itrunc" '.' (imm as t) { ITRUNC (imm_of_char t) }
  | "sext" '.' (imm as t) { SEXT (imm_of_char t) }
  | "sitof" '.' (imm as t) '.' (fp as f) {
    SITOF (imm_of_char t, fp_of_char f)
  }
  | "uitof" '.' (imm as t) '.' (fp as f) {
    UITOF (imm_of_char t, fp_of_char f)
  }
  | "zext" '.' (imm as t) { ZEXT (imm_of_char t) }
  | "copy" '.' (basic as t) { COPY (basic_of_char t) }
  | "sel" '.' (basic as t) { SEL (basic_of_char t) }
  | "call" '.' (basic as t) { ACALL (basic_of_char t :> Type.ret) }
  | "call" '.' "sb" { ACALL `si8 }
  | "call" '.' "sh" { ACALL `si16 }
  | "call" '.' "sw" { ACALL `si32 }
  | "call" ':' (ident as id) { ACALL (`name id) }
  | "call" { CALL }
  | "start" { START}
  | "vaarg" '.' (basic as t) { VAARG (basic_of_char t :> Type.arg) }
  | "vaarg" ':' (ident as id) { VAARG (`name id) }
  | "vastart" { VASTART }
  | "hlt" { HLT }
  | "goto" { GOTO }
  | "break" { BREAK }
  | "continue" { CONTINUE }
  | "if" { IF }
  | "unless" { UNLESS }
  | "when" { WHEN }
  | "else" { ELSE }
  | "ret" { RET }
  | "loop" { LOOP }
  | "while" { WHILE }
  | "do" { DO }
  | "switch" '.' (imm as t) { SWITCH (imm_of_char t) }
  | "case" { CASE }
  | "default" { DEFAULT }
  | "function" { FUNCTION }
  | "data" { DATA }
  | "export" { EXPORT }
  | "section" { SECTION }
  | "noreturn" { NORETURN }
  | '"' {
    let buf = Buffer.create 64 in
    string buf lexbuf;
    STRING (Buffer.contents buf)
  }
  | eof { EOF }
  | (posints as i) '_' (imm as t) {
    let i = Z.of_string i in
    let t = imm_of_char t in
    INT (Bv.bigint_unsafe i, t)
  }
  | posints as i {
    let i = Z.of_string i in
    NUM (Bv.bigint_unsafe i)
  }
  | (flt as f) "_d" { DOUBLE (Float.of_string f) }
  | (flt as f) "_s" { SINGLE (Float32.of_string f) }
  | "true" { BOOL true }
  | "false" { BOOL false }
  | _ { raise Error }

and string buf = parse
  | '"' { () }
  | '\\' (backslash_escapes as c) {
    Buffer.add_char buf (char_for_backslash c);
    string buf lexbuf
  }
  | eof { raise Error }
  | _ as c {
    Buffer.add_char buf c;
    string buf lexbuf
  }

and block_comment depth = parse
  | "/*" { block_comment (depth + 1) lexbuf }
  | "*/" { if depth > 0 then block_comment (depth - 1) lexbuf }
  | '\n' { newline lexbuf; block_comment depth lexbuf }
  | eof { raise Error }
  | _ { block_comment depth lexbuf }

and line_comment = parse
  | '\n' { newline lexbuf }
  | eof { () }
  | _ { line_comment lexbuf }
