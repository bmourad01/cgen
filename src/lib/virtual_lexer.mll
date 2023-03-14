{
  open Lexing
  open Virtual_parser

  let string_buff = Buffer.create 256

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
let double = digit+ '.' digit+
let single = double 'f'
let backslash_escapes = ['\\' '\'' '"' 'n' 't' 'b' 'r' ' ']
let imm = ['w' 'l' 'b' 'h']
let fp = ['s' 'd']
let basic = (imm | fp)
let special = ['m' 'f']
let typ = (basic | special)

rule token = parse
  | '\n' { newline lexbuf; token lexbuf }
  | space { token lexbuf }
  | '+' { PLUS }
  | '-' { MINUS }
  | ':' (ident as id) { TYPENAME id }
  | ':' { COLON }
  | '$' (ident as id) { SYM id }
  | '@' (ident as id) { LABEL id }
  | '@' (integer as id) { LABEL id }
  | '%' (ident as id) '.' (integer as i) { VAR (id, int_of_string i) }
  | '%' (ident as id) { IDENT id }
  | '%' (integer as id) { TEMP (int_of_string id) }
  | '%' (integer as id) '.' (integer as i) {
    TEMPI (int_of_string id, int_of_string i)
  }
  | "module" space+ (ident as id) { MODULE id }
  | "align" { ALIGN }
  | "type" { TYPE }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LSQUARE }
  | ']' { RSQUARE }
  | ',' { COMMA }
  | '=' { EQUALS }
  | "->" { ARROW }
  | "..." { ELIPSIS }
  | 'w' { W }
  | 'l' { L }
  | 'b' { B }
  | 'h' { H }
  | 's' { S }
  | 'd' { D }
  | 'z' { Z }
  | 'm' { M }
  | 'f' { F }
  | "add" '.' (basic as t) { ADD (basic_of_char t) }
  | "div" '.' (basic as t) { DIV (basic_of_char t) }
  | "mul" '.' (basic as t) { MUL (basic_of_char t) }
  | "rem" '.' (basic as t) { REM (basic_of_char t) }
  | "sub" '.' (basic as t) { SUB (basic_of_char t) }
  | "udiv" '.' (imm as t) { UDIV (imm_of_char t) }
  | "urem" '.' (imm as t) { UREM (imm_of_char t) }
  | "neg" '.' (basic as t) { NEG (basic_of_char t) }
  | "and" '.' (imm as t) { AND (imm_of_char t) }
  | "or" '.' (imm as t) { OR (imm_of_char t) }
  | "sar" '.' (imm as t) { SAR (imm_of_char t) }
  | "shl" '.' (imm as t) { SHL (imm_of_char t) }
  | "shr" '.' (imm as t) { SHR (imm_of_char t) }
  | "xor" '.' (imm as t) { XOR (imm_of_char t) }
  | "not" '.' (imm as t) { NOT (imm_of_char t) }
  | "alloc" { ALLOC }
  | "ld" '.' (basic as t) { LOAD (basic_of_char t) }
  | "st" '.' (basic as t) { STORE (basic_of_char t) }
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
  | "bits" '.' (basic as t) { BITS (basic_of_char t) }
  | "ftosi" '.' (fp as t) '.' (imm as i) {
    FTOSI (fp_of_char t, imm_of_char i)
  }
  | "ftoui" '.' (fp as t) '.' (imm as i) {
    FTOUI (fp_of_char t, imm_of_char i)
  }
  | "ftrunc" '.' (fp as t) { FTRUNC (fp_of_char t) }
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
  | "select" '.' (basic as t) { SELECT (basic_of_char t) }
  | "call" '.' (basic as t) { ACALL (basic_of_char t) }
  | "call" { CALL }
  | "vastart" { VASTART }
  | "hlt" { HLT }
  | "jmp" { JMP }
  | "jnz" { JNZ }
  | "ret" { RET }
  | "switch" '.' (imm as t) { SWITCH (imm_of_char t) }
  | "function" { FUNCTION }
  | "data" { DATA }
  | "export" { EXPORT }
  | "section" { SECTION }
  | "noreturn" { NORETURN }
  | '"' {
    Buffer.clear string_buff;
    string lexbuf;
    STRING (Buffer.contents string_buff)
  }
  | eof { EOF }
  | integer as i { INT (Bitvec.of_string i) }
  | ninteger as n { INT (Bitvec.of_string n) }
  | hinteger as h { INT (Bitvec.of_string h) }
  | ointeger as o { INT (Bitvec.of_string o) }
  | binteger as b { INT (Bitvec.of_string b) }
  | double as d { DOUBLE (Float.of_string d) }
  | single as s { SINGLE (Float32.of_string s) }
  | _ { raise Error }

and string = parse
  | '"' { () }
  | '\\' (backslash_escapes as c) {
    Buffer.add_char string_buff (char_for_backslash c);
    string lexbuf
  }
  | _ as c {
    Buffer.add_char string_buff c;
    string lexbuf
  }
