{
  open Query_parser
  exception SyntaxError of string

}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read =
  parse
  | white { read lexbuf }
  | "STOP" { STOP }
  | "RI" { REG_IMPL }
  | "RS" { REG_SPEC}
  | "RIS" { REGS_IMPL }
  | "RSS" { REGS_SPEC}
  | "@" { AT_SIGN }
  | "IMPL" { MID_IMPL }
  | "SPEC" { MID_SPEC }
  | "[" { LEFT_BRACK }
  | "]" { RIGHT_BRACK }
  | "(" { LEFT_PAREN }
  | ")" { RIGHT_PAREN }
  | "," { COMMA }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof { EOF }
