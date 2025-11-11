{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let float = '-'? digit+ '.' digit+
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read = 
  parse
  | white { read lexbuf }
  | "true" { TRUE }
  | "false" { FALSE }
  | "=>" { GEQ }
  | "<=" { LEQ }
  | "*" { TIMES }
  | "*." { TIMES_FLOAT }
  | "/" { DIVIDE }
  | "/." { DIVIDE_FLOAT }
  | "+" { PLUS }
  | "+." { PLUS_FLOAT }
  | "-" { MINUS }
  | "-." { MINUS_FLOAT }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "let" { LET }
  | "=" { EQUALS }
  | "in" { IN }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | ":" {COLON}
  | "int" {INT_TYPE}
  | "float" {FLOAT_TYPE}
  | "bool" {BOOL_TYPE}
  | id { ID (Lexing.lexeme lexbuf) }
  | float { FLOAT (float_of_string (Lexing.lexeme lexbuf))}
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }

