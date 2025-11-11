
(* The type of tokens. *)

type token = 
  | TRUE
  | TIMES_FLOAT
  | TIMES
  | THEN
  | RPAREN
  | PLUS_FLOAT
  | PLUS
  | MINUS_FLOAT
  | MINUS
  | LPAREN
  | LET
  | LEQ
  | INT_TYPE
  | INT of (int)
  | IN
  | IF
  | ID of (string)
  | GEQ
  | FLOAT_TYPE
  | FLOAT of (float)
  | FALSE
  | EQUALS
  | EOF
  | ELSE
  | DIVIDE_FLOAT
  | DIVIDE
  | COLON
  | BOOL_TYPE

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
