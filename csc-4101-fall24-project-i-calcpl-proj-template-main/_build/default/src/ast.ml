type bop = 
  | Add
  | Add_Float
  | Mult
  | Mult_Float
  | Geq
  | Leq
  | Sub
  | Sub_Float
  | Div
  | Div_Float

(* [typ] represents the type of an expression. *)
type typ =
  | TFloat
  | TInt
  | TBool

type expr = 
| Var of string
| Float of float
| Int of int
| Bool of bool
| Binop of bop * expr * expr
| Let of string * typ * expr * expr
| If of expr * expr * expr
