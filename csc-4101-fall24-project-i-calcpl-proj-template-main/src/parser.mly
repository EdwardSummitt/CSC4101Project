%{
open Ast
%}

%token <float> FLOAT
%token <int> INT
%token <string> ID
%token TRUE
%token FALSE
%token GEQ
%token LEQ
%token TIMES_FLOAT
%token TIMES
%token DIVIDE_FLOAT
%token DIVIDE
%token PLUS_FLOAT
%token PLUS
%token MINUS_FLOAT
%token MINUS
%token LPAREN
%token RPAREN
%token LET
%token EQUALS
%token IN
%token IF
%token THEN
%token ELSE
%token COLON
%token FLOAT_TYPE
%token INT_TYPE
%token BOOL_TYPE
%token EOF

%nonassoc IN
%nonassoc ELSE
%left LEQ
%left GEQ
%left PLUS MINUS PLUS_FLOAT MINUS_FLOAT
%left TIMES DIVIDE TIMES_FLOAT DIVIDE_FLOAT


%start <Ast.expr> prog

%%

prog:
	| e = expr; EOF { e }
	;
	
expr:
	| f = FLOAT { Float f }
	| i = INT { Int i }
  	| x = ID { Var x }
  	| TRUE { Bool true }
  	| FALSE { Bool false }
	| e1 = expr; GEQ; e2 = expr { Binop (Geq, e1, e2) }
  	| e1 = expr; LEQ; e2 = expr { Binop (Leq, e1, e2) }
	| e1 = expr; TIMES_FLOAT; e2 = expr { Binop (Mult_Float, e1, e2)}
  	| e1 = expr; TIMES; e2 = expr { Binop (Mult, e1, e2) }
	| e1 = expr; DIVIDE_FLOAT; e2 = expr { Binop (Div_Float, e1, e2)}
	| e1 = expr; DIVIDE; e2 = expr { Binop (Div, e1, e2) }
	| e1 = expr; PLUS_FLOAT; e2 = expr { Binop (Add_Float, e1, e2) }
  	| e1 = expr; PLUS; e2 = expr { Binop (Add, e1, e2) }
	| e1 = expr; MINUS_FLOAT; e2 = expr { Binop (Sub_Float, e1, e2) }
	| e1 = expr; MINUS; e2 = expr { Binop (Sub, e1, e2) }
  	| LET; x = ID; COLON; t = typ; EQUALS; e1 = expr; IN; e2 = expr 
		{ Let (x, t, e1, e2) }
  	| IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { If (e1, e2, e3) }
  	| LPAREN; e=expr; RPAREN {e}
	;

typ: 
	| FLOAT_TYPE { TFloat }
	| INT_TYPE { TInt }
	| BOOL_TYPE { TBool }
