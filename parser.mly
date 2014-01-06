%{
  open Printf
  open Lexing
  open AbSyn

  let get_pos n =
    let p = Parsing.rhs_start_pos n in
    (p.pos_lnum, p.pos_cnum - p.pos_bol);;

  let parse_error s =
    let pos = Parsing.symbol_start_pos () in
    printf "%s [line %d, col %d]\n" s pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
    flush stdout;;
%}

%token NAME TYPE WHERE IF THEN ELSE MATCH WITH LET REC FUN IN FRESH SWAP
%token INT_T REAL_T BOOL_T STRING_T UNIT_T
%token L_PAREN R_PAREN
%token DONT_CARE  /* _ */
%token NEG        /* ~ */
%token EQUAL      /* = */
%token LT         /* < */
%token GT         /* > */
%token COMMA      /* , */
%token DBL_LT     /* << */
%token DBL_GT     /* >> */
%token UNIT       /* () */
%token ARROW      /* -> */
%token BAR        /* | */
%token COLON      /* : */
%token SEMI       /* ; */
%token DBL_SEMI   /* ;; */
%token PLUS
%token MINUS 
%token STAR
%token DIV
%token <string> ID
%token <int> INT
%token <float> REAL
%token <string> STRING
%token <bool> BOOL

%left EQUAL DBL_GT LT GT SEMI DBL_SEMI STAR PLUS MINUS DIV R_PAREN
%right DBL_LT ARROW L_PAREN

%start program 
%type <user_types list * exp list> program

%%

program:
  | user_types let_decs SEMI { ($1, $2) }
;

let_decs:
  | /* empty */ { [] }
  | LET dec IN exp let_decs { (Let($2, $4), get_pos 1)::$5 }
;

user_types:
  | /* empty */ { [] }
  | nty user_types { Ns($1)::$2 }
  | dty user_types { Ds($1)::$2 }
;

nty:
  | NAME id_list SEMI { $2 }
;

dty:
  | TYPE id_list WHERE ctor_list { ($2, $4) }
;

type_name:
  | INT_T  { IntT }
  | REAL_T { RealT }
  | BOOL_T { BoolT }
  | STRING_T { StringT }
  | ID { DataT($1) }   /* TODO how to distinguish between name and data types? -> Don't */
  | DBL_LT ID DBL_GT type_name { NameAbT($2, $4) }
  | UNIT_T { UnitT }
  | type_name STAR type_name { ProdT($1, $3) }
  | type_name ARROW type_name { FuncT($1, $3) }
;

id_list:
  | ID { [$1] }
  | ID COMMA id_list { $1::$3 }
;

ctor:
  | ID COLON type_name { ($1, $3) }
;

ctor_list:
  | ctor SEMI { [$1] }
  | ctor COMMA ctor_list { $1::$3 }
;

dec:
  | pattern EQUAL exp { ValBind($1, $3) }
  | ID L_PAREN ID COLON type_name R_PAREN COLON type_name EQUAL exp {
      RecFunc($1, $3, $5, $8, $10)
    }
;

pattern:
  | DONT_CARE { DontCareP }
  | ID { IdP($1) }
  | ID pattern { CtorP($1, $2) }
  | DBL_LT ID DBL_GT pattern { NameAbsP($2, $4) }
  | UNIT { UnitP }
  | L_PAREN pattern COMMA pattern R_PAREN { ProdP($2, $4) }
  | L_PAREN pattern R_PAREN { $2 }
;

exp:
  | ID { (Id $1, get_pos 1) }
  | ID exp { (Ctor($1, $2), get_pos 1) }
  | INT { (IntLiteral($1), get_pos 1) }
  | REAL { (RealLiteral($1), get_pos 1) }
  | BOOL { (BoolLiteral($1), get_pos 1) }
  | STRING { (StringLiteral($1), get_pos 1) }
  | FRESH COLON ID { (Fresh $3, get_pos 1) }
  | IF exp EQUAL exp THEN exp ELSE exp { (If($2, $4, $6, $8), get_pos 1) }
  | SWAP L_PAREN exp COMMA exp R_PAREN IN exp { (Swap($3, $5, $8), get_pos 1) }
  | DBL_LT exp DBL_GT exp { (NameAb($2, $4), get_pos 1) }
  | UNIT { (Unit, get_pos 1) }
  | L_PAREN exp COMMA exp R_PAREN { (Pair($2, $4), get_pos 1) }
  | FUN L_PAREN ID COLON type_name R_PAREN ARROW exp {
      (Lambda($3, $5, $8), get_pos 1)
    }
  | exp exp { (App($1, $2), get_pos 1) }
  | MATCH exp WITH branch { (Match($2, $4), get_pos 1) }
  | LET dec IN exp { (Let($2, $4), get_pos 1) }
  | L_PAREN exp R_PAREN { $2 }
;

branch:
  | BAR pattern ARROW exp { [($2, $4)] }
  | BAR pattern ARROW exp branch { ($2, $4)::$5 }
;

%%

