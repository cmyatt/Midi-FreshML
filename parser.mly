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

  let types = Hashtbl.create 50;; (* key: type name, val: actual type *)

  let debug = true;;
%}

%token NAME TYPE WHERE IF THEN ELSE MATCH WITH LET REC FUN IN FRESH SWAP
%token INT_T REAL_T BOOL_T STRING_T UNIT_T
%token L_PAREN R_PAREN
%token DONT_CARE  /* _ */
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
%token STAR       /*  *  */
%token <string> ID
%token <AbSyn.bin_op> BIN_OP
%token <AbSyn.un_op> UN_OP
%token <int> INT
%token <float> REAL
%token <string> STRING
%token <bool> BOOL

%left SEMI DBL_SEMI STAR ARROW ELSE COMMA
%right IF LET
%nonassoc EQUAL DBL_GT DBL_LT L_PAREN R_PAREN UN_OP NAME TYPE WHERE MATCH WITH
%nonassoc FUN IN FRESH SWAP DONT_CARE LT GT UNIT COLON BAR

%start program 
%type <((string, AbSyn.typ) Hashtbl.t) * AbSyn.exp list> program

%%

program:
  | user_types SEMI { ($1, []) }
  | exp SEMI { (types, [$1]) }
  | error program { $2 }
;

user_types:
  | NAME nty { types }
  | TYPE dty ctor_list { types }
;

nty:
  | ID { Hashtbl.add types $1 (NameT $1) }
  | nty COMMA ID { Hashtbl.add types $3 (NameT $3) }
;

dty:
  | ID WHERE { Hashtbl.add types $1 (DataT $1) }
  | ID COMMA dty { Hashtbl.add types $1 (DataT $1) }
;

ctor:
  | ID COLON type_name { Hashtbl.add types $1 (CtorT $3) }
;

ctor_list:
  | ctor { }
  | ctor_list COMMA ctor { }
;

type_name:
  | INT_T  { IntT }
  | REAL_T { RealT }
  | BOOL_T { BoolT }
  | STRING_T { StringT }
  | ID {
      try let t = Hashtbl.find types $1 in t with
      Not_found -> parse_error ("Undefined identifier: "^$1); raise Parse_error
    }
  | DBL_LT ID DBL_GT type_name {
      try let NameT(s) = Hashtbl.find types $2 in NameAbT(NameT(s), $4) with
      | Not_found ->
          parse_error ("Undefined identifier: "^$2); raise Parse_error
      | Match_failure _ ->
          parse_error ("Expected name type in name abstraction");
          raise Parse_error
    }
  | UNIT_T { UnitT }
  | type_name STAR type_name { ProdT($1, $3) }
  | type_name ARROW type_name { FuncT($1, $3) }
;

rec_func:
  | ID L_PAREN ID COLON type_name R_PAREN COLON type_name EQUAL {
      Hashtbl.add types $1 (FuncT($5, $8));
      ($1, $3, $5, $8)
    }
;

dec:
  | pattern EQUAL exp { ValBind($1, $3) }
  | rec_func exp { let (a, b, c, d) = $1 in RecFunc(a, b, c, d, $2) }
;

pattern:
  | DONT_CARE { DontCareP }
  | ID { IdP($1) }
  | ID pattern { CtorP($1, $2) }
  | DBL_LT pattern DBL_GT pattern { NameAbsP($2, $4) }
  | UNIT { UnitP }
  | L_PAREN pattern COMMA pattern R_PAREN { ProdP($2, $4) }
  | L_PAREN pattern R_PAREN { $2 }
;

exp:
  | ID { (Id $1, get_pos 1) }
  | ID exp {
      try
        let t = Hashtbl.find types $1 in
        (match t with
        | CtorT _ -> (Ctor($1, $2), get_pos 1)
        | FuncT _ -> (App((Id($1), get_pos 1), $2), get_pos 1)
        | _ ->
            parse_error ("Cannot apply expression to non-function "^"type"^$1);
            raise Parse_error)
      with
      | Not_found -> (App((Id($1), get_pos 1), $2), get_pos 1)
    }
  | INT { (IntLiteral($1), get_pos 1) }
  | REAL { (RealLiteral($1), get_pos 1) }
  | BOOL { (BoolLiteral($1), get_pos 1) }
  | STRING { (StringLiteral($1), get_pos 1) }
  | FRESH COLON ID { (Fresh $3, get_pos 1) }
  | IF exp EQUAL exp THEN exp ELSE exp {
      (If($2, $4, $6, $8), get_pos 1)
    }
  | SWAP L_PAREN exp COMMA exp R_PAREN IN exp {
      (Swap($3, $5, $8), get_pos 1)
    }
  | DBL_LT exp DBL_GT exp {
      (NameAb($2, $4), get_pos 1)
    }
  | UNIT { (Unit, get_pos 1) }
  | L_PAREN exp COMMA exp R_PAREN {
      (Pair($2, $4), get_pos 1)
    }
  | exp exp { (App($1, $2), get_pos 1) }
  | MATCH exp WITH branch { (Match($2, $4), get_pos 1) }
  | LET dec { (TopLet($2, get_pos 2), get_pos 1) }
  | LET dec IN exp { (Let($2, $4), get_pos 1) }
  | exp BIN_OP exp { (BinaryOp($1, $2, $3), get_pos 1) }
  | exp STAR exp { (BinaryOp($1, Mult, $3), get_pos 1) }
  | FUN L_PAREN ID COLON type_name R_PAREN ARROW exp {
      (Lambda($3, $5, $8), get_pos 1)
    }
  | UN_OP exp { (UnaryOp($1, $2), get_pos 1) }
  | L_PAREN exp R_PAREN { $2 }
;

branch:
  | BAR pattern ARROW exp { [($2, $4)] }
  | branch BAR pattern ARROW exp { ($3, $5)::$1 }
;

%%

