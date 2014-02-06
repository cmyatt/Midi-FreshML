type token =
  | NAME
  | TYPE
  | WHERE
  | IF
  | THEN
  | ELSE
  | MATCH
  | WITH
  | LET
  | REC
  | FUN
  | IN
  | FRESH
  | SWAP
  | LIST
  | INT_T
  | REAL_T
  | BOOL_T
  | STRING_T
  | UNIT_T
  | L_PAREN
  | R_PAREN
  | HASH
  | DONT_CARE
  | EQUAL
  | COMMA
  | DBL_LT
  | DBL_GT
  | UNIT
  | ARROW
  | BAR
  | COLON
  | SEMI
  | DBL_SEMI
  | STAR
  | ID of (string)
  | BIN_OP of (AbSyn.bin_op)
  | UN_OP of (AbSyn.un_op)
  | INT of (int)
  | REAL of (float)
  | STRING of (string)
  | BOOL of (bool)

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> ((string, int) Hashtbl.t) * ((string, AbSyn.typ) Hashtbl.t) * AbSyn.exp list
