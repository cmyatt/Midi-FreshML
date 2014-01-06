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
  | INT_T
  | REAL_T
  | BOOL_T
  | STRING_T
  | UNIT_T
  | L_PAREN
  | R_PAREN
  | DONT_CARE
  | EQUAL
  | LT
  | GT
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
  | BIN_OP of (AbSyn.bin_op)
  | UN_OP of (AbSyn.un_op)
  | ID of (string)
  | INT of (int)
  | REAL of (float)
  | STRING of (string)
  | BOOL of (bool)

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
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
# 61 "parser.ml"
let yytransl_const = [|
  257 (* NAME *);
  258 (* TYPE *);
  259 (* WHERE *);
  260 (* IF *);
  261 (* THEN *);
  262 (* ELSE *);
  263 (* MATCH *);
  264 (* WITH *);
  265 (* LET *);
  266 (* REC *);
  267 (* FUN *);
  268 (* IN *);
  269 (* FRESH *);
  270 (* SWAP *);
  271 (* INT_T *);
  272 (* REAL_T *);
  273 (* BOOL_T *);
  274 (* STRING_T *);
  275 (* UNIT_T *);
  276 (* L_PAREN *);
  277 (* R_PAREN *);
  278 (* DONT_CARE *);
  279 (* EQUAL *);
  280 (* LT *);
  281 (* GT *);
  282 (* COMMA *);
  283 (* DBL_LT *);
  284 (* DBL_GT *);
  285 (* UNIT *);
  286 (* ARROW *);
  287 (* BAR *);
  288 (* COLON *);
  289 (* SEMI *);
  290 (* DBL_SEMI *);
  291 (* STAR *);
    0|]

let yytransl_block = [|
  292 (* BIN_OP *);
  293 (* UN_OP *);
  294 (* ID *);
  295 (* INT *);
  296 (* REAL *);
  297 (* STRING *);
  298 (* BOOL *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\002\000\002\000\002\000\006\000\007\000\
\010\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
\010\000\008\000\008\000\011\000\009\000\009\000\004\000\004\000\
\012\000\012\000\012\000\012\000\012\000\012\000\012\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\013\000\013\000\000\000"

let yylen = "\002\000\
\003\000\000\000\005\000\000\000\002\000\002\000\003\000\004\000\
\001\000\001\000\001\000\001\000\001\000\004\000\001\000\003\000\
\003\000\001\000\003\000\003\000\002\000\003\000\003\000\010\000\
\001\000\001\000\002\000\004\000\001\000\005\000\003\000\001\000\
\002\000\001\000\001\000\001\000\001\000\003\000\008\000\008\000\
\004\000\001\000\005\000\008\000\002\000\004\000\004\000\003\000\
\003\000\002\000\003\000\004\000\005\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\054\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\005\000\006\000\000\000\
\007\000\000\000\000\000\025\000\000\000\029\000\000\000\000\000\
\000\000\001\000\019\000\000\000\008\000\000\000\000\000\000\000\
\000\000\000\000\027\000\000\000\000\000\000\000\000\000\021\000\
\031\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\042\000\000\000\000\000\034\000\
\035\000\037\000\036\000\000\000\000\000\009\000\010\000\011\000\
\012\000\015\000\000\000\013\000\000\000\022\000\000\000\028\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\003\000\000\000\
\000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\
\000\000\038\000\000\000\051\000\000\000\000\000\000\000\000\000\
\000\000\000\000\017\000\016\000\000\000\000\000\000\000\046\000\
\000\000\000\000\000\000\000\000\000\000\000\000\014\000\000\000\
\000\000\000\000\000\000\000\000\043\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\053\000\000\000\000\000"

let yydgoto = "\002\000\
\005\000\006\000\087\000\024\000\088\000\007\000\008\000\010\000\
\029\000\069\000\030\000\025\000\112\000"

let yysindex = "\011\000\
\053\255\000\000\246\254\246\254\000\000\021\255\053\255\053\255\
\010\255\030\255\070\255\054\255\045\255\000\000\000\000\246\254\
\000\000\046\255\121\255\000\000\049\255\000\000\162\255\078\255\
\079\255\000\000\000\000\092\255\000\000\006\255\121\255\243\254\
\097\255\199\255\000\000\050\001\050\001\178\255\046\255\000\000\
\000\000\121\255\121\255\048\255\050\001\050\001\054\255\106\255\
\095\255\108\255\050\001\050\001\000\000\050\001\050\001\000\000\
\000\000\000\000\000\000\189\000\228\000\000\000\000\000\000\000\
\000\000\000\000\100\255\000\000\017\255\000\000\118\255\000\000\
\178\255\133\255\172\255\140\255\107\255\117\255\050\001\094\255\
\211\255\050\001\228\000\054\255\050\001\050\001\000\000\228\000\
\129\255\178\255\178\255\000\000\255\254\050\001\130\255\050\001\
\131\255\000\000\250\255\000\000\050\001\050\001\152\255\050\001\
\050\001\178\255\000\000\000\000\134\255\033\000\121\255\000\000\
\228\000\178\255\050\001\072\000\050\001\050\001\000\000\178\255\
\050\001\135\255\003\255\111\000\000\000\189\000\087\255\150\000\
\050\001\137\255\165\255\050\001\050\001\011\001\050\001\050\001\
\228\000\228\000\000\000\050\001\228\000"

let yyrindex = "\000\000\
\254\254\000\000\000\000\000\000\000\000\145\255\254\254\254\254\
\002\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\164\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\128\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\035\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\036\255\000\000\
\000\000\000\000\000\000\145\255\176\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\020\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\088\001\248\001\000\000\000\000\000\000\000\000\016\002\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\120\001\
\152\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\040\002\000\000\000\000\000\000\184\001\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\145\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\083\255\000\000\000\000\
\186\255\064\002\000\000\216\001\088\002"

let yygindex = "\000\000\
\000\000\105\000\184\000\212\255\220\255\000\000\000\000\007\000\
\163\000\187\255\000\000\239\255\069\000"

let yytablesize = 889
let yytable = "\060\000\
\061\000\032\000\076\000\093\000\018\000\035\000\004\000\041\000\
\074\000\075\000\011\000\001\000\042\000\035\000\080\000\081\000\
\032\000\082\000\083\000\109\000\107\000\108\000\027\000\130\000\
\071\000\072\000\035\000\009\000\090\000\012\000\004\000\039\000\
\090\000\091\000\018\000\016\000\119\000\091\000\040\000\103\000\
\032\000\032\000\099\000\032\000\123\000\020\000\090\000\032\000\
\104\000\105\000\127\000\091\000\020\000\003\000\004\000\026\000\
\032\000\110\000\032\000\113\000\026\000\032\000\017\000\032\000\
\116\000\117\000\032\000\019\000\032\000\020\000\032\000\032\000\
\018\000\019\000\021\000\020\000\022\000\026\000\124\000\073\000\
\021\000\126\000\022\000\028\000\128\000\031\000\033\000\052\000\
\052\000\036\000\052\000\023\000\134\000\122\000\052\000\137\000\
\138\000\045\000\140\000\141\000\046\000\037\000\047\000\052\000\
\048\000\052\000\049\000\050\000\052\000\132\000\052\000\014\000\
\015\000\051\000\100\000\052\000\090\000\052\000\052\000\101\000\
\052\000\091\000\053\000\038\000\043\000\077\000\078\000\079\000\
\085\000\086\000\054\000\055\000\056\000\057\000\058\000\059\000\
\045\000\089\000\092\000\046\000\019\000\047\000\020\000\048\000\
\097\000\049\000\050\000\021\000\026\000\022\000\026\000\096\000\
\051\000\026\000\098\000\094\000\106\000\026\000\031\000\052\000\
\111\000\053\000\114\000\118\000\129\000\120\000\135\000\085\000\
\086\000\054\000\055\000\056\000\057\000\058\000\059\000\045\000\
\136\000\002\000\046\000\095\000\047\000\034\000\048\000\020\000\
\049\000\050\000\026\000\023\000\021\000\013\000\022\000\051\000\
\062\000\063\000\064\000\065\000\066\000\024\000\052\000\031\000\
\053\000\070\000\139\000\000\000\067\000\000\000\085\000\086\000\
\054\000\055\000\056\000\057\000\058\000\059\000\045\000\068\000\
\000\000\046\000\019\000\047\000\020\000\048\000\000\000\049\000\
\050\000\021\000\000\000\022\000\000\000\000\000\051\000\000\000\
\000\000\000\000\000\000\000\000\044\000\052\000\102\000\053\000\
\000\000\000\000\000\000\000\000\000\000\085\000\086\000\054\000\
\055\000\056\000\057\000\058\000\059\000\045\000\000\000\000\000\
\046\000\000\000\047\000\000\000\048\000\000\000\049\000\050\000\
\000\000\000\000\000\000\000\000\000\000\051\000\000\000\000\000\
\000\000\000\000\000\000\115\000\052\000\000\000\053\000\000\000\
\000\000\000\000\000\000\000\000\085\000\086\000\054\000\055\000\
\056\000\057\000\058\000\059\000\045\000\121\000\000\000\046\000\
\000\000\047\000\000\000\048\000\000\000\049\000\050\000\000\000\
\000\000\000\000\000\000\000\000\051\000\000\000\000\000\000\000\
\000\000\000\000\000\000\052\000\000\000\053\000\000\000\000\000\
\000\000\000\000\000\000\085\000\086\000\054\000\055\000\056\000\
\057\000\058\000\059\000\045\000\000\000\000\000\046\000\000\000\
\047\000\000\000\048\000\000\000\049\000\050\000\000\000\000\000\
\000\000\000\000\000\000\051\000\125\000\000\000\000\000\000\000\
\000\000\000\000\052\000\000\000\053\000\000\000\000\000\000\000\
\000\000\000\000\085\000\086\000\054\000\055\000\056\000\057\000\
\058\000\059\000\045\000\000\000\000\000\046\000\000\000\047\000\
\000\000\048\000\000\000\049\000\050\000\000\000\000\000\000\000\
\000\000\000\000\051\000\131\000\000\000\000\000\000\000\000\000\
\000\000\052\000\000\000\053\000\000\000\000\000\000\000\000\000\
\000\000\085\000\086\000\054\000\055\000\056\000\057\000\058\000\
\059\000\045\000\000\000\133\000\046\000\000\000\047\000\000\000\
\048\000\000\000\049\000\050\000\000\000\000\000\000\000\000\000\
\000\000\051\000\000\000\000\000\000\000\000\000\000\000\000\000\
\052\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\
\085\000\086\000\054\000\055\000\056\000\057\000\058\000\059\000\
\045\000\000\000\000\000\046\000\000\000\084\000\000\000\048\000\
\000\000\049\000\050\000\000\000\000\000\000\000\000\000\000\000\
\051\000\000\000\000\000\000\000\000\000\000\000\000\000\052\000\
\000\000\053\000\000\000\000\000\000\000\000\000\000\000\085\000\
\086\000\054\000\055\000\056\000\057\000\058\000\059\000\045\000\
\000\000\000\000\046\000\000\000\047\000\000\000\048\000\000\000\
\049\000\050\000\000\000\000\000\000\000\000\000\000\000\051\000\
\000\000\000\000\000\000\000\000\000\000\000\000\052\000\000\000\
\053\000\000\000\000\000\000\000\000\000\000\000\085\000\086\000\
\054\000\055\000\056\000\057\000\058\000\059\000\045\000\000\000\
\000\000\046\000\000\000\047\000\000\000\048\000\000\000\049\000\
\050\000\000\000\000\000\000\000\000\000\000\000\051\000\000\000\
\000\000\000\000\000\000\000\000\000\000\052\000\000\000\053\000\
\000\000\111\000\000\000\000\000\000\000\000\000\000\000\054\000\
\055\000\056\000\057\000\058\000\059\000\045\000\000\000\000\000\
\046\000\000\000\047\000\000\000\048\000\000\000\049\000\050\000\
\000\000\000\000\000\000\000\000\000\000\051\000\000\000\000\000\
\000\000\000\000\000\000\000\000\052\000\000\000\053\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\054\000\055\000\
\056\000\057\000\058\000\059\000\050\000\050\000\000\000\050\000\
\000\000\000\000\000\000\050\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\050\000\000\000\050\000\000\000\
\000\000\050\000\000\000\050\000\000\000\000\000\050\000\000\000\
\050\000\000\000\050\000\050\000\049\000\049\000\000\000\049\000\
\000\000\000\000\000\000\049\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\049\000\000\000\049\000\000\000\
\000\000\049\000\000\000\049\000\000\000\000\000\049\000\000\000\
\049\000\000\000\049\000\049\000\048\000\048\000\000\000\048\000\
\000\000\000\000\000\000\048\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\048\000\000\000\048\000\000\000\
\000\000\048\000\000\000\048\000\000\000\000\000\048\000\000\000\
\048\000\000\000\048\000\048\000\041\000\041\000\000\000\041\000\
\000\000\000\000\000\000\041\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\041\000\000\000\041\000\000\000\
\000\000\041\000\000\000\041\000\000\000\000\000\041\000\000\000\
\041\000\000\000\041\000\041\000\044\000\044\000\000\000\044\000\
\000\000\000\000\000\000\044\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\044\000\000\000\044\000\000\000\
\000\000\044\000\000\000\044\000\000\000\000\000\044\000\000\000\
\044\000\000\000\044\000\044\000\033\000\033\000\000\000\033\000\
\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\033\000\000\000\033\000\000\000\
\000\000\033\000\000\000\033\000\045\000\045\000\033\000\045\000\
\033\000\000\000\000\000\045\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\045\000\000\000\045\000\000\000\
\000\000\045\000\000\000\045\000\047\000\047\000\045\000\047\000\
\045\000\000\000\000\000\047\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\047\000\000\000\047\000\000\000\
\000\000\047\000\000\000\047\000\039\000\039\000\047\000\039\000\
\047\000\000\000\000\000\039\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\039\000\000\000\039\000\000\000\
\000\000\039\000\000\000\039\000\040\000\040\000\039\000\040\000\
\039\000\000\000\000\000\040\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\040\000\000\000\040\000\000\000\
\000\000\040\000\000\000\040\000\000\000\000\000\040\000\000\000\
\040\000"

let yycheck = "\036\000\
\037\000\019\000\047\000\073\000\003\001\023\000\009\001\021\001\
\045\000\046\000\004\000\001\000\026\001\031\000\051\000\052\000\
\034\000\054\000\055\000\021\001\090\000\091\000\016\000\021\001\
\042\000\043\000\044\000\038\001\030\001\009\001\033\001\026\001\
\030\001\035\001\033\001\026\001\106\000\035\001\033\001\084\000\
\005\001\006\001\079\000\008\001\114\000\026\001\030\001\012\001\
\085\000\086\000\120\000\035\001\033\001\001\001\002\001\021\001\
\021\001\094\000\023\001\096\000\026\001\026\001\033\001\028\001\
\101\000\102\000\031\001\020\001\033\001\022\001\035\001\036\001\
\003\001\020\001\027\001\022\001\029\001\033\001\115\000\032\001\
\027\001\118\000\029\001\038\001\121\000\038\001\038\001\005\001\
\006\001\012\001\008\001\038\001\129\000\111\000\012\001\132\000\
\133\000\004\001\135\000\136\000\007\001\023\001\009\001\021\001\
\011\001\023\001\013\001\014\001\026\001\023\001\028\001\007\000\
\008\000\020\001\021\001\033\001\030\001\035\001\036\001\026\001\
\027\001\035\001\029\001\032\001\028\001\020\001\032\001\020\001\
\035\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\004\001\038\001\021\001\007\001\020\001\009\001\022\001\011\001\
\038\001\013\001\014\001\027\001\021\001\029\001\023\001\012\001\
\020\001\026\001\038\001\023\001\028\001\030\001\038\001\027\001\
\031\001\029\001\032\001\012\001\030\001\032\001\030\001\035\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\004\001\
\012\001\033\001\007\001\008\001\009\001\020\001\011\001\022\001\
\013\001\014\001\023\001\012\001\027\001\006\000\029\001\020\001\
\015\001\016\001\017\001\018\001\019\001\012\001\027\001\038\001\
\029\001\039\000\134\000\255\255\027\001\255\255\035\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\004\001\038\001\
\255\255\007\001\020\001\009\001\022\001\011\001\255\255\013\001\
\014\001\027\001\255\255\029\001\255\255\255\255\020\001\255\255\
\255\255\255\255\255\255\255\255\038\001\027\001\028\001\029\001\
\255\255\255\255\255\255\255\255\255\255\035\001\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\004\001\255\255\255\255\
\007\001\255\255\009\001\255\255\011\001\255\255\013\001\014\001\
\255\255\255\255\255\255\255\255\255\255\020\001\255\255\255\255\
\255\255\255\255\255\255\026\001\027\001\255\255\029\001\255\255\
\255\255\255\255\255\255\255\255\035\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\004\001\005\001\255\255\007\001\
\255\255\009\001\255\255\011\001\255\255\013\001\014\001\255\255\
\255\255\255\255\255\255\255\255\020\001\255\255\255\255\255\255\
\255\255\255\255\255\255\027\001\255\255\029\001\255\255\255\255\
\255\255\255\255\255\255\035\001\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\004\001\255\255\255\255\007\001\255\255\
\009\001\255\255\011\001\255\255\013\001\014\001\255\255\255\255\
\255\255\255\255\255\255\020\001\021\001\255\255\255\255\255\255\
\255\255\255\255\027\001\255\255\029\001\255\255\255\255\255\255\
\255\255\255\255\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\004\001\255\255\255\255\007\001\255\255\009\001\
\255\255\011\001\255\255\013\001\014\001\255\255\255\255\255\255\
\255\255\255\255\020\001\021\001\255\255\255\255\255\255\255\255\
\255\255\027\001\255\255\029\001\255\255\255\255\255\255\255\255\
\255\255\035\001\036\001\037\001\038\001\039\001\040\001\041\001\
\042\001\004\001\255\255\006\001\007\001\255\255\009\001\255\255\
\011\001\255\255\013\001\014\001\255\255\255\255\255\255\255\255\
\255\255\020\001\255\255\255\255\255\255\255\255\255\255\255\255\
\027\001\255\255\029\001\255\255\255\255\255\255\255\255\255\255\
\035\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\004\001\255\255\255\255\007\001\255\255\009\001\255\255\011\001\
\255\255\013\001\014\001\255\255\255\255\255\255\255\255\255\255\
\020\001\255\255\255\255\255\255\255\255\255\255\255\255\027\001\
\255\255\029\001\255\255\255\255\255\255\255\255\255\255\035\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\004\001\
\255\255\255\255\007\001\255\255\009\001\255\255\011\001\255\255\
\013\001\014\001\255\255\255\255\255\255\255\255\255\255\020\001\
\255\255\255\255\255\255\255\255\255\255\255\255\027\001\255\255\
\029\001\255\255\255\255\255\255\255\255\255\255\035\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\004\001\255\255\
\255\255\007\001\255\255\009\001\255\255\011\001\255\255\013\001\
\014\001\255\255\255\255\255\255\255\255\255\255\020\001\255\255\
\255\255\255\255\255\255\255\255\255\255\027\001\255\255\029\001\
\255\255\031\001\255\255\255\255\255\255\255\255\255\255\037\001\
\038\001\039\001\040\001\041\001\042\001\004\001\255\255\255\255\
\007\001\255\255\009\001\255\255\011\001\255\255\013\001\014\001\
\255\255\255\255\255\255\255\255\255\255\020\001\255\255\255\255\
\255\255\255\255\255\255\255\255\027\001\255\255\029\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\037\001\038\001\
\039\001\040\001\041\001\042\001\005\001\006\001\255\255\008\001\
\255\255\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\255\255\255\255\031\001\255\255\
\033\001\255\255\035\001\036\001\005\001\006\001\255\255\008\001\
\255\255\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\255\255\255\255\031\001\255\255\
\033\001\255\255\035\001\036\001\005\001\006\001\255\255\008\001\
\255\255\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\255\255\255\255\031\001\255\255\
\033\001\255\255\035\001\036\001\005\001\006\001\255\255\008\001\
\255\255\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\255\255\255\255\031\001\255\255\
\033\001\255\255\035\001\036\001\005\001\006\001\255\255\008\001\
\255\255\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\255\255\255\255\031\001\255\255\
\033\001\255\255\035\001\036\001\005\001\006\001\255\255\008\001\
\255\255\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\005\001\006\001\031\001\008\001\
\033\001\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\005\001\006\001\031\001\008\001\
\033\001\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\005\001\006\001\031\001\008\001\
\033\001\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\005\001\006\001\031\001\008\001\
\033\001\255\255\255\255\012\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\255\255\028\001\255\255\255\255\031\001\255\255\
\033\001"

let yynames_const = "\
  NAME\000\
  TYPE\000\
  WHERE\000\
  IF\000\
  THEN\000\
  ELSE\000\
  MATCH\000\
  WITH\000\
  LET\000\
  REC\000\
  FUN\000\
  IN\000\
  FRESH\000\
  SWAP\000\
  INT_T\000\
  REAL_T\000\
  BOOL_T\000\
  STRING_T\000\
  UNIT_T\000\
  L_PAREN\000\
  R_PAREN\000\
  DONT_CARE\000\
  EQUAL\000\
  LT\000\
  GT\000\
  COMMA\000\
  DBL_LT\000\
  DBL_GT\000\
  UNIT\000\
  ARROW\000\
  BAR\000\
  COLON\000\
  SEMI\000\
  DBL_SEMI\000\
  STAR\000\
  "

let yynames_block = "\
  BIN_OP\000\
  UN_OP\000\
  ID\000\
  INT\000\
  REAL\000\
  STRING\000\
  BOOL\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'user_types) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'let_decs) in
    Obj.repr(
# 50 "parser.mly"
                             ( (_1, _2) )
# 481 "parser.ml"
               : AbSyn.user_types list * AbSyn.exp list))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                ( [] )
# 487 "parser.ml"
               : 'let_decs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'dec) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'let_decs) in
    Obj.repr(
# 55 "parser.mly"
                            ( (Let(_2, _4), get_pos 1)::_5 )
# 496 "parser.ml"
               : 'let_decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
                ( [] )
# 502 "parser.ml"
               : 'user_types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'nty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'user_types) in
    Obj.repr(
# 60 "parser.mly"
                   ( Ns(_1)::_2 )
# 510 "parser.ml"
               : 'user_types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'dty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'user_types) in
    Obj.repr(
# 61 "parser.mly"
                   ( Ds(_1)::_2 )
# 518 "parser.ml"
               : 'user_types))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'id_list) in
    Obj.repr(
# 65 "parser.mly"
                      ( _2 )
# 525 "parser.ml"
               : 'nty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'id_list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'ctor_list) in
    Obj.repr(
# 69 "parser.mly"
                                 ( (_2, _4) )
# 533 "parser.ml"
               : 'dty))
; (fun __caml_parser_env ->
    Obj.repr(
# 73 "parser.mly"
           ( IntT )
# 539 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
           ( RealT )
# 545 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
           ( BoolT )
# 551 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
             ( StringT )
# 557 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 77 "parser.mly"
       ( DataT(_1) )
# 564 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'type_name) in
    Obj.repr(
# 78 "parser.mly"
                               ( NameAbT(_2, _4) )
# 572 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "parser.mly"
           ( UnitT )
# 578 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_name) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'type_name) in
    Obj.repr(
# 80 "parser.mly"
                             ( ProdT(_1, _3) )
# 586 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_name) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'type_name) in
    Obj.repr(
# 81 "parser.mly"
                              ( FuncT(_1, _3) )
# 594 "parser.ml"
               : 'type_name))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 85 "parser.mly"
       ( [_1] )
# 601 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'id_list) in
    Obj.repr(
# 86 "parser.mly"
                     ( _1::_3 )
# 609 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'type_name) in
    Obj.repr(
# 90 "parser.mly"
                       ( (_1, _3) )
# 617 "parser.ml"
               : 'ctor))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ctor) in
    Obj.repr(
# 94 "parser.mly"
              ( [_1] )
# 624 "parser.ml"
               : 'ctor_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ctor) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ctor_list) in
    Obj.repr(
# 95 "parser.mly"
                         ( _1::_3 )
# 632 "parser.ml"
               : 'ctor_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 99 "parser.mly"
                      ( ValBind(_1, _3) )
# 640 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 9 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'type_name) in
    let _8 = (Parsing.peek_val __caml_parser_env 2 : 'type_name) in
    let _10 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 100 "parser.mly"
                                                                    (
      RecFunc(_1, _3, _5, _8, _10)
    )
# 653 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    Obj.repr(
# 106 "parser.mly"
              ( DontCareP )
# 659 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 107 "parser.mly"
       ( IdP(_1) )
# 666 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 108 "parser.mly"
               ( CtorP(_1, _2) )
# 674 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'pattern) in
    Obj.repr(
# 109 "parser.mly"
                             ( NameAbsP(_2, _4) )
# 682 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    Obj.repr(
# 110 "parser.mly"
         ( UnitP )
# 688 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    Obj.repr(
# 111 "parser.mly"
                                          ( ProdP(_2, _4) )
# 696 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'pattern) in
    Obj.repr(
# 112 "parser.mly"
                            ( _2 )
# 703 "parser.ml"
               : 'pattern))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 118 "parser.mly"
       ( (Id _1, get_pos 1) )
# 710 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 119 "parser.mly"
           ( (Ctor(_1, _2), get_pos 1) )
# 718 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 120 "parser.mly"
        ( (IntLiteral(_1), get_pos 1) )
# 725 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 121 "parser.mly"
         ( (RealLiteral(_1), get_pos 1) )
# 732 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 122 "parser.mly"
         ( (BoolLiteral(_1), get_pos 1) )
# 739 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 123 "parser.mly"
           ( (StringLiteral(_1), get_pos 1) )
# 746 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 124 "parser.mly"
                   ( (Fresh _3, get_pos 1) )
# 753 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'exp) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 125 "parser.mly"
                                       ( (If(_2, _4, _6, _8), get_pos 1) )
# 763 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'exp) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 126 "parser.mly"
                                              ( (Swap(_3, _5, _8), get_pos 1) )
# 772 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 127 "parser.mly"
                          ( (NameAb(_2, _4), get_pos 1) )
# 780 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    Obj.repr(
# 128 "parser.mly"
         ( (Unit, get_pos 1) )
# 786 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 129 "parser.mly"
                                  ( (Pair(_2, _4), get_pos 1) )
# 794 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'type_name) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 130 "parser.mly"
                                                     (
      (Lambda(_3, _5, _8), get_pos 1)
    )
# 805 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 133 "parser.mly"
            ( (App(_1, _2), get_pos 1) )
# 813 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'branch) in
    Obj.repr(
# 134 "parser.mly"
                          ( (Match(_2, _4), get_pos 1) )
# 821 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'dec) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 135 "parser.mly"
                   ( (Let(_2, _4), get_pos 1) )
# 829 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : AbSyn.bin_op) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 136 "parser.mly"
                   ( (BinaryOp(_1, _2, _3), get_pos 1) )
# 838 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 137 "parser.mly"
                 ( (BinaryOp(_1, Mult, _3), get_pos 1) )
# 846 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : AbSyn.un_op) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 138 "parser.mly"
              ( (UnaryOp(_1, _2), get_pos 1) )
# 854 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 139 "parser.mly"
                        ( _2 )
# 861 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 143 "parser.mly"
                          ( [(_2, _4)] )
# 869 "parser.ml"
               : 'branch))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'pattern) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'branch) in
    Obj.repr(
# 144 "parser.mly"
                                 ( (_2, _4)::_5 )
# 878 "parser.ml"
               : 'branch))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : AbSyn.user_types list * AbSyn.exp list)
;;
# 148 "parser.mly"

# 905 "parser.ml"
