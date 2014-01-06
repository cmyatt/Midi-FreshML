# 1 "lexer.mll"
 
  open Printf
  open Parser;;

  exception Lexer_error of string;;

  (* Update lexbuf positional info *)
  (* type position = {
   *   pos_fname : string;  (* file name *)
   *   pos_lnum : int;		  (* line number *)
   *   pos_bol : int;		    (* the offset of the beginning of the line *)
   *   pos_cnum : int;		  (* the offset of the position *)
   * }
   *)
  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    };;

  let create_hashtable size data =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, value) -> Hashtbl.add tbl key value) data; tbl;;

  let keyword_tbl =
    create_hashtable 18 [
      ("name", NAME);
      ("type", TYPE);
      ("where", WHERE);
      ("if", IF);
      ("then", THEN);
      ("else", ELSE);
      ("match", MATCH);
      ("with", WITH);
      ("let", LET);
      ("fun", FUN);
      ("in", IN);
      ("fresh", FRESH);
      ("swap", SWAP);
      ("int", INT_T);
      ("real", REAL_T);
      ("bool", BOOL_T);
      ("string", STRING_T);
      ("unit", UNIT_T)
    ];;

  let cur_str = ref "";;

# 52 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\226\255\227\255\229\255\230\255\001\000\004\000\032\000\
    \237\255\238\255\241\255\242\255\243\255\244\255\051\000\246\255\
    \247\255\032\000\249\255\250\255\252\255\084\000\192\000\020\001\
    \161\000\171\000\104\001\188\001\016\002\100\002\184\002\239\255\
    \228\255\240\255\236\255\234\255\233\255\074\001\251\255\252\255\
    \253\255\004\000\055\000\255\255\254\255\111\000\253\255\254\255\
    \255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\024\000\023\000\020\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\010\000\255\255\
    \255\255\007\000\255\255\255\255\255\255\002\000\002\000\002\000\
    \000\000\001\000\002\000\002\000\002\000\002\000\002\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\003\000\003\000\255\255\255\255\255\255\255\255\255\255\
    \255\255";
  Lexing.lex_default = 
   "\002\000\000\000\000\000\000\000\000\000\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\255\255\000\000\000\000\000\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\000\000\
    \000\000\000\000\000\000\000\000\000\000\039\000\000\000\000\000\
    \000\000\255\255\255\255\000\000\000\000\047\000\000\000\000\000\
    \000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\003\000\004\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \003\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\
    \014\000\013\000\016\000\018\000\010\000\017\000\044\000\015\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\008\000\007\000\006\000\011\000\005\000\036\000\
    \035\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\034\000\033\000\032\000\031\000\019\000\
    \043\000\021\000\021\000\021\000\021\000\021\000\022\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\023\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\009\000\000\000\012\000\000\000\
    \000\000\000\000\000\000\000\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\000\000\000\000\
    \000\000\048\000\000\000\000\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\000\000\
    \000\000\000\000\000\000\021\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\025\000\
    \000\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\000\000\000\000\021\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\000\000\000\000\000\000\000\000\021\000\
    \000\000\028\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\040\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\046\000\
    \000\000\000\000\041\000\021\000\042\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\026\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\000\000\000\000\000\000\000\000\021\000\
    \000\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\027\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\000\000\
    \000\000\000\000\000\000\021\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\038\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\000\000\000\000\000\000\000\000\021\000\
    \000\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\029\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\000\000\
    \000\000\000\000\000\000\021\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\030\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\000\000\000\000\000\000\000\000\021\000\
    \000\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\041\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\
    \006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\007\000\014\000\014\000\017\000\000\000\
    \042\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\021\000\000\000\255\255\000\000\255\255\
    \255\255\255\255\255\255\255\255\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\255\255\255\255\
    \255\255\045\000\255\255\255\255\255\255\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\255\255\
    \255\255\255\255\255\255\021\000\255\255\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\024\000\
    \255\255\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\255\255\255\255\022\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\255\255\255\255\255\255\255\255\022\000\
    \255\255\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\023\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\037\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\045\000\
    \255\255\255\255\037\000\023\000\037\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\026\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\255\255\255\255\255\255\255\255\026\000\
    \255\255\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\027\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\255\255\
    \255\255\255\255\255\255\027\000\255\255\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\028\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\037\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\255\255\255\255\255\255\255\255\028\000\
    \255\255\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\029\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\255\255\
    \255\255\255\255\255\255\029\000\255\255\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\030\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\255\255\255\255\255\255\255\255\030\000\
    \255\255\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec scan lexbuf =
    __ocaml_lex_scan_rec lexbuf 0
and __ocaml_lex_scan_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 57 "lexer.mll"
              inum
# 342 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 57 "lexer.mll"
                   (
      let n = int_of_string inum in printf "INT (%d)\n" n;
      INT n
    )
# 349 "lexer.ml"

  | 1 ->
let
# 61 "lexer.mll"
                         rnum
# 355 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 61 "lexer.mll"
                              (
      let n = float_of_string rnum in printf "REAL (%f)\n" n;
      REAL n
    )
# 362 "lexer.ml"

  | 2 ->
let
# 65 "lexer.mll"
          word
# 368 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 65 "lexer.mll"
               (
      try let kw = Hashtbl.find keyword_tbl word in printf "%s\n" word; kw with
      | Not_found -> printf "ID (%s)\n" word; ID word
    )
# 375 "lexer.ml"

  | 3 ->
# 69 "lexer.mll"
         ( cur_str := ""; str_literal lexbuf )
# 380 "lexer.ml"

  | 4 ->
let
# 71 "lexer.mll"
               b
# 386 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 71 "lexer.mll"
                 ( printf "BOOL (%s)\n" b; BOOL (bool_of_string b) )
# 390 "lexer.ml"

  | 5 ->
# 72 "lexer.mll"
        ( printf "DONT_CARE\n"; DONT_CARE )
# 395 "lexer.ml"

  | 6 ->
# 73 "lexer.mll"
        ( printf "BIN_OP (+)\n"; BIN_OP(AbSyn.Add) )
# 400 "lexer.ml"

  | 7 ->
# 74 "lexer.mll"
        ( printf "BIN_OP (-)\n"; BIN_OP(AbSyn.Sub) )
# 405 "lexer.ml"

  | 8 ->
# 75 "lexer.mll"
        ( printf "STAR\n"; STAR )
# 410 "lexer.ml"

  | 9 ->
# 76 "lexer.mll"
        ( printf "BIN_OP (/)\n"; BIN_OP(AbSyn.Div) )
# 415 "lexer.ml"

  | 10 ->
# 77 "lexer.mll"
         ( printf "L_PAREN\n"; L_PAREN )
# 420 "lexer.ml"

  | 11 ->
# 78 "lexer.mll"
         ( printf "R_PAREN\n"; R_PAREN )
# 425 "lexer.ml"

  | 12 ->
# 79 "lexer.mll"
         ( printf "UN_OP (~)\n"; UN_OP(AbSyn.Neg) )
# 430 "lexer.ml"

  | 13 ->
# 80 "lexer.mll"
         ( printf "EQUAL\n"; EQUAL )
# 435 "lexer.ml"

  | 14 ->
# 81 "lexer.mll"
         ( printf "COMMA\n"; COMMA )
# 440 "lexer.ml"

  | 15 ->
# 82 "lexer.mll"
         ( printf "UNIT\n"; UNIT )
# 445 "lexer.ml"

  | 16 ->
# 83 "lexer.mll"
         ( printf "ARROW\n"; ARROW )
# 450 "lexer.ml"

  | 17 ->
# 84 "lexer.mll"
         ( printf "BAR\n"; BAR )
# 455 "lexer.ml"

  | 18 ->
# 85 "lexer.mll"
         ( printf "COLON\n"; COLON )
# 460 "lexer.ml"

  | 19 ->
# 86 "lexer.mll"
         ( printf "DBL_SEMI\n"; DBL_SEMI )
# 465 "lexer.ml"

  | 20 ->
# 87 "lexer.mll"
         ( printf "SEMI\n"; SEMI )
# 470 "lexer.ml"

  | 21 ->
# 88 "lexer.mll"
         ( printf "DBL_LT\n"; DBL_LT )
# 475 "lexer.ml"

  | 22 ->
# 89 "lexer.mll"
         ( printf "DBL_GT\n"; DBL_GT )
# 480 "lexer.ml"

  | 23 ->
# 90 "lexer.mll"
         ( printf "LT\n"; LT )
# 485 "lexer.ml"

  | 24 ->
# 91 "lexer.mll"
         ( printf "GT\n"; GT )
# 490 "lexer.ml"

  | 25 ->
# 92 "lexer.mll"
         ( incr_linenum lexbuf; scan lexbuf )
# 495 "lexer.ml"

  | 26 ->
# 93 "lexer.mll"
               ( scan lexbuf )
# 500 "lexer.ml"

  | 27 ->
# 94 "lexer.mll"
         ( comment 0 lexbuf )
# 505 "lexer.ml"

  | 28 ->
let
# 95 "lexer.mll"
         c
# 511 "lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 95 "lexer.mll"
           ( raise (Lexer_error ("Unrecognised character: "^(Char.escaped c))) )
# 515 "lexer.ml"

  | 29 ->
# 96 "lexer.mll"
        ( raise End_of_file )
# 520 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_scan_rec lexbuf __ocaml_lex_state

and comment level lexbuf =
    __ocaml_lex_comment_rec level lexbuf 37
and __ocaml_lex_comment_rec level lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 99 "lexer.mll"
         ( if level = 0 then scan lexbuf else comment (level-1) lexbuf )
# 531 "lexer.ml"

  | 1 ->
# 100 "lexer.mll"
         ( comment (level+1) lexbuf )
# 536 "lexer.ml"

  | 2 ->
# 101 "lexer.mll"
         ( incr_linenum lexbuf; comment level lexbuf )
# 541 "lexer.ml"

  | 3 ->
# 102 "lexer.mll"
        ( comment level lexbuf )
# 546 "lexer.ml"

  | 4 ->
# 103 "lexer.mll"
         ( raise (Lexer_error "Comments are not closed") )
# 551 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec level lexbuf __ocaml_lex_state

and str_literal lexbuf =
    __ocaml_lex_str_literal_rec lexbuf 45
and __ocaml_lex_str_literal_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 106 "lexer.mll"
         ( printf "STRING (%s)\n" !cur_str; STRING !cur_str )
# 562 "lexer.ml"

  | 1 ->
let
# 107 "lexer.mll"
         c
# 568 "lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 107 "lexer.mll"
           ( cur_str := (!cur_str ^ (Char.escaped c)); str_literal lexbuf )
# 572 "lexer.ml"

  | 2 ->
# 108 "lexer.mll"
        ( raise (Lexer_error "String literal not closed") )
# 577 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_str_literal_rec lexbuf __ocaml_lex_state

;;

# 110 "lexer.mll"
 
  let rec parse lexbuf =
    let _ = scan lexbuf in (* do something *) parse lexbuf;;

  let main () =
    let cin = if Array.length Sys.argv > 1 then open_in Sys.argv.(1) else stdin
    in
    let lexbuf = Lexing.from_channel cin in
    try parse lexbuf with
    | End_of_file -> ()
    | Lexer_error s ->
        let pos = lexbuf.Lexing.lex_curr_p in
        let line = pos.Lexing.pos_lnum in
        let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
        printf "!!! %s [line %d, col %d]\n" s line col; ();;

  let _ = Printexc.print main ();;

# 602 "lexer.ml"
