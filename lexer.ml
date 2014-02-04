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

  let debug = false;;

  let keyword_tbl =
    create_hashtable 19 [
      ("list", LIST);
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

# 55 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\223\255\224\255\226\255\227\255\004\000\232\255\233\255\
    \236\255\237\255\238\255\239\255\050\000\067\000\068\000\245\255\
    \246\255\247\255\002\000\249\255\250\255\251\255\084\000\192\000\
    \020\001\161\000\171\000\104\001\188\001\016\002\100\002\184\002\
    \012\003\234\255\228\255\244\255\229\255\243\255\225\255\235\255\
    \231\255\074\001\251\255\252\255\253\255\004\000\052\000\255\255\
    \254\255\062\000\253\255\254\255\255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\025\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\015\000\013\000\014\000\255\255\
    \255\255\255\255\007\000\255\255\255\255\255\255\003\000\003\000\
    \003\000\000\000\001\000\003\000\003\000\002\000\003\000\003\000\
    \003\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\003\000\003\000\255\255\
    \255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_default = 
   "\002\000\000\000\000\000\000\000\000\000\255\255\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\255\255\255\255\000\000\
    \000\000\000\000\255\255\000\000\000\000\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\043\000\000\000\000\000\000\000\255\255\255\255\000\000\
    \000\000\051\000\000\000\000\000\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\003\000\004\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \003\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\
    \012\000\011\000\017\000\019\000\008\000\018\000\048\000\016\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\006\000\005\000\013\000\009\000\014\000\040\000\
    \033\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\039\000\038\000\047\000\015\000\020\000\
    \052\000\022\000\022\000\022\000\022\000\022\000\023\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\024\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\007\000\000\000\010\000\036\000\
    \037\000\035\000\034\000\000\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\000\000\
    \000\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\026\000\
    \000\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\000\000\000\000\022\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\000\000\000\000\000\000\000\000\022\000\
    \000\000\030\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\000\000\000\000\050\000\000\000\
    \000\000\000\000\000\000\000\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\044\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\000\000\
    \000\000\000\000\045\000\022\000\046\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\027\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\000\000\000\000\000\000\000\000\022\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\028\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\000\000\
    \000\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
    \022\000\029\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\042\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\000\000\000\000\000\000\000\000\022\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\000\000\
    \000\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \031\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\000\000\000\000\000\000\000\000\022\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\032\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\000\000\
    \000\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
    \022\000\029\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\000\000\
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
    \000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\045\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\
    \018\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\012\000\012\000\046\000\000\000\000\000\
    \049\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\022\000\000\000\255\255\000\000\013\000\
    \013\000\014\000\014\000\255\255\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\255\255\
    \255\255\255\255\255\255\022\000\255\255\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\025\000\
    \255\255\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\026\000\026\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\255\255\255\255\023\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\255\255\255\255\255\255\255\255\023\000\
    \255\255\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\024\000\255\255\255\255\049\000\255\255\
    \255\255\255\255\255\255\255\255\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\041\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\255\255\
    \255\255\255\255\041\000\024\000\041\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\027\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\255\255\255\255\255\255\255\255\027\000\
    \255\255\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\028\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\255\255\
    \255\255\255\255\255\255\028\000\255\255\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\028\000\
    \028\000\028\000\028\000\028\000\028\000\028\000\028\000\029\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\041\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\255\255\255\255\255\255\255\255\029\000\
    \255\255\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\030\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\255\255\
    \255\255\255\255\255\255\030\000\255\255\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\031\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\255\255\255\255\255\255\255\255\031\000\
    \255\255\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\032\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\255\255\
    \255\255\255\255\255\255\032\000\255\255\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\255\255\
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
    \255\255\255\255\255\255\255\255\255\255";
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
# 60 "lexer.mll"
              inum
# 365 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 60 "lexer.mll"
                   (
      let n = int_of_string inum in if debug then printf "INT (%d)\n" n else ();
      INT n
    )
# 372 "lexer.ml"

  | 1 ->
let
# 64 "lexer.mll"
                         rnum
# 378 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 64 "lexer.mll"
                              (
      let n = float_of_string rnum in if debug then printf "REAL (%f)\n" n else ();
      REAL n
    )
# 385 "lexer.ml"

  | 2 ->
let
# 69 "lexer.mll"
               b
# 391 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 69 "lexer.mll"
                 ( if debug then printf "BOOL (%s)\n" b else (); BOOL (bool_of_string b) )
# 395 "lexer.ml"

  | 3 ->
let
# 70 "lexer.mll"
          word
# 401 "lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 70 "lexer.mll"
               (
      try let kw = Hashtbl.find keyword_tbl word in if debug then printf "%s\n" word else (); kw with
      | Not_found -> if debug then printf "ID (%s)\n" word else (); ID word
    )
# 408 "lexer.ml"

  | 4 ->
# 74 "lexer.mll"
         ( cur_str := ""; str_literal lexbuf )
# 413 "lexer.ml"

  | 5 ->
# 75 "lexer.mll"
        ( if debug then printf "DONT_CARE\n" else (); DONT_CARE )
# 418 "lexer.ml"

  | 6 ->
# 76 "lexer.mll"
        ( if debug then printf "BIN_OP (+)\n" else (); BIN_OP(AbSyn.Add) )
# 423 "lexer.ml"

  | 7 ->
# 77 "lexer.mll"
        ( if debug then printf "BIN_OP (-)\n" else (); BIN_OP(AbSyn.Sub) )
# 428 "lexer.ml"

  | 8 ->
# 78 "lexer.mll"
        ( if debug then printf "STAR\n" else (); STAR )
# 433 "lexer.ml"

  | 9 ->
# 79 "lexer.mll"
        ( if debug then printf "BIN_OP (/)\n" else (); BIN_OP(AbSyn.Div) )
# 438 "lexer.ml"

  | 10 ->
# 80 "lexer.mll"
        ( if debug then printf "BIN_OP (^)\n" else (); BIN_OP(AbSyn.Concat) )
# 443 "lexer.ml"

  | 11 ->
# 81 "lexer.mll"
         ( if debug then printf "GT_EQ\n" else (); BIN_OP(AbSyn.Gteq) )
# 448 "lexer.ml"

  | 12 ->
# 82 "lexer.mll"
         ( if debug then printf "LT_EQ\n" else (); BIN_OP(AbSyn.Lteq) )
# 453 "lexer.ml"

  | 13 ->
# 83 "lexer.mll"
         ( if debug then printf "LT\n" else (); BIN_OP(AbSyn.Lt) )
# 458 "lexer.ml"

  | 14 ->
# 84 "lexer.mll"
         ( if debug then printf "GT\n" else (); BIN_OP(AbSyn.Gt) )
# 463 "lexer.ml"

  | 15 ->
# 85 "lexer.mll"
         ( if debug then printf "L_PAREN\n" else (); L_PAREN )
# 468 "lexer.ml"

  | 16 ->
# 86 "lexer.mll"
         ( if debug then printf "R_PAREN\n" else (); R_PAREN )
# 473 "lexer.ml"

  | 17 ->
# 87 "lexer.mll"
         ( if debug then printf "UN_OP (~)\n" else (); UN_OP(AbSyn.Neg) )
# 478 "lexer.ml"

  | 18 ->
# 88 "lexer.mll"
         ( if debug then printf "EQUAL\n" else (); EQUAL )
# 483 "lexer.ml"

  | 19 ->
# 89 "lexer.mll"
         ( if debug then printf "COMMA\n" else (); COMMA )
# 488 "lexer.ml"

  | 20 ->
# 90 "lexer.mll"
         ( if debug then printf "UNIT\n" else (); UNIT )
# 493 "lexer.ml"

  | 21 ->
# 91 "lexer.mll"
         ( if debug then printf "ARROW\n" else (); ARROW )
# 498 "lexer.ml"

  | 22 ->
# 92 "lexer.mll"
         ( if debug then printf "BAR\n" else (); BAR )
# 503 "lexer.ml"

  | 23 ->
# 93 "lexer.mll"
         ( if debug then printf "COLON\n" else (); COLON )
# 508 "lexer.ml"

  | 24 ->
# 94 "lexer.mll"
         ( if debug then printf "DBL_SEMI\n" else (); DBL_SEMI )
# 513 "lexer.ml"

  | 25 ->
# 95 "lexer.mll"
         ( if debug then printf "SEMI\n" else (); SEMI )
# 518 "lexer.ml"

  | 26 ->
# 96 "lexer.mll"
         ( if debug then printf "DBL_LT\n" else (); DBL_LT )
# 523 "lexer.ml"

  | 27 ->
# 97 "lexer.mll"
         ( if debug then printf "DBL_GT\n" else (); DBL_GT )
# 528 "lexer.ml"

  | 28 ->
# 98 "lexer.mll"
         ( incr_linenum lexbuf; scan lexbuf )
# 533 "lexer.ml"

  | 29 ->
# 99 "lexer.mll"
               ( scan lexbuf )
# 538 "lexer.ml"

  | 30 ->
# 100 "lexer.mll"
         ( comment 0 lexbuf )
# 543 "lexer.ml"

  | 31 ->
let
# 101 "lexer.mll"
         c
# 549 "lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 101 "lexer.mll"
           ( raise (Lexer_error ("Unrecognised character: "^(Char.escaped c))) )
# 553 "lexer.ml"

  | 32 ->
# 102 "lexer.mll"
        ( raise End_of_file )
# 558 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_scan_rec lexbuf __ocaml_lex_state

and comment level lexbuf =
    __ocaml_lex_comment_rec level lexbuf 41
and __ocaml_lex_comment_rec level lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 105 "lexer.mll"
         ( if level = 0 then scan lexbuf else comment (level-1) lexbuf )
# 569 "lexer.ml"

  | 1 ->
# 106 "lexer.mll"
         ( comment (level+1) lexbuf )
# 574 "lexer.ml"

  | 2 ->
# 107 "lexer.mll"
         ( incr_linenum lexbuf; comment level lexbuf )
# 579 "lexer.ml"

  | 3 ->
# 108 "lexer.mll"
        ( comment level lexbuf )
# 584 "lexer.ml"

  | 4 ->
# 109 "lexer.mll"
         ( raise (Lexer_error "Comments are not closed") )
# 589 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec level lexbuf __ocaml_lex_state

and str_literal lexbuf =
    __ocaml_lex_str_literal_rec lexbuf 49
and __ocaml_lex_str_literal_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 112 "lexer.mll"
         ( if debug then printf "STRING (%s)\n" !cur_str else (); STRING !cur_str )
# 600 "lexer.ml"

  | 1 ->
let
# 113 "lexer.mll"
         c
# 606 "lexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 113 "lexer.mll"
           ( cur_str := (!cur_str ^ (Char.escaped c)); str_literal lexbuf )
# 610 "lexer.ml"

  | 2 ->
# 114 "lexer.mll"
        ( raise (Lexer_error "String literal not closed") )
# 615 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_str_literal_rec lexbuf __ocaml_lex_state

;;

# 116 "lexer.mll"
 
  (*
  let rec parse lexbuf =
    let _ = scan lexbuf in (* do something *) parse lexbuf;;
  *)

  (*
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
  *)

# 644 "lexer.ml"
