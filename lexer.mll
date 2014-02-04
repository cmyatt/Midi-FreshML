{
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
}

(* Definitions *)
let digit = ['0'-'9']
let id = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

(* Rules *)
rule scan = parse
  | digit+ as inum {
      let n = int_of_string inum in if debug then printf "INT (%d)\n" n else ();
      INT n
    }
  | digit+ '.' digit* as rnum {
      let n = float_of_string rnum in if debug then printf "REAL (%f)\n" n else ();
      REAL n
    }
  | "true"
  | "false" as b { if debug then printf "BOOL (%s)\n" b else (); BOOL (bool_of_string b) }
  | id as word {
      try let kw = Hashtbl.find keyword_tbl word in if debug then printf "%s\n" word else (); kw with
      | Not_found -> if debug then printf "ID (%s)\n" word else (); ID word
    }
  | '\"' { cur_str := ""; str_literal lexbuf }
  | '_' { if debug then printf "DONT_CARE\n" else (); DONT_CARE }
  | '+' { if debug then printf "BIN_OP (+)\n" else (); BIN_OP(AbSyn.Add) }
  | '-' { if debug then printf "BIN_OP (-)\n" else (); BIN_OP(AbSyn.Sub) }
  | '*' { if debug then printf "STAR\n" else (); STAR }
  | '/' { if debug then printf "BIN_OP (/)\n" else (); BIN_OP(AbSyn.Div) }
  | '^' { if debug then printf "BIN_OP (^)\n" else (); BIN_OP(AbSyn.Concat) }
  | ">=" { if debug then printf "GT_EQ\n" else (); BIN_OP(AbSyn.Gteq) }
  | "<=" { if debug then printf "LT_EQ\n" else (); BIN_OP(AbSyn.Lteq) }
  | '<'  { if debug then printf "LT\n" else (); BIN_OP(AbSyn.Lt) }
  | '>'  { if debug then printf "GT\n" else (); BIN_OP(AbSyn.Gt) }
  | '('  { if debug then printf "L_PAREN\n" else (); L_PAREN }
  | ')'  { if debug then printf "R_PAREN\n" else (); R_PAREN }
  | '~'  { if debug then printf "UN_OP (~)\n" else (); UN_OP(AbSyn.Neg) }
  | '='  { if debug then printf "EQUAL\n" else (); EQUAL }
  | ','  { if debug then printf "COMMA\n" else (); COMMA }
  | "()" { if debug then printf "UNIT\n" else (); UNIT }
  | "->" { if debug then printf "ARROW\n" else (); ARROW }
  | '|'  { if debug then printf "BAR\n" else (); BAR }
  | ':'  { if debug then printf "COLON\n" else (); COLON }
  | ";;" { if debug then printf "DBL_SEMI\n" else (); DBL_SEMI }
  | ';'  { if debug then printf "SEMI\n" else (); SEMI }
  | "<<" { if debug then printf "DBL_LT\n" else (); DBL_LT }
  | ">>" { if debug then printf "DBL_GT\n" else (); DBL_GT }
  | '\n' { incr_linenum lexbuf; scan lexbuf }
  | [' ' '\t'] { scan lexbuf }
  | "(*" { comment 0 lexbuf }
  | _ as c { raise (Lexer_error ("Unrecognised character: "^(Char.escaped c))) }
  | eof { raise End_of_file }

and comment level = parse
  | "*)" { if level = 0 then scan lexbuf else comment (level-1) lexbuf }
  | "(*" { comment (level+1) lexbuf }
  | '\n' { incr_linenum lexbuf; comment level lexbuf }
  | _		 { comment level lexbuf }
  | eof	 { raise (Lexer_error "Comments are not closed") }

and str_literal = parse
  | '\"' { if debug then printf "STRING (%s)\n" !cur_str else (); STRING !cur_str }
  | _ as c { cur_str := (!cur_str ^ (Char.escaped c)); str_literal lexbuf }
  | eof { raise (Lexer_error "String literal not closed") }

{
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
}

