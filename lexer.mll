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
}

(* Definitions *)
let digit = ['0'-'9']
let id = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

(* Rules *)
rule scan = parse
  | digit+ as inum {
      let n = int_of_string inum in printf "INT (%d)\n" n;
      INT n
    }
  | digit+ '.' digit* as rnum {
      let n = float_of_string rnum in printf "REAL (%f)\n" n;
      REAL n
    }
  | id as word {
      try let kw = Hashtbl.find keyword_tbl word in printf "%s\n" word; kw with
      | Not_found -> printf "ID (%s)\n" word; ID word
    }
  | '\"' { cur_str := ""; str_literal lexbuf }
  | "true"
  | "false" as b { printf "BOOL (%s)\n" b; BOOL (bool_of_string b) }
  | '_' { printf "DONT_CARE\n"; DONT_CARE }
  | '+' { printf "BIN_OP (+)\n"; BIN_OP(AbSyn.Add) }
  | '-' { printf "BIN_OP (-)\n"; BIN_OP(AbSyn.Sub) }
  | '*' { printf "STAR\n"; STAR }
  | '/' { printf "BIN_OP (/)\n"; BIN_OP(AbSyn.Div) }
  | '('  { printf "L_PAREN\n"; L_PAREN }
  | ')'  { printf "R_PAREN\n"; R_PAREN }
  | '~'  { printf "UN_OP (~)\n"; UN_OP(AbSyn.Neg) }
  | '='  { printf "EQUAL\n"; EQUAL }
  | ','  { printf "COMMA\n"; COMMA }
  | "()" { printf "UNIT\n"; UNIT }
  | "->" { printf "ARROW\n"; ARROW }
  | '|'  { printf "BAR\n"; BAR }
  | ':'  { printf "COLON\n"; COLON }
  | ";;" { printf "DBL_SEMI\n"; DBL_SEMI }
  | ';'  { printf "SEMI\n"; SEMI }
  | "<<" { printf "DBL_LT\n"; DBL_LT }
  | ">>" { printf "DBL_GT\n"; DBL_GT }
  | '<'  { printf "LT\n"; LT }
  | '>'  { printf "GT\n"; GT }
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
  | '\"' { printf "STRING (%s)\n" !cur_str; STRING !cur_str }
  | _ as c { cur_str := (!cur_str ^ (Char.escaped c)); str_literal lexbuf }
  | eof { raise (Lexer_error "String literal not closed") }

{
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
}

