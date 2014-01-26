(* Yacc parser file is parser.mly and Lex lexer file is lexer.mll *)

open Lexing;;

let rec print_prog es =
  match es with
  | [] -> Printf.printf "\n"
  | (e, (line, col))::es -> 
      Printf.printf "%s [line %d, col %d]\n" (AbSyn.string_of_expr e) line col;
      (print_prog es);;

let print_types ts =
  print_string "Types:\n";
  Hashtbl.iter
    (fun k v -> Printf.printf "%s : %s\n" k (AbSyn.string_of_typ v)) ts;
  print_string "\n";;

let run lexbuf top_lev_env =
  try
    let types, es = Parser.program Lexer.scan lexbuf in
    match es with
    | [] -> true
    | (e, p)::[] ->
      (try
        (*print_types types;*)
        print_string ((AbSyn.string_of_expr e)^" : ");
        print_string (AbSyn.string_of_typ (TyCheck.get_type types top_lev_env [] (e,p))^"\n");
        true
      with
      | TyCheck.Type_error(s) -> print_string (s^"\n"); true)
  with
  | Invalid_argument _ ->
      (let pos = lexbuf.lex_curr_p in
      Printf.printf "syntax error [line %d, col %d]\n" pos.pos_lnum (pos.pos_cnum - pos.pos_bol));
      true
  | End_of_file -> false;;

let main () =
  try
    let cin = if Array.length Sys.argv > 1 then open_in Sys.argv.(1) else stdin in
    let top_level_env = Hashtbl.create 10 in
    let lexbuf = Lexing.from_channel cin in
    let continue = ref true in
    while !continue do
      continue := run lexbuf top_level_env;
      flush stdout
    done
  with End_of_file -> print_string "End of file reached."; exit 0;;

let _ = Printexc.print main ();;

