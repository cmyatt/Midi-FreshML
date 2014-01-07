(* Yacc parser file is parser.mly and Lex lexer file is lexer.mll *)
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

let main () =
  try
    let cin =
      if Array.length Sys.argv > 1
      then open_in Sys.argv.(1)
      else stdin
    in
    let lexbuf = Lexing.from_channel cin in
    while true do
      let types, (e, p)::es = Parser.program Lexer.scan lexbuf in
      (try
        print_types types;
        print_string ((AbSyn.string_of_expr e)^" : ");
        print_string ((AbSyn.string_of_typ (TyCheck.get_type types [] (e,p))^"\n"))
      with
      | TyCheck.Type_error(s) -> print_string (s^"\n"));
      (print_prog es)
    done
  with End_of_file -> print_string "End of file reached."; exit 0;;

let _ = Printexc.print main ();;
