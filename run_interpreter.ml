
(*
let main () =
	while true do
		let line = read_line () in
		(* Split by SEMI - if none, then cache line and read next line *)
		let exprs = Str.split_delim (Str.regexp ";") line in
		let len = List.length exprs in
		if len > 0 then
			(* For each member, parse, typecheck and evaluate
			 * If final member (once trimmed) != "" then save it for next time *)
		(*let types, exs = Parser.program Lexer.scan (Lexing.from_string line) in*)
		List.iter (fun s -> Printf.printf "%s|\n" s) exprs
	done;;
*)

let run lexbuf top_lev_env =
  try
		let env = ref [[]] in
		while true do
			let atoms, types, es = Parser.program Lexer.scan lexbuf in
			match es with
			| [] -> () (* TODO: print ack in parser on reading new user type *)
			| (e, p)::[] ->
				(try
					let t = TyCheck.get_type types top_lev_env [] (e, p) in
					let env', (v, _) = Interpreter.exp_state atoms !env [] (e, p) in
					env := env';
					(* TODO: if top-level let, want to print e.g. inc : (int -> int) rather
					 * than function body of inc *)
					(match e with
					| AbSyn.TopLet(AbSyn.ValBind(pat, _), _) ->
							print_string ((AbSyn.extract_ids pat v t) ^ "\n")
					| AbSyn.TopLet(AbSyn.RecF(AbSyn.RecFunc(s, _, _, _, _, _)), _) ->
							print_string ("val " ^ s ^ " : " ^ (AbSyn.string_of_typ t) ^ " = <fun>\n")
					| _ -> print_string ("- : "^(AbSyn.string_of_typ t)^" = "^(AbSyn.string_of_expr v)^"\n"))
				with
				| TyCheck.Type_error s -> print_string ("[Error] "^s^"\n")
				| Interpreter.Run_time_error s -> print_string ("[Error] "^s^"\n"))
			| _ -> print_string "Parse error: multiple top-level expressions parsed.\n"
		done
  with
  | Invalid_argument _ ->
      (*
			let pos = lexbuf.lex_curr_p in
      Printf.printf "syntax error [line %d, col %d]\n" pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
			*)
      Printf.printf "syntax error\n"
  | End_of_file -> ();;

let main () =
	try
    if Array.length Sys.argv > 1 then
			let cin = open_in Sys.argv.(1) in
			let top_level_env = Hashtbl.create 10 in
			let lexbuf = Lexing.from_channel cin in
			run lexbuf top_level_env
		else print_string "[Usage] ./fml <filename>\n"
  with End_of_file -> print_string "End of file reached.\n"; exit 0;;

let _ = Printexc.print main ();;

