open Lexing;;

let leftover = ref "";;	(* incomplete exp *)
let exps = ref [];;			(* completed, but unevaluated exps *)

(* TODO ignore pos when in repl mode. *)

(* Returns a stream containing the next evaulatable chunk of code (i.e. up until ;) *)
let rec repl_lexbuf () =
	let exprs =
		(if (List.length !exps) > 0 then !exps
		else
			(if !leftover = "" then print_string "# " else print_string "  ";
			let line = read_line () in
			Str.split_delim (Str.regexp ";") line))
	in
	let len = List.length exprs in
	if len = 0 then repl_lexbuf ()
	else
		match len with
		| 0 -> repl_lexbuf ()
		| 1 -> leftover := (!leftover ^ " " ^ (List.hd exprs)); repl_lexbuf ()
		| 2 ->
				let s = from_string (!leftover^" "^(List.hd exprs)^";") in
				leftover := (List.nth exprs 1);
				exps := [];
				s
		| n ->
				exps := List.tl exprs;
				let s = from_string (!leftover^" "^(List.hd exprs)^";") in
				leftover := "";
				s;;

(* TODO Add support for directives, e.g. #quit; and #open <filename>; *)

(* TODO Want to abandon current expr on encountering the first error
 * - Getting too many useless error messages atm
 *)

let rec run get_lexbuf top_lev_env =
  try
		let env = ref [[]] in
		while true do
			(try
				let atoms, types, es = Parser.program Lexer.scan (get_lexbuf ()) in
				(match es with
				| [] -> ()
				| (e, p)::[] ->
					(try
						let t = TyCheck.get_type types top_lev_env [] (e, p) in
						let env', (v, _) = Interpreter.exp_state atoms !env [] (e, p) in
						env := env';
						(match e with
						| AbSyn.TopLet(AbSyn.ValBind(pat, _), _) ->
								print_string ((AbSyn.extract_ids pat v t) ^ "\n")
						| AbSyn.TopLet(AbSyn.RecF(AbSyn.RecFunc(s, _, _, _, _, _)), _) ->
								print_string ("val " ^ s ^ " : " ^ (AbSyn.string_of_typ t) ^ " = <fun>\n")
						| _ -> print_string ("- : "^(AbSyn.string_of_typ t)^" = "^(AbSyn.string_of_expr v)^"\n"))
					with
					| TyCheck.Type_error s -> print_string ("[Error] "^s^"\n")
					| Interpreter.Run_time_error s -> print_string ("[Error] "^s^"\n")
					| Stack_overflow -> print_string "[Error] Stack overflow\n")
				| _ -> print_string "Parse error: multiple top-level expressions parsed.\n")
			with
			| Invalid_argument _ ->
					(*let pos = lexbuf.lex_curr_p in*)
					Printf.printf "[Error] Syntax error\n"(* [line %d, col %d]\n pos.pos_lnum (pos.pos_cnum - pos.pos_bol)*)
			| Parsing.Parse_error -> print_string "[Error] Syntax error\n")
		done
  with End_of_file -> ();;

let main () =
	try
		let top_level_env = Hashtbl.create 10 in
    if Array.length Sys.argv > 1 then
			let cin = open_in Sys.argv.(1) in
			let lexbuf = from_channel cin in
			run (fun () -> lexbuf) top_level_env
		else
			(print_string "\tMidi-FreshML version 0.1\n\n";
			run repl_lexbuf top_level_env)
  with End_of_file -> print_string "End of file reached.\n"; exit 0;;

let _ = Printexc.print main ();;

