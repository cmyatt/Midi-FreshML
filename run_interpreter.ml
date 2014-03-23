open Interpreter;;
open Lexing;;

(*
let leftover = ref "";;	(* incomplete exp *)
let exps = ref [];;			(* completed, but unevaluated exps *)

(* Returns a stream containing the next evaulatable chunk of code (i.e. up until ;) *)
let rec repl_lexbuf () =
	let exprs =
		(if (length !exps) > 0 then !exps
		else
			(if !leftover = "" then print_string "# " else print_string "  ";
			let line = read_line () in
			split_delim (regexp ";") line))
	in
	let len = length exprs in
	if len = 0 then repl_lexbuf ()
	else
		match len with
		| 0 -> repl_lexbuf ()
		| 1 -> leftover := (!leftover ^ " " ^ (hd exprs)); repl_lexbuf ()
		| 2 ->
				let s = from_string (!leftover^" "^(hd exprs)^";") in
				leftover := (nth exprs 1);
				exps := [];
				s
		| n ->
				exps := tl exprs;
				let s = from_string (!leftover^" "^(hd exprs)^";") in
				leftover := "";
				s;;

(* TODO Want to abandon current expr on encountering the first error
 * - Getting too many useless error messages atm
 *)

let rec run get_lexbuf top_lev_env delay_perms =
	let env = ref [[]] in
  try
		while true do
			(try
				let atoms, types, es = Parser.program Lexer.scan (get_lexbuf ()) in
				Parsing.clear_parser();	(* free memory used by the parser TODO test if has any effect *)
				(match es with
				| [] -> ()
				| (Directive(Quit, xs), _, p)::[] ->
						if (length xs) = 0 then exit 0
						else print_string ("[Error] Directive 'quit' does not take any arguments " ^
							(string_of_pos p) ^ "\n")
				| (Directive(Use, xs), _, p)::[] ->
						if (length xs) = 1 then
							(try
								let cin = open_in (hd xs) in
								let lb = from_channel cin in
								env := run (fun () -> lb) top_lev_env delay_perms
							with
							| Sys_error s ->
									print_string ("[Error] " ^ s ^ " " ^ (string_of_pos p) ^ "\n"))
						else print_string ("[Error] Directive 'use' expects 1 argument " ^
								(string_of_pos p) ^ "\n")
				| (e, _, p)::[] ->
					(try
						let t = get_type types top_lev_env [] (e, [], p) in
						let env', (v, _, _) = exp_state delay_perms atoms !env [] (e, [], p) in
						env := env';
						(match e with
						| TopLet(ValBind(pat, _), _) ->
								print_string ((extract_ids pat v t) ^ "\n")
						| TopLet(RecF(RecFunc(s, _, _, _, _, _)), _) ->
								print_string ("val " ^ s ^ " : " ^ (string_of_typ t) ^ " = <fun>\n")
						| _ -> print_string ("- : "^(string_of_typ t)^" = "^(string_of_expr v)^"\n"))
					with
					| Type_error s -> print_string ("[Error] "^s^"\n")
					| Run_time_error s -> print_string ("[Error] "^s^"\n")
					| Stack_overflow -> print_string "[Error] Stack overflow\n")
				| _ -> print_string "Parse error: multiple top-level expressions parsed.\n")
			with
			| Lexer.Lexer_error s -> print_string ("[Error] "^s^"\n")
			| Invalid_argument _ ->
					(*let pos = lexbuf.lex_curr_p in*)
					Printf.printf "[Error] Syntax error\n"
					(* [line %d, col %d]\n pos.pos_lnum (pos.pos_cnum - pos.pos_bol) *)
			| Parsing.Parse_error -> ())(*print_string "[error] syntax error\n"; skip_error get_lexbuf)*)
		done; !env
  with End_of_file -> !env;;
*)

let main () =
	try
		let top_level_env = Hashtbl.create 10 in
		let delayed_perms = ref true in
		let lexbuf = ref None in
		let opts = ["-n", Arg.Clear delayed_perms, "Disable delayed permutations"] in
		let usage = "Usage: ./fml [options] [files]" in
		Arg.parse opts (fun s -> lexbuf := Some (from_channel (open_in s))) usage;
		(match !lexbuf with
		| None -> 
				print_string "\tMidi-FreshML version 0.2\n\n";
				run repl_lexbuf top_level_env !delayed_perms
		| Some x -> run (fun () -> x) top_level_env !delayed_perms)
	with
	| Sys_error s -> print_string (s^"\n"); exit 0
	| End_of_file -> print_string "End of file reached.\n"; exit 0;;

let _ = Printexc.print main ();;

