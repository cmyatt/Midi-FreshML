open Benchmark;;
open Lexing;;
open AbSyn;;
open TyCheck;;
open Lexing;;
open List;;

(* Benchmark push function *)
let test_push () =
	let pi = [("a", 0), ("a", 1)] in
	let e = (AbSyn.EmptySlot, [], (0, 0)) in
	let f e =
		let _ = Interpreter.push pi e in ()
	in
	let results = (latencyN ~style:Auto ~repeat:4 (Int64.of_int 20000000) [("push", f, e)]) in
	tabulate results;;

(* Benchmark permute vs. swap *)
let test_primitives () =
	let pi = [("a", 0), ("a", 1)] in
	let p = (0, 0) in
	let env = [
		"x", (IntLiteral(0), [], p);
		"y", (BoolLiteral(true), [], p);
		"z", (NameLiteral("a", 0), [], p)]
	in
	let v1 =
		(Ctor("C",
			(Pair(
				(Ctor("B",
					(Lambda("f", IntT, (EmptySlot, [], p), env), [], p)),
					[], p),
				(Ctor("D", (NameAb((NameLiteral("b", 6), [], p), (IntLiteral(4), [], p)), [], p)), [], p)),
			[], p)), [], p)
	in
	let v2 = (Ctor("C", (NameLiteral("a", 2), [], p)), [], p) in
	let v3 = (Ctor("C", (NameLiteral("a", 0), [], p)), [], p) in
	let v4 = (NameAb((NameLiteral("a", 1), [], p), v2), pi, p) in
	let f a =
		let _ = Interpreter.permute pi a in ()
	in
	let g v a =
		let _ = Interpreter.swap ("a", 0) ("a", 1) v in ()
	in
	let h a =
		let _ = Interpreter.push_perm v4 in ()
	in
	let results =
		(latencyN ~repeat:4 (Int64.of_int 20000000)
			[("permute (no match)", f, ("a", 2));
			 ("permute (match)", f, ("a", 0));
			 ("swap (10 deep)", g v1, ("", -1));
			 ("swap (no match, 1 deep)", g v2, ("", -1));
			 ("swap (match, 1 deep)", g v3, ("", -1));
			 ("push_perm", h, ("", -1))])
	in
	tabulate results;;

let reps = ref 2;;
let iters = ref 800;;
let exp_no = ref 0;;

(* Benchmark the given function (expect it to evaluate an expression)
 *  and print the results iff run = true
 *)
let run_bench run f =
	if run then
		let results = (latencyN ~style:Auto ~repeat:!reps (Int64.of_int !iters)
										[("no delay", f, false);
										("delayed", f, true)])
		in tabulate results
	else ();;

let clear_counts () =
	Interpreter.push_count := 0;
	Interpreter.permute_count := 0;
	Interpreter.pi_length := 0;
	Interpreter.push_perm_count := 0;
	Interpreter.swap_count := 0;
	Interpreter.swap_depth := 0;;

let print_stats b delay_perms =
	if not b then ()
	else
		(if delay_perms then
			Printf.printf
			"pushes: %d, perms: %d, avg. pi length: %d, push_perm count: %d\n"
			!Interpreter.push_count
			!Interpreter.permute_count
			(if !Interpreter.permute_count > 0 then !Interpreter.pi_length / !Interpreter.permute_count else -1)
			!Interpreter.push_perm_count
		else
			Printf.printf
			"swaps: %d, avg. swap depth: %d\n"
			!Interpreter.swap_count
			(if !Interpreter.swap_count > 0 then !Interpreter.swap_depth / !Interpreter.swap_count else -1));
		clear_counts();;

(* Modified version of Interpreter.run to benchmark the
   evaluation of a particular expression *)
let rec run get_lexbuf top_lev_env delay_perms verbose =
  let env = ref [[]] in
  try
		let count = ref 0 in
    while true do
			count := !count + 1;
			if verbose then Printf.printf "* Expr. no: %d...." !count else ();
      (try
        let atoms, types, es = Parser.program Lexer.scan (get_lexbuf ()) in
        Parsing.clear_parser();
        (match es with
        | [] -> ()
        | (Directive(Quit, xs), _, p)::[] ->
            if (length xs) = 0 then exit 0
            else print_string ("[Error] Directive 'quit' does not take any arguments "
              ^ (string_of_pos p) ^ "\n")
        | (Directive(Use, xs), _, p)::[] ->
            if (length xs) = 1 then
              (try
                let cin = open_in (hd xs) in
                let lb = from_channel cin in
                env := run (fun () -> lb) top_lev_env delay_perms verbose
              with
              | Sys_error s ->
                  print_string ("[Error] " ^ s ^ " " ^ (string_of_pos p) ^ "\n"))
            else print_string ("[Error] Directive 'use' expects 1 argument " ^
                (string_of_pos p) ^ "\n")
        | (e, _, p)::[] ->
          (try
            let _ = get_type types top_lev_env [] (e, [], p) in
            let f = (fun b -> let _ = Interpreter.exp_state b atoms !env [] (e, [], p) in ()) in
						run_bench (!count = !exp_no) f;
						clear_counts ();
						let env', (v, _, _) = Interpreter.exp_state delay_perms atoms !env [] (e, [], p) in
						print_stats verbose delay_perms;
            env := env'
          with
          | Type_error s -> print_string ("[Error] "^s^"\n")
          | Interpreter.Run_time_error s -> print_string ("[Error] "^s^"\n")
          | Stack_overflow -> print_string "[Error] Stack overflow\n")
        | _ -> print_string "Parse error: multiple top-level expressions parsed.\n")
      with
      | Lexer.Lexer_error s -> print_string ("[Error] "^s^"\n")
      | Invalid_argument _ ->
          Printf.printf "[Error] Syntax error\n"
      | Parsing.Parse_error -> ())
    done; !env
  with End_of_file -> !env;;

(*
	Options used to generate results:
		dpTest.fml: -r 2 -i 150 -e 6
		dpTestSmall.fml: -r 2 -i 362 -e 6
		plc.fml: -r 2 -i 800 -e 40
		plc-nbe.fml: -r 2 -i 1276 -e 38
		pi-calculator.fml: -r 2 -i 9500 -e 44
	
	To get results without all program output:
		$ ./bin/bench-fml [options] [file] > temp.txt; less temp.txt | grep /s
*)

let test_whole file =
	let env = Hashtbl.create 10 in
	let x = open_in !file in
	let f dp =
		seek_in x 0;
		(let lexbuf = from_channel x in
		let _ = Interpreter.run (fun () -> lexbuf) env dp in
		Hashtbl.clear Parser.atoms;
		Hashtbl.clear Parser.types;
		Hashtbl.clear env)
	in
	let results = (latencyN ~style:Auto ~repeat:!reps (Int64.of_int !iters)
									[("no delay", f, false);
									("delayed", f, true)])
	in
	tabulate results;;

let main () =
	try
		let top_level_env = Hashtbl.create 10 in
		let file = ref "examples/plc.fml" in
		let verbose = ref false in
		let primitives = ref false in
		let delay_perms = ref true in
		let whole = ref false in
		let opts =
			["-p", Arg.Set primitives, "Benchmark primitive functions";
			 "-r", Arg.Set_int reps, "Set the number of repetitions";
			 "-i", Arg.Set_int iters, "Set the number of iterations";
			 "-e", Arg.Set_int exp_no, "Set the number of the expression to benchmark";
			 "-v", Arg.Set verbose, "Print additional stats";
			 "-w", Arg.Set whole, "Benchmark the whole program execution";
			 "-n", Arg.Clear delay_perms, "Don't use delayed perms for non-benchmarked expressions"]
		in
		let usage = "Usage: ./bench-fml [options] [file]" in
		Parser.print_info := false;
		(Arg.parse opts (fun s -> file := s) usage;
		if !whole then test_whole file
		else (if !primitives then let _ = test_primitives () in exit 0
		else
			let lexbuf = from_channel (open_in !file) in
			let _ = run (fun () -> lexbuf) top_level_env !delay_perms !verbose in
			print_string "\n"; exit 0))
	with Sys_error s -> print_string (s ^ "\n"); exit 0;;

let _ = Printexc.print main ();;

