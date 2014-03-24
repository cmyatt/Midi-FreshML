open Benchmark;;
open Lexing;;
open AbSyn;;
open TyCheck;;
open Lexing;;
open List;;

let top_level_env = Hashtbl.create 10;;
let plc_lexbuf = from_channel (open_in "tests/dpTestLarge.fml");;
let run_plc = Interpreter.run (fun () -> plc_lexbuf) top_level_env;;
let results = ref [];;

(* TODO Benchmark just the evaluation code and not the whole lexing -->* evaluation flow. *)

(* Warm-up run *)
(*let _ = latencyN ~style:Nil ~repeat:1 (Int64.of_int 10000) [("ignore", run_plc, false)];;*)

let rec run get_lexbuf top_lev_env delay_perms =
  let env = ref [[]] in
  try
    while true do
      (try
        let atoms, types, es = Parser.program Lexer.scan (get_lexbuf ()) in
        Parsing.clear_parser(); (* free memory used by the parser TODO test if has any effect *)
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
            let f = (fun b -> Interpreter.exp_state b atoms !env [] (e, [], p)) in
            results := (latencyN ~style:Auto ~repeat:1 (Int64.of_int 1)
                          [("plc - no delay", f, false);
                          ("plc - delayed", f, true)]) @ !results;
            let env', (v, _, _) = Interpreter.exp_state delay_perms atoms !env [] (e, [], p) in
            env := env';
            (match e with
            | TopLet(ValBind(pat, _), _) ->
                print_string ((extract_ids pat v t) ^ "\n")
            | TopLet(RecF(RecFunc(s, _, _, _, _, _)), _) ->
                print_string ("val " ^ s ^ " : " ^ (string_of_typ t) ^ " = <fun>\n")
            | _ -> print_string ("- : "^(string_of_typ t)^" = "^(string_of_expr v)^"\n"))
          with
          | Type_error s -> print_string ("[Error] "^s^"\n")
          | Interpreter.Run_time_error s -> print_string ("[Error] "^s^"\n")
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

let i = ref 0;;
while !i < 50000 do
  i := !i+1;
  run (fun () -> plc_lexbuf) top_level_env true
done;;
tabulate !results;;

