open Interpreter;;
open Lexing;;

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

