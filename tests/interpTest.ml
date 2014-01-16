(* Interpreter test *)
open AbSyn
open Interpreter;;

let p = (0, 0);;

let atoms = Hashtbl.create 2;;

(* Add name types a and b *)
Hashtbl.add atoms "a" 0;;
Hashtbl.add atoms "b" 0;;

(* Create an environment *)
let myEnv = [[
  "x", (IntLiteral(5), p);
  "z", ((gen_atom atoms "a"), p);
  "y", ((gen_atom atoms "a"), p)
]];;


let swapEx = Swap((Id("y"), p), (Id("z"), p), (Id("y"), p));;

let (a, e, (v, _)) = exp_state atoms myEnv [] (swapEx, p);;

let (y_val, _) = lookup "y" myEnv;;
let (z_val, _) = lookup "z" myEnv;;

print_string ("y = "^(AbSyn.string_of_expr y_val)^"\n");
print_string ("z = "^(AbSyn.string_of_expr z_val)^"\n");
print_string ((AbSyn.string_of_expr swapEx)^" ==> "^(AbSyn.string_of_expr v));;
