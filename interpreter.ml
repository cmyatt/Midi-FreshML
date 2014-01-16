open AbSyn;;

exception Run_time_error of string;;

(* x : 'a
 * env : (('a, 'b) list) list
 * Return true iff x is in the head of the env list
 *)
let rec lookup s env =
  let rec look x ys =
    match ys with
    | [] -> raise Not_found
    | (y, z)::ys -> if x=y then z else look x ys
  in
  match env with
  | [] -> raise Not_found
  | xs::xss -> look s xs;;

(* The atoms Hashtbl maintains a count for the number of generated atoms of each
 * type. To generate a new one, get the count (=n), increment it in atoms, and
 * return the NameLiteral (<name type id>, n).
 *)
let gen_atom atoms s =
  try
    let n = Hashtbl.find atoms s in
    Hashtbl.add atoms s (n+1);
    NameLiteral(Name(s, n))
  with Not_found -> raise (Run_time_error ("Invalid name type: "^s));;

(* Swap atoms a1 and a2 in expression v.
 * Invariant: is_val v = true
 *)
let rec swap a1 a2 v =
  match v with 
  | NameLiteral(n), p -> 
      if n = a1 then (NameLiteral(a2), p)
      else if n = a2 then (NameLiteral(a1), p) else (NameLiteral(n), p)
  | Ctor(s, e), p -> (Ctor(s, (swap a1 a2 e)), p)
  | NameAb(e1, e2), p -> (NameAb(swap a1 a2 e1, swap a1 a2 e2), p)
  | Unit, p -> (Unit, p)
  | Pair(e1, e2), p -> (Pair(swap a1 a2 e1, swap a1 a2 e2), p)
  | Lambda(s, t, e, env), p -> (Lambda(s, t, e, swap_env a1 a2 env), p)
  | RecFunc(s1, s2, t1, t2, e, env), p ->
      (RecFunc(s1, s2, t1, t2, e, swap_env a1 a2 env), p)
  | _ -> raise (Run_time_error "Swap called on non-value expression")

(* Swap atoms a1 and a2 in the environment list env
 * Only does swaps in the head of the list as per the rules for ((a a') * E)
 *)
and swap_env a1 a2 env =
  match env with
  | [] -> []
  | xs -> List.map (fun (x, v) -> (x, swap a1 a2 v)) xs;;


(*********************************************************************************
 * We assumme that the typechecker has been run on the expressions passed to the
 * state functions. This means we don't have to check for certain errors (e.g.
 * that the values being compared in an if expression are of the same name type).
 *
 ********************************************************************************)

(* atoms - Hashtbl (string, int)
 * env - ((string, val) list) list
 * fs - expr list
 * ast - exp
 *
 * TODO be sure to check for values in exp_state - if so, then forward straight
 * to val_state.
 *
 * Returns a 3-tuple of (new atoms, new env, value)
 *)
let rec exp_state atoms env fs ast =
  if is_val ast then val_state atoms env fs ast
  else
    match ast with
    | Id(s), _ -> val_state atoms env fs (lookup s env)
    | Ctor(s, (e, p1)), p2 ->
        val_state atoms env ((Ctor(s, (EmptySlot, p1)), p2)::fs) (e, p1)
    | Fresh(s), p -> let a = gen_atom atoms s in val_state atoms env fs (a, p)
    | If((e1, p1), e2, e3, e4), p2 ->
        exp_state atoms env ((If((EmptySlot, p1), e2, e3, e4), p2)::fs) (e1, p1)
    | Swap((e1, p1), e2, e3), p2 ->
        exp_state atoms env ((Swap((EmptySlot, p1), e2, e3), p2)::fs) (e1, p1)
    | NameAb((e1, p1), e2), p2 ->
        exp_state atoms env ((NameAb((EmptySlot, p1), e2), p2)::fs) (e1, p1)

(* Invariant: is_val ast = true *)
and val_state atoms env fs ast =
  match fs with
  | [] -> (atoms, env, ast)
  | (EofFunc, _)::xs -> val_state atoms (List.tl env) xs ast
  | (Ctor(s, (EmptySlot, _)), p)::xs -> val_state atoms env xs (Ctor(s, ast), p)
  | (If((EmptySlot, _), (e1, p1), e2, e3), p2)::xs ->
      exp_state atoms env ((If(ast, (EmptySlot, p1), e2, e3), p2)::xs) (e1, p1)
  | (If((a1, _), (EmptySlot, _), e1, e2), _)::xs ->
      let (a2, _) = ast in
      if a1 = a2 then exp_state atoms env xs e1
      else exp_state atoms env xs e2
  | (Swap((EmptySlot, _), (e1, p1), e2), p2)::xs ->
      exp_state atoms env ((Swap(ast, (EmptySlot, p1), e2), p2)::xs) (e1, p1)
  | (Swap(a, (EmptySlot, _), (e, p1)), p2)::xs ->
      exp_state atoms env ((Swap(a, ast, (EmptySlot, p1)), p2)::xs) (e, p1)
  | (Swap(a1, a2, (EmptySlot, _)), p)::xs ->
      let (NameLiteral(n1), _) = a1 in
      let (NameLiteral(n2), _) = a2 in
      val_state atoms env xs (swap n1 n2 ast)
  | (NameAb((EmptySlot, _), (e, p1)), p2)::xs ->
      exp_state atoms env ((NameAb(ast, (EmptySlot, p1)), p2)::xs) (e, p1)
  | (NameAb(a, (EmptySlot, _)), p)::xs ->
      val_state atoms env xs (NameAb(a, ast), p);;

