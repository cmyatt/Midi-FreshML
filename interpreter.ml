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

let print_env env =
	List.iter
		(fun xs ->
			print_string "--------------------------------------------------------------\n";
			List.iter (fun (x, (e, _)) -> Printf.printf "%s -> %s\n" x (string_of_expr e)) xs;
			print_string "--------------------------------------------------------------\n")
		env;;

(* Cons x onto the list of lists xss. *)
let cons x xss =
	match xss with
	| [] -> [[x]]
  | ys::yss -> ((x :: ys) :: yss);;

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
  | IntLiteral(n), p -> (IntLiteral(n), p)
  | RealLiteral(r), p -> (RealLiteral(r), p)
  | BoolLiteral(b), p -> (BoolLiteral(b), p)
  | StringLiteral(s), p -> (StringLiteral(s), p)
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

(* TODO handle precedance correctly *)
(* Perform a binary operation on two numeric values *)
let bin_operate v1 op v2 =
  let (v, _) = v1 in
  let (v', p) = v2 in
  match (v, v') with
  | IntLiteral(n1), IntLiteral(n2) ->
      (match op with
      | Div -> (IntLiteral(n1/n2), p)
      | Mult -> (IntLiteral(n1*n2), p)
      | Add -> (IntLiteral(n1+n2), p)
      | Sub -> (IntLiteral(n1-n2), p))
  | RealLiteral(n1), RealLiteral(n2) ->
      (match op with
      | Div -> (RealLiteral(n1 /. n2), p)
      | Mult -> (RealLiteral(n1 *. n2), p)
      | Add -> (RealLiteral(n1 +. n2), p)
      | Sub -> (RealLiteral(n1 -. n2), p))
  | _ ->
      raise (Run_time_error ("Trying to perform arithmetic operation on"^
        " non-numeric types"));;

(* Perform a unary operation on a numeric value *)
let un_operate u v =
  let (v', p) = v in
  match v' with
  | IntLiteral(n) ->
      (match u with
      | Neg -> (IntLiteral(-n), p))
  | RealLiteral(n) ->
      (match u with
      | Neg -> (RealLiteral(-.n), p))
  | _ ->
      raise (Run_time_error ("Trying to perform unary operation on"^
        " non-numeric type"));;

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
 * Returns a 2-tuple of (new env, value)
 * No need to return new atoms - assume user still has a reference to the Hashtbl.
 *)
let rec exp_state atoms env fs ast =
  if is_val ast then val_state atoms env fs ast
  else
    match ast with
    | Id(s), _ ->
				(try val_state atoms env fs (lookup s env) with
				Not_found -> (print_env env; raise (Run_time_error ("Id "^s^" not found in environment"))))
    | Ctor(s, (e, p1)), p2 ->
        exp_state atoms env ((Ctor(s, (EmptySlot, p1)), p2)::fs) (e, p1)
    | Fresh(s), p -> let a = gen_atom atoms s in val_state atoms env fs (a, p)
		| EqTest((e1, p1), e2), p2 ->
				exp_state atoms env ((EqTest((EmptySlot, p1), e2), p2)::fs) (e1, p1)
    | If((e1, p1), e2, e3), p2 ->
        exp_state atoms env ((If((EmptySlot, p1), e2, e3), p2)::fs) (e1, p1)
    | Swap((e1, p1), e2, e3), p2 ->
        exp_state atoms env ((Swap((EmptySlot, p1), e2, e3), p2)::fs) (e1, p1)
    | NameAb((e1, p1), e2), p2 ->
        exp_state atoms env ((NameAb((EmptySlot, p1), e2), p2)::fs) (e1, p1)
    | Lambda(s, t, e, _), p ->
        val_state atoms env fs (Lambda(s, t, e, (List.hd env)), p)
		| Pair((e1, p1), e2), p2 ->
				exp_state atoms env ((Pair((EmptySlot, p1), e2), p2)::fs) (e1, p1)
    | BinaryOp((e1, p1), b, e2), p2 ->
        exp_state atoms env ((BinaryOp((EmptySlot, p1), b, e2), p2)::fs) (e1, p1)
    | UnaryOp(u, (e, p1)), p2 ->
        exp_state atoms env ((UnaryOp(u, (EmptySlot, p1)), p2)::fs) (e, p1)
    | App((e1, p1), e2), p2 ->
        exp_state atoms env ((App((EmptySlot, p1), e2), p2)::fs) (e1, p1)
    | Match((e1, p1), br), p2 ->
        exp_state atoms env ((Match((EmptySlot, p1), br), p2)::fs) (e1, p1)
    | Let(ValBind(pat, (e1, p1)), e2), p2 ->
        exp_state atoms env ((Let(ValBind(pat, (EmptySlot, p1)), e2), p2)::fs) (e1, p1)
    | Let(RecF(RecFunc(s1, s2, t1, t2, e, _)), e'), p ->
        exp_state atoms (cons (s1, (RecFunc(s1, s2, t1, t2, e, (List.hd env)), p)) env) fs e'
		| TopLet(ValBind(pat, (e1, p1)), p2), p3 ->
				exp_state atoms env ((TopLet(ValBind(pat, (EmptySlot, p1)), p2), p3)::fs) (e1, p1)
    | TopLet(RecF(RecFunc(s1, s2, t1, t2, e, _)), p1), p2 ->
				let f = (RecFunc(s1, s2, t1, t2, e, List.hd env), p1) in
        val_state atoms (cons (s1, f) env) fs f

(* TODO Catch match failures for Exp individually (e.g. if NameAb
 * doesn't have EmptySlot *)
(* Invariant: is_val ast = true *)
and val_state atoms env fs ast =
  match fs with
  | [] -> (env, ast)
  | (EofFunc, _)::xs -> val_state atoms (List.tl env) xs ast
  | (Ctor(s, (EmptySlot, _)), p)::xs -> val_state atoms env xs (Ctor(s, ast), p)
	| (EqTest((EmptySlot, _), (e, p1)), p2)::xs ->
			exp_state atoms env ((EqTest(ast, (EmptySlot, p1)), p2)::xs) (e, p1)
	| (EqTest((v1, _), (EmptySlot, _)), p)::xs ->
			let v2, _ = ast in exp_state atoms env xs (BoolLiteral(v1 = v2), p)
  | (If((EmptySlot, _), (e1, p1), e2), p2)::xs ->
			let BoolLiteral(b), _ = ast in
      exp_state atoms env xs (if b then (e1, p1) else e2)
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
      val_state atoms env xs (NameAb(a, ast), p)
	| (Pair((EmptySlot, _), (e, p1)), p2)::xs ->
			exp_state atoms env ((Pair(ast, (EmptySlot, p1)), p2)::xs) (e, p1)
	| (Pair(v, (EmptySlot, _)), p)::xs -> val_state atoms env xs (Pair(v, ast), p)
  | (BinaryOp((EmptySlot, _), b, (e, p1)), p2)::xs ->
      exp_state atoms env ((BinaryOp(ast, b, (EmptySlot, p1)), p2)::xs) (e, p1)
  | (BinaryOp(v, b, (EmptySlot, _)), _)::xs ->
      val_state atoms env xs (bin_operate v b ast)
  | (UnaryOp(u, (EmptySlot, _)), _)::xs ->
      val_state atoms env xs (un_operate u ast)
  | (App((EmptySlot, _), (e, p1)), p2)::xs ->
      exp_state atoms env ((App(ast, (EmptySlot, p1)), p2)::xs) (e, p1)
  | (App((Lambda(s, t, e, en), _), (EmptySlot, _)), p)::xs ->
      exp_state atoms (((s, ast)::en)::env) ((EofFunc, p)::xs) e
  | (App((RecFunc(s1, s2, t1, t2, e, en), p1), (EmptySlot, _)), p2)::xs ->
      exp_state atoms
        (((s1, (RecFunc(s1, s2, t1, t2, e, en), p1))::(s2, ast)::en)::env)
        ((EofFunc, p2)::xs) e
  | (Match((EmptySlot, p1), (pat, e)::[]), p2)::xs ->
      match_init atoms env [] ((Let(ValBind(pat, (EmptySlot, p1)), e), p2)::xs) false ast
  | (Match((EmptySlot, p1), (pat, e)::br), p2)::xs ->
      match_init atoms env [(br, ast)] ((Let(ValBind(pat, (EmptySlot, p1)), e), p2)::xs) false ast
  | (Let(ValBind(pat, (EmptySlot, p1)), e), p2)::xs ->
      match_state atoms env [] ((Let(ValBind(pat, (EmptySlot, p1)), e), p2)::xs) false ast
  | (TopLet(ValBind(pat, (EmptySlot, p1)), p2), p3)::xs ->
      match_state atoms env [] ((Let(ValBind(pat, (EmptySlot, p1)), ast), p3)::xs) true ast

(* Duplicate (hd env) and push EofFunc onto F to create a new scope for Match exprs *)
and match_init atoms env ms fs is_top ast =
	let x::xs = fs in
	let e::es = env in
	match_state atoms (e::e::es) ms (x::(EofFunc, (0, 0))::xs) is_top ast

(* Invariant: is_val v = true *)
and match_state atoms env ms fs is_top ast =
  match fs with
  | (Let(ValBind(DontCareP, _), e), _)::xs -> exp_state atoms env xs e
  | (Let(ValBind(IdP(s), (EmptySlot, _)), e), _)::xs ->
      exp_state atoms (cons (s, ast) env) xs e
  | (Let(ValBind(CtorP(s1, pat), (EmptySlot, p1)), e), p2)::xs ->
      let Ctor(s2, e'), _ = ast in
      if s1 = s2 then
        match_state atoms env ms ((Let(ValBind(pat, (EmptySlot, p1)), e), p2)::xs) is_top e'
      else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1); (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
				(* Need to discard env and EofFunc which we added in match_init *)
        val_state atoms (List.tl env) ((Match((EmptySlot, p1), br), p2)::(List.tl xs)) v)
      else
        raise (Run_time_error ("Match failed: could not match constructor "^s2))
  | (Let(ValBind(NameAbsP(IdP(x), pat), (EmptySlot, p1)), e), p2)::xs ->
      let NameAb((NameLiteral(Name(s, n)), p3), v), p' = ast in
      let NameLiteral(a') = gen_atom atoms s in
			let v' = swap (Name(s, n)) a' v in
			let e' = if is_top then NameAb((NameLiteral(a'), p3), v'), p' else e in
      match_state atoms (cons (x, (NameLiteral(a'), p3)) env) ms
        ((Let(ValBind(pat, (EmptySlot, p1)), e'), p2)::xs) is_top v'
  | (Let(ValBind(UnitP, _), e), _)::xs -> exp_state atoms env xs e
  | (Let(ValBind(ProdP(pat1, pat2), (EmptySlot, p1)), e), p2)::xs ->
      let Pair(v1, v2), _ = ast in
      match_state atoms env ms
        ((Let(ValBind(pat1, (EmptySlot, p1)),
          (Let(ValBind(pat2, v2), e), p2)), p2)::xs) is_top v1;;

