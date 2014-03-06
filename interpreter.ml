open AbSyn;;

exception Run_time_error of string;;

(* x : 'a
 * env : (('a, 'b) list) list
 * Return true iff x is in the head of the env list
 * TODO look into standard library assoc list functions
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

(* Print stats for debugging *)
let env_stats env fs =
	let fs_size = List.length fs in
	let stack_size = List.length env in
	let avg_env_len = (List.fold_left (fun y xs -> (List.fold_left (fun x _ -> x+.1.) y xs)) 0. env) /. (float_of_int stack_size) in
	Printf.printf "stack size = %d\tavg. env length = %f\tframe stack size = %d\n" stack_size avg_env_len fs_size;;

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
		(*Printf.printf "Generating new %s atom: %d\n" s (n+1);*)
    NameLiteral(s, n)
  with Not_found -> raise (Run_time_error ("Invalid name type: "^s));;

(*
 * Swap atoms a1 and a2 in expression v.
 * Invariant: is_val v = true
 *)
let rec swap a1 a2 v =
	(* Expect empty perm if doing eager swapping *)
	let (v', [], p) = v in
  match v' with
  | IntLiteral n -> (IntLiteral n, [], p)
  | RealLiteral r -> (RealLiteral r, [], p)
  | BoolLiteral b -> (BoolLiteral b, [], p)
  | StringLiteral s -> (StringLiteral s, [], p)
  | NameLiteral n -> 
      if n = a1 then (NameLiteral a2, [], p)
      else if n = a2 then (NameLiteral a1, [], p) else (NameLiteral n, [], p)
  | Ctor(s, e) -> (Ctor(s, (swap a1 a2 e)), [], p)
  | NameAb(e1, e2) -> (NameAb(swap a1 a2 e1, swap a1 a2 e2), [], p)
  | Unit -> (Unit, [], p)
  | Pair(e1, e2) -> (Pair(swap a1 a2 e1, swap a1 a2 e2), [], p)
  | Lambda(s, t, e, env) -> (Lambda(s, t, e, swap_env a1 a2 env), [], p)
  | RecFunc(s1, s2, t1, t2, e, env) ->
      (RecFunc(s1, s2, t1, t2, e, swap_env a1 a2 env), [], p)
  | _ -> raise (Run_time_error "Swap called on non-value expression")

(* Swap atoms a1 and a2 in the environment list env
 * Only does swaps in the head of the list as per the rules for ((a a') * E)
 *)
and swap_env a1 a2 env = List.map (fun (x, v) -> (x, swap a1 a2 v)) env;;

(* Add the permutation pi to the value e *)
let push pi e =
	let (e', pi', ps) = e in
	(e', pi' @ pi, ps);;

(* Apply permutation pi to name a *)
let permute pi a =
	List.fold_left (fun a (a1, a2) -> if a = a1 then a2 else if a = a2 then a1 else a) a pi;;

(*
 * Presented as cf(-) in the semantics.
 * Pushes the permutation attached to the given expression through the first
 * level of its structure, making the outermost constructor manifest.
 *)
let push_perm v =
	let permute_env pi env = List.map (fun (x, v) -> (x, push pi v)) env in
	let (e, pi, ps) = v in
	match e with
	| IntLiteral n -> (e, [], ps)
	| RealLiteral n -> (e, [], ps)
	| BoolLiteral n -> (e, [], ps)
	| StringLiteral n -> (e, [], ps)
	| NameLiteral a -> (NameLiteral(permute pi a), [], ps)
	| Unit -> (Unit, [], ps)
	| Lambda(s, t, e, env) -> (Lambda(s, t, e, permute_env pi env), [], ps)
	| RecFunc(s1, s2, t1, t2, e, env) ->
			(RecFunc(s1, s2, t1, t2, e, permute_env pi env), [], ps)
	| Ctor(s, v) -> (Ctor(s, push pi v), [], ps)
	| NameAb((NameLiteral(a), [], p), v) ->
			(NameAb((NameLiteral(permute pi a), [], p), push pi v), [], ps)
	| Pair(e1, e2) -> (Pair(push pi e1, push pi e2), [], ps)
	| _ -> raise (Run_time_error "Got expression but expected value for permutation application");;

let rec calc_ineq delay_perms atoms v1 op v2 =
	match op with
	(* Type checking ensures that for <, <=, > and >=, v1 and v2 are int, real or string literals *)
	| Gt -> BoolLiteral(v1 > v2)
	| Gteq -> BoolLiteral(v1 >= v2)
	| Lt -> BoolLiteral(v1 < v2)
	| Lteq -> BoolLiteral(v1 <= v2)
	| Eq ->
			(match v1 with
			| NameAb((NameLiteral(s1, n1), [], _), e2) ->
					let NameAb((NameLiteral(s2, n2), [], _), d2) = v2 in
					let NameLiteral(a) = gen_atom atoms s1 in
					if delay_perms then
						let pi, pi' = [(s1, n1), a], [(s2, n2), a] in
						let (x, _, _), (y, _, _) = (push_perm (push pi e2)), (push_perm (push pi' d2)) in
						calc_ineq delay_perms atoms x Eq y
					else
						let (x, _, _), (y, _, _) = (swap (s1, n1) a e2), (swap (s2, n2) a d2) in
						calc_ineq delay_perms atoms x Eq y
			| Ctor(s1, e) ->
					let Ctor(s2, e') = v2 in 
					if s1 = s2 then
						if delay_perms then
							let (e1, _, _) = push_perm e in
							let (e2, _, _) = push_perm e' in
							calc_ineq delay_perms atoms e1 Eq e2
						else
							let (e1, _, _) = e in
							let (e2, _, _) = e' in
							calc_ineq delay_perms atoms e1 Eq e2
					else BoolLiteral(false)
			| Pair(e, e') ->
					let Pair(d, d') = v2 in
					if delay_perms then
						let (e1, _, _), (e2, _, _) = push_perm e, push_perm e' in
						let (d1, _, _), (d2, _, _) = push_perm d, push_perm d' in
						let BoolLiteral(b) = calc_ineq delay_perms atoms e1 Eq d1 in
						if b then (calc_ineq delay_perms atoms e2 Eq d2) else BoolLiteral(b)
					else
						let (e1, _, _), (e2, _, _) = e, e' in
						let (d1, _, _), (d2, _, _) = d, d' in
						let BoolLiteral(b) = calc_ineq delay_perms atoms e1 Eq d1 in
						if b then (calc_ineq delay_perms atoms e2 Eq d2) else BoolLiteral(b)
			| Lambda _ -> raise (Run_time_error "Cannot compare function values")
			| RecFunc _ -> raise (Run_time_error "Cannot compare function values")
			(*| NameLiteral(s1, n1) ->
					let NameLiteral(s2, n2) = v2 in
					Printf.printf "name eq: (%s, %d) = (%s, %d)\n" s1 n1 s2 n2;
					BoolLiteral(n1 = n2)*)
			| _ -> BoolLiteral(v1 = v2));;

(* Perform a binary operation on two values
 * 	- Applies any permutations to those values
 *	- Returns a single exp with an empty permutation
 *)
(* TODO update semantics to apply cf(-) here *)
(* TODO handle precedance correctly *)
let bin_operate delay_perms atoms v1 op v2 =
  let (v, _, _) = if delay_perms then push_perm v1 else v1 in
  let (v', _, p) = if delay_perms then push_perm v2 else v2 in
	match (v, v') with
	| IntLiteral(n1), IntLiteral(n2) ->
			(match op with
			| Div -> (IntLiteral(n1/n2), [], p)
			| Mult -> (IntLiteral(n1*n2), [], p)
			| Add -> (IntLiteral(n1+n2), [], p)
			| Sub -> (IntLiteral(n1-n2), [], p)
			| _ -> (calc_ineq delay_perms atoms (IntLiteral n1) op (IntLiteral n2), [], p))
	| RealLiteral(n1), RealLiteral(n2) ->
			(match op with
			| Div -> (RealLiteral(n1 /. n2), [], p)
			| Mult -> (RealLiteral(n1 *. n2), [], p)
			| Add -> (RealLiteral(n1 +. n2), [], p)
			| Sub -> (RealLiteral(n1 -. n2), [], p)
			| _ -> (calc_ineq delay_perms atoms (RealLiteral n1) op (RealLiteral n2), [], p))
	| StringLiteral(s1), StringLiteral(s2) ->
			(match op with
			| Concat -> (StringLiteral(s1 ^ s2), [], p)
			| _ -> (calc_ineq delay_perms atoms (StringLiteral s1) op (StringLiteral s2), [], p))
	| _ -> (calc_ineq delay_perms atoms v op v', [], p);;

(* Perform a unary operation on a numeric value *)
(* TODO update semantics to call cf(-) here *)
let un_operate op v =
  let (v', _, p) = v in		(* Don't call push_perm - it will have no effect on numeric literals *)
  match v' with
  | IntLiteral(n) ->
      (match op with
      | Neg -> (IntLiteral(-n), [], p))
  | RealLiteral(n) ->
      (match op with
      | Neg -> (RealLiteral(-.n), [], p))
  | _ ->
      raise (Run_time_error ("Trying to perform unary operation on"^
        " non-numeric type"));;

(*let no = ref 0;; (* for debugging *)*)

(*********************************************************************************
 * We assumme that the typechecker has been run on the expressions passed to the
 * state functions. This means we don't have to check for certain errors (e.g.
 * that the values being compared in an if expression are of the same name type).
 ********************************************************************************)

(*
 * Replace the expr in an exp with an empty slot.
 * Returns the new exp with an empty permutation.
 * empty : exp -> exp
 *)
let empty e = let (e', pi, ps) = e in (EmptySlot, [], ps);;

(*
 * atoms - Hashtbl (string, int)
 * env - ((string, val) list) list
 * fs - expr list
 * ast - exp
 *
 * Returns a 2-tuple of (new env, value)
 * No need to return new atoms - assume user still has a reference to the Hashtbl.
 *)
(* TODO add interface file to hide all but exp_state function *)
let rec exp_state delay_perms atoms env fs ast =
  if is_val ast then val_state delay_perms atoms env fs ast
  else
		(* Expressions (as opposed to values) have empty permutations, so ignore the them *)
		let (e, [], ps) = ast in
		match e with
		| Id(s) ->
				(try
					(*(let (v, pi, p) = lookup s env in
					if (List.length pi) > 100000 then
						(print_string ("Looking up (" ^ s ^ ", " ^ (string_of_exp (v, pi, p)) ^ ") in env ==> ");
						print_string ((string_of_exp (push_perm (v, pi, p))) ^ "\n"))
					else ());*)
					if delay_perms then
						val_state delay_perms atoms env fs (push_perm (lookup s env))
					else
						val_state delay_perms atoms env fs (lookup s env)
				with
				Not_found -> raise (Run_time_error ("Id "^s^" not found in environment")))
		| Ctor(s, e') ->
				exp_state delay_perms atoms env ((Ctor(s, empty e'), [], ps)::fs) e'
		| Fresh(s) -> let a = gen_atom atoms s in val_state delay_perms atoms env fs (a, [], ps)
		| If(e1, e2, e3) ->
				exp_state delay_perms atoms env ((If(empty e1, e2, e3), [], ps)::fs) e1
		| Swap(e1, e2, e3) ->
				exp_state delay_perms atoms env ((Swap(empty e1, e2, e3), [], ps)::fs) e1
		| NameAb(e1, e2) ->
				exp_state delay_perms atoms env ((NameAb(empty e1, e2), [], ps)::fs) e1
		| Lambda(s, t, e, _) ->
				val_state delay_perms atoms env fs (Lambda(s, t, e, List.hd env), [], ps)
		| Pair(e1, e2) ->
				exp_state delay_perms atoms env ((Pair(empty e1, e2), [], ps)::fs) e1
		| BinaryOp(e1, b, e2) ->
				exp_state delay_perms atoms env ((BinaryOp(empty e1, b, e2), [], ps)::fs) e1
		| UnaryOp(u, e) ->
				exp_state delay_perms atoms env ((UnaryOp(u, empty e), [], ps)::fs) e
		| App(e1, e2) ->
				exp_state delay_perms atoms env ((App(empty e1, e2), [], ps)::fs) e1
		| Match(e1, br) ->
				exp_state delay_perms atoms env ((Match(empty e1, br), [], ps)::fs) e1
		| Let(ValBind(pat, e1), e2) ->
				exp_state delay_perms atoms env ((Let(ValBind(pat, empty e1), e2), [], ps)::fs) e1
		| Let(RecF(RecFunc(s1, s2, t1, t2, e1, _)), e2) ->
				exp_state delay_perms atoms (cons (s1, (RecFunc(s1, s2, t1, t2, e1, List.hd env), [], ps)) env) fs e2
		| TopLet(ValBind(pat, e1), p) ->
				exp_state delay_perms atoms env ((TopLet(ValBind(pat, empty e1), p), [], ps)::fs) e1
		| TopLet(RecF(RecFunc(s1, s2, t1, t2, e, _)), p) ->
				let f = (RecFunc(s1, s2, t1, t2, e, List.hd env), [], p) in
				val_state delay_perms atoms (cons (s1, f) env) fs f

(* Invariant: is_val ast = true *)
and val_state delay_perms atoms env fs ast =
	if fs = [] then (env, ast)
	else
		(* Permutations will be empty for elements of FS, so ignore them *)
		let (e, [], ps)::xs = fs in
		match e with
		| EofFunc -> val_state delay_perms atoms (List.tl env) xs ast
		| Ctor(s, (EmptySlot, [], _)) ->
				val_state delay_perms atoms env xs (Ctor(s, ast), [], ps)
		| If((EmptySlot, [], _), e1, e2) ->
				let BoolLiteral(b), _, _ = ast in
				exp_state delay_perms atoms env xs (if b then e1 else e2)
		| Swap((EmptySlot, [], _), e1, e2) ->
				exp_state delay_perms atoms env ((Swap(ast, empty e1, e2), [], ps)::xs) e1
		| Swap(a, (EmptySlot, [], _), e) ->
				exp_state delay_perms atoms env ((Swap(a, ast, empty e), [], ps)::xs) e
		| Swap(x, y, (EmptySlot, [], _)) ->
				if delay_perms then
					let NameLiteral(a1), _, _ = push_perm x in
					let NameLiteral(a2), _, _ = push_perm y in
					val_state delay_perms atoms env xs (push_perm (push [(a1, a2)] ast))
				else
					let (NameLiteral(a1), _, _), (NameLiteral(a2), _, _) = x, y in
					val_state delay_perms atoms env xs (swap a1 a2 ast)
		| NameAb((EmptySlot, [], _), e1) ->
				exp_state delay_perms atoms env ((NameAb(ast, empty e1), [], ps)::xs) e1
		| NameAb(a, (EmptySlot, [], _)) ->
				val_state delay_perms atoms env xs (NameAb(a, ast), [], ps)
		| Pair((EmptySlot, [], _), e1) ->
				exp_state delay_perms atoms env ((Pair(ast, empty e1), [], ps)::xs) e1
		| Pair(v, (EmptySlot, [], _)) -> val_state delay_perms atoms env xs (Pair(v, ast), [], ps)
		| BinaryOp((EmptySlot, [], _), b, e1) ->
				exp_state delay_perms atoms env ((BinaryOp(ast, b, empty e1), [], ps)::xs) e1
		| BinaryOp(v, b, (EmptySlot, [], _)) ->
				val_state delay_perms atoms env xs (bin_operate delay_perms atoms v b ast)
		| UnaryOp(u, (EmptySlot, [], _)) ->
				val_state delay_perms atoms env xs (un_operate u ast)
		| App((EmptySlot, [], _), e1) ->
				exp_state delay_perms atoms env ((App(ast, empty e1), [], ps)::xs) e1
		| App((Lambda(s, _, e, en), _, _), (EmptySlot, [], _)) ->
				exp_state delay_perms atoms (((s, ast)::en)::env) ((EofFunc, [], ps)::xs) e
		| App((RecFunc(s1, s2, t1, t2, e, en), pi, p), (EmptySlot, [], _)) ->
				exp_state delay_perms atoms
					(((s1, (RecFunc(s1, s2, t1, t2, e, en), pi, p))::(s2, ast)::en)::env)
					((EofFunc, [], ps)::xs) e
		| Match((EmptySlot, [], p), (pat, e)::[]) ->
				match_init delay_perms atoms env []
					((Let(ValBind(pat, (EmptySlot, [], p)), e), [], ps)::xs) false ast
		| Match((EmptySlot, [], p), (pat, e)::br) ->
				match_init delay_perms atoms env [(br, ast)]
					((Let(ValBind(pat, (EmptySlot, [], p)), e), [], ps)::xs) false ast
		| Let(ValBind(pat, (EmptySlot, [], p)), e) ->
				match_state delay_perms atoms env []
					((Let(ValBind(pat, (EmptySlot, [], p)), e), [], ps)::xs) false ast
		| TopLet(ValBind(pat, (EmptySlot, [], p)), _) ->
				match_state delay_perms atoms env []
					((Let(ValBind(pat, (EmptySlot, [], p)), ast), [], ps)::xs) true ast
		| _ -> raise (Run_time_error "Head of frame stack has no empty slot")

(* Duplicate (hd env) and push EofFunc onto F to create a new scope for Match exprs *)
and match_init delay_perms atoms env ms fs is_top ast =
	let x::xs = fs in
	let e::es = env in
	match_state delay_perms atoms (e::e::es) ms (x::(EofFunc, [], (0, 0))::xs) is_top ast

(* Invariant: is_val v = true *)
and match_state delay_perms atoms env ms fs is_top ast =
  (* Permutations will be empty for elements of FS, so ignore them *)
  let (e, [], ps)::xs = fs in
  (* Match against a literal pattern *)
  let handle_literal x y p e =
    if x = y then exp_state delay_perms atoms env xs e
    else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1);    (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
        (* Need to discard env and EofFunc which we added in match_init.
		   		 match_init must have been called since ms not empty and therefore we must
		   		 be pattern-matching within a Match expression.
				*)
        val_state delay_perms atoms (List.tl env)
					((Match((EmptySlot, [], p), br), [], ps)::(List.tl xs)) v)
    else raise (Run_time_error "Match failed: could not match literal")
  in
  match e with
  | Let(ValBind(DontCareP, _), e) -> exp_state delay_perms atoms env xs e
  | Let(ValBind(IdP(s), (EmptySlot, [], _)), e) ->
			(*(let (_, pi, _) = ast in
			if (List.length pi) > 100000 then
				print_string ("Adding: (" ^ s ^ ", " ^ (string_of_exp ast) ^ ") to env\n")
			else ());*)
      exp_state delay_perms atoms (cons (s, ast) env) xs e
	| Let(ValBind(IntP(n1), (EmptySlot, [], p)), e) ->
			let IntLiteral(n2), _, _ = ast in handle_literal n1 n2 p e
	| Let(ValBind(RealP(n1), (EmptySlot, [], p)), e) ->
			let RealLiteral(n2), _, _ = ast in handle_literal n1 n2 p e
	| Let(ValBind(BoolP(b1), (EmptySlot, [], p)), e) ->
			let BoolLiteral(b2), _, _ = ast in handle_literal b1 b2 p e
	| Let(ValBind(StringP(s1), (EmptySlot, [], p)), e) ->
			let StringLiteral(s2), _, _ = ast in handle_literal s1 s2 p e
  | Let(ValBind(CtorP(s1, pat), (EmptySlot, [], p)), e) ->
      let Ctor(s2, e'), [], _ = if delay_perms then push_perm ast else ast in
      if s1 = s2 then
        match_state delay_perms atoms env ms
					((Let(ValBind(pat, (EmptySlot, [], p)), e), [], ps)::xs) is_top e'
      else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1); (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
        val_state delay_perms atoms (List.tl env)
					((Match((EmptySlot, [], p), br), [], ps)::(List.tl xs)) v)
      else
        raise (Run_time_error ("Match failed: could not match constructor "^s2))
	| Let(ValBind(NameAbsP(DontCareP, pat), (EmptySlot, [], p1)), e) ->
			let NameAb((NameLiteral(s, n), [], p2), v), pi, p3 = ast in
			let NameLiteral(a') = gen_atom atoms s in
			let v' = if delay_perms then push pi (push [a', (s, n)] v) else swap a' (s, n) v in
			let e' = e in
			match_state delay_perms atoms env ms
				((Let(ValBind(pat, (EmptySlot, [], p1)), e'), [], ps)::xs) is_top v'
	| Let(ValBind(NameAbsP(IdP(x), pat), (EmptySlot, [], p1)), e) ->
			let NameAb((NameLiteral(s, n), [], p2), v), pi, p3 = ast in
			let NameLiteral(a') = gen_atom atoms s in
			(* Add a perm to freshen all bound names BEFORE pushing the existing perm into
			   the abstraction body. *)
			let v' = if delay_perms then push pi (push [a', (s, n)] v) else swap a' (s, n) v in
			(* XXX But this name abs might be nested somewhere inside e - don't want to replace
						 all of e if is_top, only the name abs part.

				 Solution: return stale value and alter string_of_expr code to normalise
				 					 all name values - e.g. increment counter at each bind, leave
									 free names as-is (will be correct since not bound and therefore
									 will not have been freshened).

				 OR: since user doesn't care about actual values, just report stale values.
				 		 Not very nice when evaluate ids bound in the pattern and get different
						 values, bu it does save a lot of work and doesn't alter functionality.
						 YES, GO WITH THIS SECOND OPTION.
			*)
			let e' = e in (*if is_top then (NameAb((NameLiteral(a'), [], p2), v'), [], p3) else e in*)
			match_state delay_perms atoms (cons (x, (NameLiteral(a'), [], p2)) env) ms
				((Let(ValBind(pat, (EmptySlot, [], p1)), e'), [], ps)::xs) is_top v'
  | Let(ValBind(UnitP, _), e) -> exp_state delay_perms atoms env xs e
  | Let(ValBind(ProdP(pat1, pat2), (EmptySlot, [], p1)), e) ->
      let Pair(v1, v2), [], _ = if delay_perms then push_perm ast else ast in
      match_state delay_perms atoms env ms
        ((Let(ValBind(pat1, (EmptySlot, [], p1)),
          (Let(ValBind(pat2, v2), e), [], ps)), [], ps)::xs) is_top v1
	| _ -> raise (Run_time_error "Unexpected expression in MATCH state");;

