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
    NameLiteral(Name(s, n))
  with Not_found -> raise (Run_time_error ("Invalid name type: "^s));;

(* Swap atoms a1 and a2 in expression v.
 * Invariant: is_val v = true
 *)
(*
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
and swap_env a1 a2 env = List.map (fun (x, v) -> (x, swap a1 a2 v)) xs;;
*)

(* Add the permutation pi to the value e *)
let push pi e = let (e', pi', ps) = e in (e', pi' @ pi, ps);;

(*
 * Presented as cf(-) in the semantics.
 * Pushes the permutation attached to the given expression through the first
 * level of its structure, making the outermost constructor manifest.
 *)
let push_perm v =
	let permute pi a =
		List.fold_left (fun a (a1, a2) -> if a = a1 then a2 else if a = a2 then a1 else a) a pi
	in
	let permute_env pi env = List.map (fun (x, v) -> (x, push pi v)) env in
	let (e, pi, ps) = v in
	match e with
	| IntLiteral(n) -> (e, [], ps)
	| RealLiteral(n) -> (e, [], ps)
	| BoolLiteral(n) -> (e, [], ps)
	| StringLiteral(n) -> (e, [], ps)
	| NameLiteral(a) -> (NameLiteral(permute pi a), [], ps)
	| Unit -> (Unit, [], ps)
	| Lambda(s, t, e, env) -> (Lambda(s, t, e, permute_env pi env), [], ps)
	| RecFunc(s1, s2, t1, t2, e, env) ->
			(RecFunc(s1, s2, t1, t2, e, permute_env pi env), [], ps)
	| Ctor(s, e) -> (Ctor(s, push pi e), [], ps)
	| NameAb(e1, e2) ->
			let (NameLiteral(a), pi', ps') = push pi e1 in
			(NameAb((NameLiteral(permute pi' a), [], ps'), push pi e2), [], ps)
	| Pair(e1, e2) -> (Pair(push pi e1, push pi e2), [], ps)
	| _ -> raise (Run_time_error "Got expression but expected value for permutation application");;

let rec calc_ineq atoms v1 op v2 =
	match op with
	(* Type checking ensures that for <, <=, > and >=, v1 and v2 are int, real or string literals *)
	| Gt -> BoolLiteral(v1 > v2)
	| Gteq -> BoolLiteral(v1 >= v2)
	| Lt -> BoolLiteral(v1 < v2)
	| Lteq -> BoolLiteral(v1 <= v2)
	| Eq ->
			(match v1 with
			| NameAb(e1, e2) ->
					let NameAb(d1, d2) = v2 in
					let (NameLiteral(Name(s1, n1)), _, _) = push_perm e1 in
					let (NameLiteral(Name(s2, n2)), _, _) = push_perm d1 in
					let NameLiteral(a) = gen_atom atoms s1 in
					let pi, pi' = [(Name(s1, n1), a)], [(Name(s2, n2), a)] in
					let (x, _, _), (y, _, _) = (push_perm (push pi e2)), (push_perm (push pi' d2)) in
					calc_ineq atoms x Eq y
			| Ctor(_, e) ->
					let Ctor(_, e') = v2 in 
					let (e1, _, _) = push_perm e in
					let (e2, _, _) = push_perm e' in
					calc_ineq atoms e1 Eq e2
			| Pair(e, e') ->
					let Pair(d, d') = v2 in
					let (e1, _, _) = push_perm e in
					let (e2, _, _) = push_perm e' in
					let (d1, _, _) = push_perm d in
					let (d2, _, _) = push_perm d' in
					(* Pairwise comparison *)
					let BoolLiteral(b) = calc_ineq atoms e1 Eq d1 in
					if b then (calc_ineq atoms e2 Eq d2) else BoolLiteral(b)
			| Lambda _ -> raise (Run_time_error "Cannot compare function values")
			| RecFunc _ -> raise (Run_time_error "Cannot compare function values")
			| NameLiteral(Name(s1, n1)) ->
					(try
						let NameLiteral(Name(s2, n2)) = v2 in
						Printf.printf "(%s, %d) = (%s, %d) = %b\n" s1 n1 s2 n2 (n1 = n2);
						BoolLiteral(n1 = n2)
					with Match_failure _ ->
						raise (Run_time_error ("Type mismatch: got "^(string_of_expr v1)^" = "^(string_of_expr v2))))
			| _ -> BoolLiteral(v1 = v2));;

(* Perform a binary operation on two values
 * 	- Applies any permutations to those values
 *	- Returns a single exp with an empty permutation
 *)
(* TODO update semantics to apply cf(-) here *)
(* TODO handle precedance correctly *)
let bin_operate atoms v1 op v2 =
  let (v, _, _) = push_perm v1 in
  let (v', _, p) = push_perm v2 in
	match (v, v') with
	| IntLiteral(n1), IntLiteral(n2) ->
			(match op with
			| Div -> (IntLiteral(n1/n2), [], p)
			| Mult -> (IntLiteral(n1*n2), [], p)
			| Add -> (IntLiteral(n1+n2), [], p)
			| Sub -> (IntLiteral(n1-n2), [], p)
			| _ -> (calc_ineq atoms (IntLiteral n1) op (IntLiteral n2), [], p))
	| RealLiteral(n1), RealLiteral(n2) ->
			(match op with
			| Div -> (RealLiteral(n1 /. n2), [], p)
			| Mult -> (RealLiteral(n1 *. n2), [], p)
			| Add -> (RealLiteral(n1 +. n2), [], p)
			| Sub -> (RealLiteral(n1 -. n2), [], p)
			| _ -> (calc_ineq atoms (RealLiteral n1) op (RealLiteral n2), [], p))
	| StringLiteral(s1), StringLiteral(s2) ->
			(match op with
			| Concat -> (StringLiteral(s1 ^ s2), [], p)
			| _ -> (calc_ineq atoms (StringLiteral s1) op (StringLiteral s2), [], p))
	| _ -> (calc_ineq atoms v op v', [], p);;

(* Perform a unary operation on a numeric value *)
(* TODO update semantics to call cf(-) here *)
let un_operate op v =
  let (v', _, p) = push_perm v in
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

(*let no = ref 0;;*)

(*********************************************************************************
 * We assumme that the typechecker has been run on the expressions passed to the
 * state functions. This means we don't have to check for certain errors (e.g.
 * that the values being compared in an if expression are of the same name type).
 ********************************************************************************)

(* Replace the expr in an exp with ann empty slot and return the new exp
 * empty : exp -> exp
 *)
let empty e = let (e', pi, ps) = e in (EmptySlot, pi, ps);;

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
		(* Expressions (as opposed to values) have empty permutations, so ignore the them *)
		let (e, [], ps) = ast in
		match e with
		| Id(s) ->
				(try val_state atoms env fs (push_perm (lookup s env)) with
				Not_found -> raise (Run_time_error ("Id "^s^" not found in environment")))
		| Ctor(s, e') ->
				exp_state atoms env ((Ctor(s, empty e'), [], ps)::fs) e'
		| Fresh(s) -> let a = gen_atom atoms s in val_state atoms env fs (a, [], ps)
		| If(e1, e2, e3) ->
				exp_state atoms env ((If(empty e1, e2, e3), [], ps)::fs) e1
		| Swap(e1, e2, e3) ->
				exp_state atoms env ((Swap(empty e1, e2, e3), [], ps)::fs) e1
		| NameAb(e1, e2) ->
				exp_state atoms env ((NameAb(empty e1, e2), [], ps)::fs) e1
		| Lambda(s, t, e, _) ->
				val_state atoms env fs (Lambda(s, t, e, List.hd env), [], ps)
		| Pair(e1, e2) ->
				exp_state atoms env ((Pair(empty e1, e2), [], ps)::fs) e1
		| BinaryOp(e1, b, e2) ->
				exp_state atoms env ((BinaryOp(empty e1, b, e2), [], ps)::fs) e1
		| UnaryOp(u, e) ->
				exp_state atoms env ((UnaryOp(u, empty e), [], ps)::fs) e
		| App(e1, e2) ->
				exp_state atoms env ((App(empty e1, e2), [], ps)::fs) e1
		| Match(e1, br) ->
				exp_state atoms env ((Match(empty e1, br), [], ps)::fs) e1
		| Let(ValBind(pat, e1), e2) ->
				exp_state atoms env ((Let(ValBind(pat, empty e1), e2), [], ps)::fs) e1
		| Let(RecF(RecFunc(s1, s2, t1, t2, e1, _)), e2) ->
				exp_state atoms (cons (s1, (RecFunc(s1, s2, t1, t2, e1, List.hd env), [], ps)) env) fs e2
		| TopLet(ValBind(pat, e1), p) ->
				exp_state atoms env ((TopLet(ValBind(pat, empty e1), p), [], ps)::fs) e1
		| TopLet(RecF(RecFunc(s1, s2, t1, t2, e, _)), p) ->
				let f = (RecFunc(s1, s2, t1, t2, e, List.hd env), [], p) in
				val_state atoms (cons (s1, f) env) fs f

(* TODO Catch match failures for Exp individually (e.g. if NameAb doesn't have EmptySlot *)
(* Invariant: is_val ast = true *)
and val_state atoms env fs ast =
	if fs = [] then (env, ast)
	else
		(* Permutations will be empty for elements of FS, so ignore them *)
		let (e, [], ps)::xs = fs in
		match e with
		| EofFunc -> val_state atoms (List.tl env) xs ast
		| Ctor(s, (EmptySlot, _, _)) ->
				val_state atoms env xs (Ctor(s, ast), [], ps)
		| If((EmptySlot, _, _), e1, e2) ->
				let BoolLiteral(b), _, _ = ast in
				exp_state atoms env xs (if b then e1 else e2)
		| Swap((EmptySlot, _, _), e1, e2) ->
				exp_state atoms env ((Swap(ast, empty e1, e2), [], ps)::xs) e1
		| Swap(a, (EmptySlot, _, _), e) ->
				exp_state atoms env ((Swap(a, ast, empty e), [], ps)::xs) e
		| Swap((NameLiteral(a1), pi1, _), (NameLiteral(a2), pi2, _), (EmptySlot, _, _)) ->
				val_state atoms env xs (push_perm (push [(a1, a2)] ast))
		| NameAb((EmptySlot, _, _), e1) ->
				exp_state atoms env ((NameAb(ast, empty e1), [], ps)::xs) e1
		| NameAb(a, (EmptySlot, _, _)) ->
				val_state atoms env xs (NameAb(a, ast), [], ps)
		| Pair((EmptySlot, _, _), e1) ->
				exp_state atoms env ((Pair(ast, empty e1), [], ps)::xs) e1
		| Pair(v, (EmptySlot, _, _)) -> val_state atoms env xs (Pair(v, ast), [], ps)
		| BinaryOp((EmptySlot, _, _), b, e1) ->
				exp_state atoms env ((BinaryOp(ast, b, empty e1), [], ps)::xs) e1
		| BinaryOp(v, b, (EmptySlot, _, _)) ->
				val_state atoms env xs (bin_operate atoms v b ast)
		| UnaryOp(u, (EmptySlot, _, _)) ->
				val_state atoms env xs (un_operate u ast)
		| App((EmptySlot, _, _), e1) ->
				exp_state atoms env ((App(ast, empty e1), [], ps)::xs) e1
		| App((Lambda(s, _, e, en), _, _), (EmptySlot, _, _)) ->
				exp_state atoms (((s, ast)::en)::env) ((EofFunc, [], ps)::xs) e
		| App((RecFunc(s1, s2, t1, t2, e, en), pi, p), (EmptySlot, _, _)) ->
				exp_state atoms
					(((s1, (RecFunc(s1, s2, t1, t2, e, en), pi, p))::(s2, ast)::en)::env)
					((EofFunc, [], ps)::xs) e
		| Match((EmptySlot, pi, p1), (pat, e)::[]) ->
				match_init atoms env [] ((Let(ValBind(pat, (EmptySlot, pi, p1)), e), [], ps)::xs) false ast
		| Match((EmptySlot, pi, p1), (pat, e)::br) ->
				match_init atoms env [(br, ast)]
					((Let(ValBind(pat, (EmptySlot, pi, p1)), e), [], ps)::xs) false ast
		| Let(ValBind(pat, (EmptySlot, pi, p1)), e) ->
				match_state atoms env [] ((Let(ValBind(pat, (EmptySlot, pi, p1)), e), [], ps)::xs) false ast
		| TopLet(ValBind(pat, (EmptySlot, pi, p1)), _) ->
				match_state atoms env [] ((Let(ValBind(pat, (EmptySlot, pi, p1)), ast), [], ps)::xs) true ast
		| _ -> raise (Run_time_error "Head of frame stack has no empty slot")

(* Duplicate (hd env) and push EofFunc onto F to create a new scope for Match exprs *)
and match_init atoms env ms fs is_top ast =
	let x::xs = fs in
	let e::es = env in
	match_state atoms (e::e::es) ms (x::(EofFunc, [], (0, 0))::xs) is_top ast

(* Invariant: is_val v = true *)
and match_state atoms env ms fs is_top ast =
	(* Permutations will be empty for elements of FS, so ignore them *)
	let (e, [], ps)::xs = fs in
  match e with
  | Let(ValBind(DontCareP, _), e) -> exp_state atoms env xs e
  | Let(ValBind(IdP(s), (EmptySlot, _, _)), e) ->
      exp_state atoms (cons (s, ast) env) xs e
	| Let(ValBind(IntP(n1), (EmptySlot, pi, p1)), e) ->
			(* TODO abstract this functionality into a function and call for each literal pattern *)
			let IntLiteral(n2), _, _ = ast in
			if n1 = n2 then exp_state atoms env xs e
			else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1); (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
				(* Remark
					-----------
					 Need to discard env and EofFunc which we added in match_init.
					 match_init must have been called since ms not empty and therefore we must
					 be pattern-matching within a Match expression.
				*)
        val_state atoms (List.tl env) ((Match((EmptySlot, pi, p1), br), [], ps)::(List.tl xs)) v)
      else
        raise (Run_time_error "Match failed: could not match int literal")
	| Let(ValBind(RealP(n1), (EmptySlot, pi, p1)), e) ->
			let RealLiteral(n2), _, _ = ast in
			if n1 = n2 then exp_state atoms env xs e
			else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1); (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
				(* See remark above *)
        val_state atoms (List.tl env) ((Match((EmptySlot, pi, p1), br), [], ps)::(List.tl xs)) v)
      else
        raise (Run_time_error "Match failed: could not match real literal")
	| Let(ValBind(BoolP(b1), (EmptySlot, pi, p1)), e) ->
			let BoolLiteral(b2), _, _ = ast in
			if b1 = b2 then exp_state atoms env xs e
			else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1); (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
				(* See remark above *)
        val_state atoms (List.tl env) ((Match((EmptySlot, pi, p1), br), [], ps)::(List.tl xs)) v)
      else
        raise (Run_time_error "Match failed: could not match bool literal")
	| Let(ValBind(StringP(s1), (EmptySlot, pi, p1)), e) ->
			let StringLiteral(s2), _, _ = ast in
			if s1 = s2 then exp_state atoms env xs e
			else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1); (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
				(* See remark above *)
        val_state atoms (List.tl env) ((Match((EmptySlot, pi, p1), br), [], ps)::(List.tl xs)) v)
      else
        raise (Run_time_error "Match failed: could not match string literal")
  | Let(ValBind(CtorP(s1, pat), (EmptySlot, pi, p1)), e) ->
      let Ctor(s2, e'), pi', _ = ast in
      if s1 = s2 then
        match_state atoms env ms ((Let(ValBind(pat, (EmptySlot, pi, p1)), e), [], ps)::xs)
					is_top (push pi' e')
      else if (List.length ms) > 0 then
        (assert ((List.length ms) == 1); (* ms should have 0 or 1 elements *)
        let (br, v)::_ = ms in
				(* See remark above *)
        val_state atoms (List.tl env) ((Match((EmptySlot, pi, p1), br), [], ps)::(List.tl xs)) v)
      else
        raise (Run_time_error ("Match failed: could not match constructor "^s2))
  | Let(ValBind(NameAbsP(IdP(x), pat), (EmptySlot, pi, p1)), e) ->
      let NameAb((NameLiteral(Name(s, n)), pi1, p2), v), pi2, p' = ast in
      let NameLiteral(a') = gen_atom atoms s in
			let v' = push [(Name(s, n), a')] v in
			let e' = if is_top then (NameAb((NameLiteral(a'), pi1, p2), v'), pi2, p') else e in
      match_state atoms (cons (x, (NameLiteral(a'), [], p2)) env) ms
        ((Let(ValBind(pat, (EmptySlot, pi, p1)), e'), [], ps)::xs) is_top v'
  | Let(ValBind(UnitP, _), e) -> exp_state atoms env xs e
  | Let(ValBind(ProdP(pat1, pat2), (EmptySlot, pi, p1)), e) ->
			(* TODO Update dynamic semantics for MATCH *)
      let Pair(v1, v2), pi', _ = ast in
      match_state atoms env ms
        ((Let(ValBind(pat1, (EmptySlot, pi, p1)),
          (Let(ValBind(pat2, push pi' v2), e), [], ps)), [], ps)::xs) is_top (push pi' v1)
	| _ -> raise (Run_time_error "Unexpected expression in MATCH state");;

