
type position = int * int;; (* (line, col) in src text *)

type bin_op =
  | Add
  | Sub
  | Div
  | Mult
	| Gt
	| Gteq
	| Lt
	| Lteq
	| Eq
	| Concat;;

type un_op =
  | Neg;;

type directive =
	| Quit
	| Use;;

(* string is for the type, int for the value *)
type name = string * int;;

(* A delayed permutation (list of swaps to apply) *)
type permutation = (name * name) list;;

(* invariant: is_val expr = true for all expressions in the environment *)
type env = (string * exp) list

and expr =
  | Id of string
  | IntLiteral of int
  | RealLiteral of float
  | BoolLiteral of bool
  | StringLiteral of string 
  | NameLiteral of name
  | Ctor of string * exp
  | Fresh of string
	(*| EqTest of exp * exp*)		(* equality test *)
  | If of exp * exp * exp
  | Swap of exp * exp * exp
  | NameAb of exp * exp
  | Unit
  | Pair of exp * exp
  | Lambda of string * typ * exp * env
  (* func name, param name, param type, func type, func body *)
  | RecFunc of string * string * typ * typ * exp * env
  | App of exp * exp
  | Match of exp * branch
  | Let of dec * exp
  | TopLet of dec * position
  | BinaryOp of exp * bin_op * exp
  | UnaryOp of un_op * exp
  | EmptySlot   (* used in interpreter as '_' in frame stack - so we can
                 * benefit from tail recursion *)
  | EofFunc     (* used in interpreter as a marker to transition between
                 * environments on the completion of a function application *)
	| Directive of directive * string list

and exp = expr * permutation * position

and typ =
  | IntT
  | RealT
  | BoolT
  | StringT
  | CtorT of typ
  | DataT of string
  | NameT of string
  | NameAbT of typ * typ  (* For now, the first type is constrained to NameT *)
  | UnitT
  | ProdT of typ * typ
  | FuncT of typ * typ

and pattern =
  | DontCareP
  | IdP of string
	| IntP of int
	| RealP of float
	| BoolP of bool
	| StringP of string
  | CtorP of string * pattern
  | NameAbsP of pattern * pattern
  | UnitP
  | ProdP of pattern * pattern

and dec =
  | ValBind of pattern * exp
  | RecF of expr  (* expr always RecFunc *)

and branch = (pattern * exp) list;;

type nty = string list;;

(* Type names * Constructor names and types *)
type dty = string list * ((string * typ) list);;

type user_types =
  | Ns of nty
  | Ds of dty;;

type prog = user_types list * exp;;

(* Returns whether or not the given expr is a value. *)
(* Assumes ex has been typechecked - otherwise NameAb case will be wrong *)
let rec is_val e =
	let (e, _, _) = e in
  match e with
  | IntLiteral _ -> true
  | RealLiteral _ -> true
  | BoolLiteral _ -> true
  | StringLiteral _ -> true
  | NameLiteral _ -> true
  | Unit -> true
	(* Must take an arg, so if env empty, then arg not yet bound,
	   so not yet an executable value *)
  | Lambda(_, _, _, env) -> not(env = [])
  | RecFunc(_, _, _, _, _, env) -> (env = [])
  | Ctor(_, e) -> is_val e
  | NameAb(e1, e2) -> is_val e1 && is_val e2
  | Pair(e1, e2) -> is_val e1 && is_val e2
  | _ -> false;;

let string_of_pos (r, c) =
  "(line "^(string_of_int r)^", col "^(string_of_int c)^")";;

(* string_of_typ : typ -> string
 * Get the string representation of the passed type.
 *)
let rec string_of_typ t =
  match t with
  | IntT -> "int"
  | RealT -> "real"
  | BoolT -> "bool"
  | StringT -> "string"
  | CtorT t -> string_of_typ t
  | DataT s -> s
  | NameT s -> s
  | NameAbT(t1, t2) -> "<<"^(string_of_typ t1)^">>("^(string_of_typ t2)^")"
  | UnitT -> "unit"
  | ProdT(t1, t2) -> (string_of_typ t1) ^ " * " ^ (string_of_typ t2)
  | FuncT(t1, t2) -> "("^(string_of_typ t1)^" -> "^(string_of_typ t2)^")";;

let rec string_of_pattern pat =
  match pat with
  | DontCareP -> "_"
  | IdP s -> s
	| IntP n -> string_of_int n
	| RealP r -> string_of_float r
	| BoolP b -> string_of_bool b
	| StringP s -> "\"" ^ s ^ "\""
  | CtorP(s, p) -> (s ^ " " ^ (string_of_pattern p))
  | NameAbsP(p1, p2) ->
      ("<<" ^ (string_of_pattern p1) ^ ">>(" ^ (string_of_pattern p2) ^ ")")
  | UnitP -> "()"
  | ProdP(p1, p2) ->
      ("(" ^ (string_of_pattern p1) ^ ", " ^ (string_of_pattern p2) ^ ")");;

let string_of_bin_op op =
  match op with
  | Add -> "+"
  | Sub -> "-"
  | Div -> "/"
  | Mult -> "*";;

let string_of_un_op op =
  match op with
  | Neg -> "~";;

let clip_str s =
	let max = 10000 in
  if String.length s > max then ((String.sub s 0 (max-3))^"...") else s;;

let string_of_directive d =
	match d with
	| Quit -> "#quit"
	| Use -> "#use";;

let string_of_perm xs =
	let rec strp = function
		| [] -> ""
		| ((s1, n1), (s2, n2))::[] -> Printf.sprintf "(%s_%d, %s_%d)" s1 n1 s2 n2
		| ((s1, n1), (s2, n2))::xs -> (Printf.sprintf "(%s_%d, %s_%d), " s1 n1 s2 n2) ^ (strp xs)
	in
		if (List.length xs) > 0 then ("[" ^ (strp xs) ^ "]") else "";;

let push pi e = let (e', pi', ps) = e in (e', pi' @ pi, ps);;

(* Apply permutation pi to name a *)
let permute pi a =
	List.fold_left (fun a (a1, a2) -> if a = a1 then a2 else if a = a2 then a1 else a) a pi;;

let push_perm v =
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
	| Ctor(s, v) -> (Ctor(s, push pi v), [], ps)
	| NameAb((NameLiteral(a), [], p), v) ->
			(NameAb((NameLiteral(permute pi a), [], p), push pi v), [], ps)
	| Pair(e1, e2) -> (Pair(push pi e1, push pi e2), [], ps);;

let rec string_of_dec dec =
  match dec with
  | ValBind(p, (e, _, _)) -> (string_of_pattern p)^" = "^(string_of_expr e)
  | RecF(RecFunc(s1, s2, t1, t2, (e, _, _),  _)) ->
      s1^"("^s2^" : "^(string_of_typ t1)^") : "^(string_of_typ t2)^
        " = "^(string_of_expr e)
  | _ ->
      print_string "!!! Error: Rec func decl does not contain recursive function";
      raise (Match_failure ("", 0, 0))

and string_of_branch b =
	match b with
	| [] -> ""
	| (p, (e, _, _))::xs ->
			"\n  | "^(string_of_pattern p)^" -> "^(string_of_expr e)^(string_of_branch xs)

(* TODO Consider not giving integer values for names in order to increase readibility *)
and string_of_expr e =
  match e with
  | Id(s) -> clip_str s
  | IntLiteral(x) -> clip_str (string_of_int x)
  | RealLiteral(x) -> clip_str (string_of_float x)
  | BoolLiteral(x) -> clip_str (string_of_bool x)
  | StringLiteral(s) -> clip_str ("\""^s^"\"")
  | NameLiteral(s, n) -> clip_str (s^"_"^(string_of_int n))	
  | Ctor(s, (e, _, _)) -> clip_str (s^" "^(string_of_expr e))
  | Fresh(s) -> clip_str ("(fresh : "^s^")")
  | If((e1, _, _), (e2, _, _), (e3, _, _)) ->
      clip_str ("if "^(string_of_expr e1)^" then "^(string_of_expr e2)^" else "^(string_of_expr e3))
  | Swap((e1, _, _), (e2, _, _), (e3, _, _)) ->
      clip_str ("swap ("^(string_of_expr e1)^", "^(string_of_expr e2)^") in "^(string_of_expr e3))
  | NameAb((e1, _, _), (e2, _, _)) ->
      clip_str ("<<"^(string_of_expr e1)^">>("^(string_of_expr e2)^")")
  | Unit -> "()"
  | Pair((e1, _, _), (e2, _, _)) ->
      clip_str ("("^(string_of_expr e1)^", "^(string_of_expr e2)^")")
  | Lambda(s, t, (e, _, _), _) -> clip_str "<fun>"
      (*clip_str ("(fun ("^s^" : "^(string_of_typ t)^") -> "^(string_of_expr e)^")")*)
  | RecFunc(s1, s2, t1, t2, (e, _, _), _) -> clip_str "<fun>"
  | App((e1, _, _), (e2, _, _)) -> clip_str ((string_of_expr e1)^" "^(string_of_expr e2))
  | Match((e, _, _), b) -> clip_str ("match "^(string_of_expr e)^" with "^(string_of_branch b))
  | Let(d, (e, _, _)) -> clip_str ("let "^(string_of_dec d)^" in "^(string_of_expr e))
  | TopLet(d, _) -> clip_str ("let "^(string_of_dec d))
  | BinaryOp((e1, _, _), op, (e2, _, _)) ->
      clip_str ((string_of_expr e1) ^ (string_of_bin_op op) ^ (string_of_expr e2))
  | UnaryOp(op, (e, _, _)) -> clip_str ((string_of_un_op op) ^ (string_of_expr e))
  | EmptySlot -> clip_str "_"
	| Directive(d, xs) ->
			clip_str ((string_of_directive d) ^ (List.fold_left (fun x y -> x^" "^y) "" xs));;
(*
and string_of_expr e =
  match e with
  | Id(s) -> clip_str s
  | IntLiteral(x) -> clip_str (string_of_int x)
  | RealLiteral(x) -> clip_str (string_of_float x)
  | BoolLiteral(x) -> clip_str (string_of_bool x)
  | StringLiteral(s) -> clip_str ("\""^s^"\"")
  | NameLiteral(s, n) -> clip_str (s^"_"^(string_of_int n))	
  | Ctor(s, e) -> clip_str (s^" "^(string_of_exp e))
  | Fresh(s) -> clip_str ("fresh : "^s)
  | If(e1, e2, e3) ->
      clip_str ("if "^(string_of_exp e1)^" then "^(string_of_exp e2)^" else "^(string_of_exp e3))
  | Swap(e1, e2, e3) ->
      clip_str ("swap ("^(string_of_exp e1)^", "^(string_of_exp e2)^") in "^(string_of_exp e3))
  | NameAb(e1, e2) ->
      clip_str ("<<"^(string_of_exp e1)^">>("^(string_of_exp e2))
  | Unit -> "()"
  | Pair(e1, e2) ->
      clip_str ("("^(string_of_exp e1)^", "^(string_of_exp e2)^")")
  | Lambda _ -> clip_str "<fun>"
  | RecFunc _ -> clip_str "<fun>"
  | App(e1, e2) -> clip_str ((string_of_exp e1)^" "^(string_of_exp e2))
  | Match(e, b) -> clip_str ("match "^(string_of_exp e)^" with "^(string_of_branch b))
  | Let(d, e) -> clip_str ("let "^(string_of_dec d)^" in "^(string_of_exp e))
  | TopLet(d, _) -> clip_str ("let "^(string_of_dec d))
  | BinaryOp(e1, op, e2) ->
      clip_str ((string_of_exp e1) ^ (string_of_bin_op op) ^ (string_of_exp e2))
  | UnaryOp(op, e) -> clip_str ((string_of_un_op op) ^ (string_of_exp e))
  | EmptySlot -> clip_str "_"
	| Directive(d, xs) ->
			clip_str ((string_of_directive d) ^ (List.fold_left (fun x y -> x^" "^y) "" xs))

and string_of_exp ex =
	let (e, pi, _) = ex in "(" ^ (string_of_expr e) ^ ")";;(*"---" ^ (string_of_perm pi) ^ ")";;*)
*)

(* Returns a string of the form id : type = value for user
 * feedback following a top-level let.
 *)
let rec extract_ids pat v t =
	let ts = string_of_typ t in
	let vs = string_of_expr v in
	let str = " : " ^ ts ^ " = " ^ vs in
	match pat with
	| DontCareP -> "-" ^ str
	| IdP(s) -> "val " ^ s ^ str
	| IntP _ -> "-" ^ str
	| RealP _ -> "-" ^ str
	| BoolP _ -> "-" ^ str
	| StringP _ -> "-" ^ str
	| CtorP(_, p) -> let Ctor(_, (v', _, _)) = v in extract_ids p v' t
	| NameAbsP(p1, p2) ->
			let NameAb((v1, _, _), (v2, _, _)) = v in 
			let NameAbT(t1, t2) = t in
			(extract_ids p1 v1 t1) ^ "\n" ^ (extract_ids p2 v2 t2)
	| UnitP -> ""
	| ProdP(p1, p2) ->
			let Pair((v1, _, _), (v2, _, _)) = v in 
			let ProdT(t1, t2) = t in
			(extract_ids p1 v1 t1) ^ "\n" ^ (extract_ids p2 v2 t2);;

