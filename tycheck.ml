(* TODO Improve comments, add overall design doc, and check formatting *)
(* TODO Produce warnings on re-declaring name- and data-types in same scope *)

open AbSyn;;

exception Type_error of string;;

(* lookup : 'a -> ('a * 'b) list -> 'b
 * Return the value paired with x in the association list xs
 *)
let rec lookup x xs =
  match xs with
  | [] -> raise Not_found
  | (y, z)::ys -> if x=y then z else lookup x ys;;

(* Raise a Type_error exception with string of the form:
  * msg: got _ but expected _ [position] *)
let failA msg got expected p =
  let msg = if msg = "" then "Got " else (msg^": got ") in
  raise (Type_error (msg^(string_of_typ got)^" but expected "^
    (string_of_typ expected)^" "^(string_of_pos p)));;

(* Raise a Type_error exception with string of the form:
  * msg [position] *)
let failB msg p =
  raise (Type_error (msg^" "^(string_of_pos p)));;

(* Get the number of args to a function. Assumes t is a FuncT *)
let rec count_args t =
  match t with
  | FuncT(t1, t2) -> (count_args t1) + (count_args t2) - 1
  | _ -> 1;;

(* Check that pattern p can have type t.
 * Returns the new environment created by elaborating the env passed with p : t.
 *)
let rec elaborate types env pat t ps =
  match pat with
  | DontCareP -> []
  | IdP s -> [(s, t)]
  | IntP n ->
      if t = IntT then []
      else failA "Expression does not match pattern type" t IntT ps
  | RealP r -> 
      if t = RealT then []
      else failA "Expression does not match pattern type" t RealT ps
  | BoolP b -> 
      if t = BoolT then []
      else failA "Expression does not match pattern type" t BoolT ps
  | StringP s -> 
      if t = StringT then []
      else failA "Expression does not match pattern type" t StringT ps
  | CtorP(s, p) ->
      (try
        let CtorT(FuncT(t1, t2)) = Hashtbl.find types s in
        if t=t2 then elaborate types env p t1 ps
        else failA "Expression does not match pattern type" t t2 ps
      with
      | Not_found -> failB ("Constructor "^s^" not recognised") ps
      | Match_failure _ ->
          failB ("Expected function type for constructor '"^s^"'") ps)
  | NameAbsP(IdP(s1), p) ->
      (match t with
      | NameAbT(NameT(s2), t1) ->
          let es = elaborate types env p t1 ps in
          (try
            let _ = lookup s1 es in
            failB ("Name identifier "^s1^" already exists in this scope") ps
          with
          | Not_found -> (elaborate types env (IdP s1) (NameT s2) ps) @ (es @ env))
      | _ -> failB "Expression is not a name abstraction" ps)
  | NameAbsP(DontCareP, p) ->
      (match t with
      | NameAbT(NameT(s2), t1) ->
          let es = elaborate types env p t1 ps in es @ env
      | _ -> failB "Expression is not a name abstraction" ps)
  | NameAbsP _ ->
      failB ("Unexpected pattern in name abstraction binding position. "^
        "Must be id or _") ps
  | UnitP -> if t = UnitT then [] else failA "" UnitT t ps
  | ProdP(p1, p2) ->
      match t with
      | ProdT(t1, t2) ->
          (* Check that the intersection of the domains of two associatiolists
           * is empty. *)
          let rec check_doms xs ys =
            match xs with
            | [] -> true
            | (s, _)::zs ->
                (try
                  let _ = lookup s ys in false
                with Not_found -> check_doms zs ys)
          in
          let es1 = elaborate types env p1 t1 ps in
          let es2 = elaborate types env p2 t2 ps in
          if check_doms es1 es2 then es1 @ es2
          else failB "Product pattern re-uses identifiers" ps
      | _ ->
          failB "Expression does not match pattern; expected product type" ps;;

(* Bind the identifiers within a pattern to a type in the top-level. *)
let rec bind_val types tbl pat t ps =
  match pat with
  | DontCareP -> t
  | IdP s -> Hashtbl.add tbl s t; t
  | IntP _ -> if t = IntT then IntT else failA "" StringT t ps
  | RealP _ -> if t = RealT then RealT else failA "" RealT t ps
  | BoolP _ -> if t = BoolT then BoolT else failA "" BoolT t ps
  | StringP _ -> if t = StringT then StringT else failA "" StringT t ps
  | CtorP(s, p) ->
      (try
        let CtorT(FuncT(t1, t2)) = Hashtbl.find types s in
        if t=t2 then bind_val types tbl p t1 ps
        else failA "Expression does not match pattern type" t t2 ps
      with
      | Not_found -> failB ("Constructor "^s^" not recognised") ps
      | Match_failure _ ->
          failB ("Expected function type for constructor '"^s^"'") ps)
  | NameAbsP(IdP(s1), p) ->
      (match t with
      | NameAbT(NameT(s2), t1) ->
          let _ = bind_val types tbl p t1 ps in (Hashtbl.add tbl s1 (NameT s2); t)
      | _ -> failB "Expression is not a name abstraction" ps)
  | NameAbsP(DontCareP, p) ->
      (match t with
      | NameAbT(NameT(s2), t1) -> let _ = bind_val types tbl p t1 ps in t
      | _ -> failB "Expression is not a name abstraction" ps)
  | NameAbsP _ ->
      failB ("Unexpected pattern in name abstraction binding position. "^
        "Must be id or _") ps
  | UnitP -> if t = UnitT then UnitT else failA "" UnitT t ps
  | ProdP(p1, p2) ->
      match t with
      | ProdT(t1, t2) ->
          (* Check that the intersection of the domains of two association lists
           * is empty. *)
          let rec check_doms xs ys =
            match xs with
            | [] -> true
            | (s, _)::zs ->
                (try
                  let _ = lookup s ys in false
                with Not_found -> check_doms zs ys)
          in
          let es1 = elaborate types [] p1 t1 ps in
          let es2 = elaborate types [] p2 t2 ps in
          if check_doms es1 es2 then
            let _ = bind_val types tbl p1 t1 ps in
            let _ = bind_val types tbl p2 t2 ps in ProdT(t1, t2)
          else failB "Product pattern re-uses identifiers" ps
      | _ ->
          failB "Expression does not match pattern; expected product type" ps;;

(* Print contents of the environment - for debugging. *)
let rec print_env env =
  match env with
  | [] -> print_string "\n"
  | (s, t)::es -> Printf.printf "(%s : %s) " s (string_of_typ t); print_env es;;

(* 1. Get what p elaborates the env with (G')
 * 2. Get the type of e using the elaborated env (G' @ G)
 *)
let rec get_branch_type types top_level env br t ps =
  match br with
  | [] -> failB "Branch is empty; no patterns to match against" ps
  | (p, e)::[] ->
      let es = elaborate types env p t ps in
      let new_env = es @ env in
      get_type types top_level new_env e
  | (p, e)::xs ->
      let es = elaborate types env p t ps in
      let new_env = es @ env in
      let t1 = get_type types top_level new_env e in
      let t2 = get_branch_type types top_level env xs t ps in
      if t1 = t2 then t1 else failA "Branch cases don't agree" t2 t1 ps

and get_dec_type types top_level env decl ps =
  match decl with
  | ValBind(p, e) -> let t = get_type types top_level env e in elaborate types env p t ps
  | RecF(RecFunc(s1, s2, t1, t2, e, _)) ->
      let t3 = get_type types top_level ((s1, FuncT(t1, t2))::(s2, t1)::env) e in
      if t3 = t2 then [(s1, FuncT(t1, t2))]
      else failA "Function body type does not match that of function" t3 t2 ps
  | _ -> failB "Rec func declaration does not contain recursive function" ps

(* TODO Come up with a more efficient data structure than association lists for
 * the environment -- needs to be able to handle scope:
   * let x = 5 in (let x = 6 in x+x end) + x end;;  => 17
   * env = [(x, 5)], env = [(x, 6), (x, 5)], env = [(x, 5)], env = []
 *)
(*
 * types - maps name and data type names to their types
 * top_level - maps top-level declarations to their types (usually functions)
 * env - maps local ids to their types
 *)
and get_type types top_level env ast =
  let (e, _, p) = ast in
  match (e, p) with
  | Id(s), p ->
      (* Lookup in local env, then top-level env and finally types *)
      (try (lookup s env) with
      | Not_found ->
          (try Hashtbl.find top_level s with
          | Not_found ->
            (try
              let t = Hashtbl.find types s in
              (match t with
              | CtorT t1 ->
                  failB ("The constructor "^s^" expects "^(string_of_int (count_args t1))^" argument(s)") p 
              | _ -> failB ("Unbound identifier "^s) p)
            with Not_found -> failB ("Unbound identifier "^s) p)))
  | IntLiteral _, _ -> IntT
  | RealLiteral _, _ -> RealT
  | BoolLiteral _, _ -> BoolT
  | StringLiteral _, _ -> StringT
  | NameLiteral(s, _), _ -> NameT(s)
  | Ctor(s, e), p ->
      (try
        let CtorT(FuncT(t1, t2)) = Hashtbl.find types s in
        let t3 = get_type types top_level env e in
        if t1=t3 then t2
        else failA ("In constructor "^s) t3 t1 p
      with
      | Not_found -> failB ("Constructor "^s^" not recognised") p
      | Match_failure _ ->
          failB ("Expected function type for constructor '"^s^"'") p)
  | Fresh s, p ->
      (try let t = Hashtbl.find types s in t with
      | Not_found -> failB ("Name type "^s^" has not been declared") p)
  | If(e1, e2, e3), p ->
      let t1 = get_type types top_level env e1 in
      if t1 = BoolT then
        let t2 = get_type types top_level env e2 in
        let t3 = get_type types top_level env e3 in
        if not(t2 = t3) then failA "" t3 t2 p else t2
      else failB "Expected bool in if expression" p
  | Swap(e1, e2, e3), p ->
      (try
        let NameT(s1) = get_type types top_level env e1 in
        let NameT(s2) = get_type types top_level env e2 in
        if not(s1=s2) then failB "Name types don't match" p
        else let t = get_type types top_level env e3 in t
      with
      | Match_failure _ ->
          (let (e5, _, _) = e1 in Printf.printf "x : %s\n" (string_of_expr e5);
          failB "Expected name types in swap" p))
  | NameAb(e1, e2), p ->
      (try
        let NameT(s) = get_type types top_level env e1 in
        let t = get_type types top_level env e2 in NameAbT(NameT(s), t)
      with
      | Match_failure _ -> failB "Expected name type in name abstraction" p)
  | Unit, p -> UnitT
  | Pair(e1, e2), p ->
      let t1 = get_type types top_level env e1 in
      let t2 = get_type types top_level env e2 in ProdT(t1, t2)
  | Lambda(s, t1, e, _), p -> let t2 = get_type types top_level ((s, t1)::env) e in FuncT(t1, t2)
  | RecFunc(_, _, t1, t2, _, _), _ -> FuncT(t1, t2)
  | App(e1, e2), p ->
      (try
        let FuncT(t1, t2) = get_type types top_level env e1 in
        let t3 = get_type types top_level env e2 in
        if not(t1=t3) then failA "" t3 t1 p
        else t2
      with
      | Match_failure _ -> failB "This expression is not a function; it cannot be applied" p)
  | Match(e, b), p ->
      let t1 = get_type types top_level env e in
      let t3 = get_branch_type types top_level env b t1 p in t3
  | Let(d, e), p ->
      let es = get_dec_type types top_level env d p in
      get_type types top_level (es @ env) e
  | TopLet(d, ps), _ ->
      (match d with
      | ValBind(p, e) -> let t = get_type types top_level env e in bind_val types top_level p t ps
      | RecF(RecFunc(s1, s2, t1, t2, e, _)) ->
          let t3 = get_type types top_level ((s1, FuncT(t1, t2))::(s2, t1)::env) e in
          if t3 = t2 then (Hashtbl.add top_level s1 (FuncT(t1, t2)); FuncT(t1, t2))
          else failA "Function body type does not match that of function" t3 t2 ps
      | _ -> failB "Rec func declaration does not contain recursive function" ps)
  | BinaryOp((e1, pi1, p1), op, (e2, pi2, p2)), p ->
      let t1 = get_type types top_level env (e1, pi1, p1) in
      let t2 = get_type types top_level env (e2, pi2, p2) in
      if t1 = t2 then
        let is_num_typ t =
          if t = IntT || t = RealT then t else failB "Expected numeric type" p2
        in
        let is_ineq_typ t =
          match t with
          | IntT -> BoolT
          | RealT -> BoolT
          | StringT -> BoolT
          | _ -> failB "Expected comparable type" p2
        in
        (match op with
        | Add -> is_num_typ t1
        | Sub -> is_num_typ t1
        | Div -> is_num_typ t1
        | Mult -> is_num_typ t1
        | Gt -> is_ineq_typ t1
        | Gteq -> is_ineq_typ t1
        | Lt -> is_ineq_typ t1
        | Lteq -> is_ineq_typ t1
        | Eq -> BoolT
        | Concat -> if t1 = StringT then StringT else failA "" t1 StringT p2)
      else failB "Operand types don't match" p2
  | UnaryOp(op, (e, pi, p)), _ ->
      let t = get_type types top_level env (e, pi, p) in
      (match t with
      | IntT -> IntT
      | RealT -> RealT
      | _ -> failB "Expected numeric type for unary operation" p);;

