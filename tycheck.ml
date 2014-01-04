
(* TODO Improve comments, add overall design doc, and check formatting *)
(* TODO Produce warnings on re-declaring name- and data-types in same scope *)

open AbSyn;;

let types = Hashtbl.create 50;; (* key: type name, val: actual type *)
let ctors = Hashtbl.create 50;; (* key: ctor name, val: list of types for ctor *)

exception Invalid_arg of string;;

(* make_funcT : typ list -> FuncT
 * Creates a function type (right-associative) from a list of types
 *)
let rec make_funcT ts =
  match ts with
  | [] -> raise (Invalid_arg "Passed empty list to make_funcT")
  | h::[] -> raise (Invalid_arg "Passed singleton list to make_funcT")
  | t1::t2::[] -> FuncT(t1, t2)
  | t::ts -> FuncT(t, make_funcT ts);;

(* init : user_types list -> unit 
 * Populates types and ctors hash tables with user-defined type info
 *)
let rec init xs = match xs with
  | (Ns(y::ys))::tl ->
      (Hashtbl.add types y (NameT(y ^ "_name"));
      print_string ("name : " ^ y ^ "_name\n");
      init (Ns(ys)::tl))
  | (Ns [])::tl -> init tl
  | (Ds(d::ds, ys))::tl ->
      (Hashtbl.add types d (DataT(d));
      print_string ("type : " ^ d ^ "\n");
      init (Ds(ds, ys)::tl))
  | (Ds([], (ctor, ts)::ys))::tl ->
      (Hashtbl.add ctors ctor (make_funcT ts);
      print_string (ctor ^ " : " ^ (string_of_typ (make_funcT ts)) ^ "\n");
      init (Ds([], ys)::tl))
  | (Ds([], []))::tl -> init tl
  | [] -> ();;

exception Not_member;;
exception Type_error of string;;

(* lookup : 'a -> ('a * 'b) list -> 'b
 * Return the value paired with x in the association list xs
 *)
let rec lookup x xs =
  match xs with
  | [] -> raise Not_member
  | (y, z)::ys -> if x=y then z else lookup x ys;;

let string_of_pos (r, c) =
  "[row "^(string_of_int r)^", col "^(string_of_int c)^"]";;

(* Raise a Type_error exception with string of the form:
  * msg: got _ but expected _ [position] *)
let failA msg got expected p =
  let msg = if msg = "" then "" else (msg^": ") in
  raise (Type_error (msg^"got "^(string_of_typ got)^" but expected "^
    (string_of_typ expected)^" "^(string_of_pos p)));;

(* Raise a Type_error exception with string of the form:
  * msg [position] *)
let failB msg p =
  raise (Type_error (msg^" "^(string_of_pos p)));;

(* (string * typ) list -> (string * typ) list -> pattern -> typ -> pos -> ((string * typ) list * (string * typ) list)
 * Check that pattern p can have type t.
 * Returns the new atoms and environment created by elaborating those passed with p : t.
 *)
let rec elaborate atoms env pat t ps =
  match pat with
  | IdP s -> ([], [(s, t)])
  | CtorP(s, p) ->
      (try
        (* Ctors only contains function types so no need to check for Match_failure *)
        let FuncT(t1, t2) = Hashtbl.find ctors s in
        if t=t2 then elaborate atoms env p t1 ps
        else failA "Expression does not match pattern type" t t2 ps
      with
      | Not_found -> failB ("Constructor "^s^" not recognised") ps)
  | NameAbsP(s, p) ->
      (match t with
      | NameAbT(n, t1) ->
          let ats, es = elaborate atoms env p t1 ps in
          let new_atoms, new_env = (ats @ atoms, es @ env) in
          (try let _ = lookup s new_atoms in
            failB ("Name identifier "^s^" already exists in this scope") ps
          with
          | Not_member -> ((s, NameT(n))::new_atoms, new_env))
      | _ -> failB "Expression is not a name abstraction" ps)
  | UnitP -> if t = UnitT then (atoms, env) else failA "" UnitT t ps
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
                with Not_member -> check_doms zs ys)
          in
          let ats1, es1 = elaborate atoms env p1 t1 ps in
          let ats2, es2 = elaborate atoms env p2 t2 ps in
          if check_doms (ats1 @ es1) (ats2 @ es2) then (ats1 @ ats2, es1 @ es2)
          else failB "Product pattern re-uses identifiers" ps
      | _ ->
          failB "Expression does not match pattern; expected product type" ps;;

(* 1. Get what p elaborates the env with (G')
 * 2. Get the type of e using the elaborated env (G' @ G)
 *)
let rec get_branch_type atoms env br t ps =
  match br with
  | [] -> failB "Branch is empty; no patterns to match against" ps
  | (p, e)::[] ->
      let ats, es = elaborate atoms env p t ps in
      let new_atoms, new_env = (ats @ atoms, es @ env) in
      get_type new_atoms new_env e
  | (p, e)::xs ->
      let ats, es = elaborate atoms env p t ps in
      let new_atoms, new_env = (ats @ atoms, es @ env) in
      let t1 = get_type new_atoms new_env e in
      let t2 = get_branch_type atoms env xs t ps in
      if t1 = t2 then t1 else failA "Branch cases don't agree" t2 t1 ps

and get_dec_type atoms env decl ps =
  match decl with
  | ValBind(p, e) -> let t = get_type atoms env e in elaborate atoms env p t ps
  | RecFunc(s1, s2, t1, t2, e) ->
      let t3 = get_type atoms ((s1, FuncT(t1, t2))::(s2, t1)::env) e in
      if t3 = t2 then ([], [(s1, FuncT(t1, t2))])
      else failA "Function body type does not match that of function" t3 t2 ps

(* TODO Come up with a more efficient data structure than association lists for
 * the atoms and environment -- needs to be able to handle scope:
   * let x = 5 in (let x = 6 in x+x end) + x end;;  => 17
   * env = [(x, 5)], env = [(x, 6), (x, 5)], env = [(x, 5)], env = []
 *)
and get_type atoms env ast =
  match ast with
  | Id(s), p ->
      (try (lookup s atoms) with
      | Not_member -> (try (lookup s env) with
      | Not_member -> failB ("Identifier '"^s^"' is not bound") p))
  | IntLiteral _, _ -> IntT
  | RealLiteral _, _ -> RealT
  | BoolLiteral _, _ -> BoolT
  | StringLiteral _, _ -> StringT
  | Ctor(s, e), p ->
      (try
        let FuncT(t1, t2) = Hashtbl.find ctors s in
        let t3 = get_type atoms env e in
        if t1=t3 then t2
        else failA ("In constructor "^s) t3 t1 p
      with
      | Not_found -> failB ("Constructor "^s^" not recognised") p)
  | Fresh s, p ->
      (try let t = Hashtbl.find types s in t with
      | Not_found -> failB ("Name type "^s^" has not been declared") p)
  | If(e1, e2, e3, e4), p ->
      (try
        let NameT(s1) = get_type atoms env e1 in
        let NameT(s2) = get_type atoms env e2 in
        if not(s1=s2) then failB "Name types don't match" p
        else let t1 = get_type atoms env e3 in
        let t2 = get_type atoms env e4 in
        if not(t1=t2) then failA "Branches of if must be same type" t2 t1 p
        else t2
      with
      | Match_failure _ -> failB "Expected name type" p)
  | Swap(e1, e2, e3), p ->
      (try
        let NameT(s1) = get_type atoms env e1 in
        let NameT(s2) = get_type atoms env e2 in
        if not(s1=s2) then failB "Name types don't match" p
        else let t = get_type atoms env e3 in t
      with
      | Match_failure _ -> failB "Expected name types in swap" p)
  | NameAb(e1, e2), p ->
      (try
        let NameT(s) = get_type atoms env e1 in
        let t = get_type atoms env e2 in NameAbT(s, t)
      with
      | Match_failure _ -> failB "Expected name type in name abstraction" p)
  | Unit, p -> UnitT
  | Pair(e1, e2), p ->
      let t1 = get_type atoms env e1 in
      let t2 = get_type atoms env e2 in ProdT(t1, t2)
  | Lambda(s, t1, e), p -> let t2 = get_type atoms ((s, t1)::env) e in FuncT(t1, t2)
  | App(e1, e2), p ->
      (try
        let FuncT(t1, t2) = get_type atoms env e1 in
        let t3 = get_type atoms env e2 in
        if not(t1=t3) then failA "" t3 t1 p
        else t2
      with
      | Match_failure _ -> failB "Expected function type in function application" p)
  | Match(e, b), p ->
      let t1 = get_type atoms env e in
      let t3 = get_branch_type atoms env b t1 p in t3
  | Let(d, e), p ->
      let ats, es = get_dec_type atoms env d p in
      get_type (ats @ atoms) (es @ env) e;;

