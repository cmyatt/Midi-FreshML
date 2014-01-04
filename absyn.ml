
type position = int * int;; (* (row, col) in src text *)

(* TODO Add basic arithmetic and string operations *)
type expr =
      Id of string
    | IntLiteral of int
    | RealLiteral of float
    | BoolLiteral of bool
    | StringLiteral of string 
    | Ctor of string * exp
    | Fresh of string
    | If of exp * exp * exp * exp   (* TODO change to test boolean expr rather than name equality *)
    | Swap of exp * exp * exp
    | NameAb of exp * exp
    | Unit
    | Pair of exp * exp
    | Lambda of string * typ * exp
    | App of exp * exp
    | Match of exp * branch
    | Let of dec * exp

and exp = expr * position

and typ =
      IntT
    | RealT
    | BoolT
    | StringT
    | DataT of string
    | NameT of string
    | NameAbT of string * typ
    | UnitT
    | ProdT of typ * typ
    | FuncT of typ * typ

and pattern =
      IdP of string
    | CtorP of string * pattern
    | NameAbsP of string * pattern
    | UnitP
    | ProdP of pattern * pattern

and dec =
      ValBind of pattern * exp
    (* func name, param name, param type, func type, func body *)
    | RecFunc of string * string * typ * typ * exp  

and branch = (pattern * exp) list;;

type nty = string list;;

type dty = string list * ((string * typ list) list);;

type user_types =
      Ns of nty
    | Ds of dty;;

type prog = user_types list * exp;;

(* string_of_typ : typ -> string
 * Get the string representation of the passed type.
 *)
let rec string_of_typ t =
  match t with
  | IntT -> "int"
  | RealT -> "real"
  | BoolT -> "bool"
  | StringT -> "string"
  | DataT(s) -> s
  | NameT(s) -> s
  | NameAbT(s, t) -> "<<" ^ s ^ ">>" ^ (string_of_typ t)
  | UnitT -> "unit"
  | ProdT(t1, t2) -> (string_of_typ t1) ^ " * " ^ (string_of_typ t2)
  | FuncT(t1, t2) -> (string_of_typ t1) ^ " -> " ^ (string_of_typ t2);;

let rec string_of_pattern pat =
  match pat with
  | IdP s -> s
  | CtorP(s, p) -> (s ^ " " ^ (string_of_pattern p))
  | NameAbsP(s, p) -> ("<<" ^ s ^ ">>(" ^ (string_of_pattern p) ^ ")")
  | UnitP -> "()"
  | ProdP(p1, p2) ->
      ("(" ^ (string_of_pattern p1) ^ ", " ^ (string_of_pattern p2) ^ ")");;

(* TODO Implement a string_of_branch function *)
(* TODO If string is too long, replace it with an ellipsis *)
let rec string_of_expr e =
  match e with
  | Id(s) -> s
  | IntLiteral(x) -> string_of_int x
  | RealLiteral(x) -> (string_of_float x)
  | BoolLiteral(x) -> (string_of_bool x)
  | StringLiteral(s) -> ("\""^s^"\"")
  | Ctor(s, (e, _)) -> (s^"("^(string_of_expr e)^")")
  | Fresh(s) -> ("(fresh : "^s^")")
  | If((e1,_), (e2,_), (e3, _), (e4,_)) ->
        ("if "^(string_of_expr e1)^" = "^(string_of_expr e2)^" then "^
          (string_of_expr e3)^" else "^(string_of_expr e4))
  | Swap((e1,_), (e2,_), (e3,_)) ->
        ("swap ("^(string_of_expr e1)^", "^(string_of_expr e2)^") in "^(string_of_expr e3))
  | NameAb((e1,_), (e2,_)) ->
      ("<<"^(string_of_expr e1)^">>("^(string_of_expr e2)^")")
  | Unit -> "()"
  | Pair((e1,_), (e2,_)) ->
      ("("^(string_of_expr e1)^", "^(string_of_expr e2)^")")
  | Lambda(s, t, (e,_)) ->
      ("(fun ("^s^" : "^(string_of_typ t)^") -> "^(string_of_expr e)^")")
  | App((e1,_), (e2,_)) -> ((string_of_expr e1)^" "^(string_of_expr e2))
  | Match((e,_), _) -> ("match "^(string_of_expr e)^" with ...")
  | Let(_, (e,_)) -> ("let _ = _ in "^(string_of_expr e));;

