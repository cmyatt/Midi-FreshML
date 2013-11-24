module AbSyn = struct

(* TODO Produce warnings on re-declaring name- and data-types. *)

type expr =
      Id of string
    | Ctor of string * exp
    | Fresh of string
    | If of exp * exp * exp * exp
    | Swap of exp * exp * exp
    | NameAb of exp * exp
    | Unit
    | Pair of exp * exp
    | Lambda of string * typ * exp
    | App of exp * exp
    | Match of exp * branch
    | Let of dec * exp

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

and branch =
      Single of string * pattern
    | Mult of string * pattern * branch

and pattern =
      IdP of string
    | CtorP of string * pattern
    | NameAbsP of string * pattern
    | UnitP
    | PairP of pattern * pattern

and dec =
      ValBind of pattern * exp
    | RecFunc of string * string * typ * typ * exp;;

type nty = string list;;

type dty = (string * typ list) list;;

type user_types =
      Ns of nty
    | Ds of dty;;

type position = int * int;; (* (row, col) in src text *)

type exp = expr * positon;;

type prog = user_types list * exp;;

end
