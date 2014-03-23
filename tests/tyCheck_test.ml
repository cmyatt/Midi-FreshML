open AbSyn;;

(* TODO Produce exhaustive tests (maybe auto-generate?), giving the code for
 * each AST tested *)

let ys = [Ns(["a";"b";"c"]);
          Ds(["exp";"typ"], [("Lam", FuncT(IntT, DataT("exp")))])];;

TyCheck.init ys;;

let test (e, p) =
  try (print_string ((string_of_expr e)^" : ");
     print_string ((string_of_typ (TyCheck.get_type [] [] (e,p))^"\n"))) with
    TyCheck.Type_error(s) -> print_string (s^"\n");;

print_string "\n";;
test (Id("x"), (1,0));;
test (Ctor("App", (RealLiteral(3.), (5, 0))), (2,0));;
test (Ctor("Lam", (IntLiteral(3), (5, 0))), (3,0));;
test (Fresh("a"), (4, 0));;
test (If(
  (Fresh("b"), (0, 1)),
  (Fresh("b"), (0, 2)),
  (RealLiteral(0.), (0, 3)),
  (RealLiteral(1.), (0, 4))
), (5, 0));;
test (If(
  (Fresh("a"), (0, 1)),
  (Fresh("a"), (0, 2)),
  (StringLiteral("x"), (0, 3)),
  (StringLiteral("y"), (0, 4))
), (6, 0));;
test (Swap(
  (Fresh("c"), (0, 1)),
  (Fresh("c"), (0, 2)),
  (IntLiteral(5), (0, 3))
), (7, 0));;
test (NameAb(
  (Fresh("a"), (0, 1)),
  (BoolLiteral(false), (0, 2))
), (8, 0));;
test (Pair(
  (Fresh("a"), (0, 1)),
  (Fresh("c"), (0, 2))
), (9, 0));;
test (Lambda(
  "x",
  IntT,
  (Id("x"), (0, 1))
), (10, 0));;
test (App(
  (Lambda("x", IntT, (Id("x"), (1,0))), (0,1)),
  (IntLiteral(5), (0,2))
), (11, 0));;
test (Match(
  (Lambda("x", IntT, (Id("x"), (1,0))), (0,1)),
  [((CtorP("Lam", IdP("x"))), (Id("x"), (97,2)))]
), (11, 0));;
test (Match(
  (Ctor("Lam", (IntLiteral(6), (2,23))), (1,0)),
  [((CtorP("Lam", IdP("x"))), (Id("x"), (97,2)))]
), (11, 0));;
test (Match(
  ((NameAb((Fresh("a"), (2,3)), (BoolLiteral(true), (4,5)))), (12,45)),
  [(NameAbsP("x", IdP("t")), (Id("t"), (2,4)))]
), (2,90));;
test (Let(
  (ValBind(ProdP(IdP("x"), IdP("y")), (Pair((IntLiteral(5), (0,1)),
  (BoolLiteral(false), (2,3))), (4,5)))),
  (Id("y"), (6,7))),
  (8,9));;
test (Let(
  (RecFunc("inc", "x", IntT, (ProdT(IntT, IntT)), (Pair((Id("x"), (0,1)),
  (IntLiteral(1), (2,3))), (4,5)))),
  (App((Id("inc"), (6,7)), (IntLiteral(5), (8,9))), (10,11))),
  (12,13));;
test (BinaryOp((IntLiteral(3), (0,1)), Add, (RealLiteral(4.), (2,3))), (4,5));;
test (UnaryOp(Neg, (RealLiteral(3.14159), (0,1))), (2,3));;
