
let ys = [AbSyn.Ns(["a";"b";"c"]);
          AbSyn.Ds(["exp";"typ"], [("Lam", [AbSyn.IntT; AbSyn.DataT("exp")])])];;

TyCheck.init ys;;

let test (e, p) =
    try (print_string ((AbSyn.string_of_expr e)^" : ");
         print_string ((AbSyn.stringify (TyCheck.get_type [] [] (e,p))^"\n"))) with
        TyCheck.Type_error(s) -> print_string (s^"\n");;

print_string "\n";;
test (AbSyn.Id("x"), (1,0));;
test (AbSyn.Ctor("App", (AbSyn.RealLiteral(3.), (5, 0))), (2,0));;
test (AbSyn.Ctor("Lam", (AbSyn.IntLiteral(3), (5, 0))), (3,0));;
test (AbSyn.Fresh("a"), (4, 0));;
test (AbSyn.If(
    (AbSyn.Fresh("b"), (0, 1)),
    (AbSyn.Fresh("b"), (0, 2)),
    (AbSyn.RealLiteral(0.), (0, 3)),
    (AbSyn.RealLiteral(1.), (0, 4))
), (5, 0));;
test (AbSyn.If(
    (AbSyn.Fresh("a"), (0, 1)),
    (AbSyn.Fresh("a"), (0, 2)),
    (AbSyn.StringLiteral("x"), (0, 3)),
    (AbSyn.StringLiteral("y"), (0, 4))
), (6, 0));;
test (AbSyn.Swap(
    (AbSyn.Fresh("c"), (0, 1)),
    (AbSyn.Fresh("c"), (0, 2)),
    (AbSyn.IntLiteral(5), (0, 3))
), (7, 0));;
test (AbSyn.NameAb(
    (AbSyn.Fresh("a"), (0, 1)),
    (AbSyn.BoolLiteral(false), (0, 2))
), (8, 0));;
test (AbSyn.Pair(
    (AbSyn.Fresh("a"), (0, 1)),
    (AbSyn.Fresh("c"), (0, 2))
), (9, 0));;
test (AbSyn.Lambda(
    "x",
    AbSyn.IntT,
    (AbSyn.Id("x"), (0, 1))
), (10, 0));;
test (AbSyn.App(
    (AbSyn.Lambda("x", AbSyn.IntT, (AbSyn.Id("x"), (1,0))), (0,1)),
    (AbSyn.IntLiteral(5), (0,2))
), (11, 0));;
