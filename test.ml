
let ys = [AbSyn.Ns(["a";"b";"c"]);
          AbSyn.Ds(["exp";"typ"], [("Lam", [AbSyn.IntT; AbSyn.DataT("exp")])])
         ];;

TyCheck.init ys;;
