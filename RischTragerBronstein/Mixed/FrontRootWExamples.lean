import RischTragerBronstein.Mixed.FrontRootW

/-!
# Examples: `n`-th roots over a logarithm with the antiderivative

`frontRootLogShow` prints the antiderivative (valid by `frontRootLogW_valid`).
-/

namespace Curves.MT.FrontRootWEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]

-- `∫ (log x)^{1/3}/x = (3/4) log x (log x)^{1/3}`.
#guard frontRootLogShow Fl 3 (log x) [cst 0, inv x] 3 =
  ["elementary; tower:", "t0 := log(x)", "antiderivative of e0 = sum of the pieces:", "level t0: 0",
    "base (rational in x): 0", "((((3/4)))*t0) * (log(x))^(1/3)"]

end Curves.MT.FrontRootWEx
