import RischTragerBronstein.Mixed.FrontNKW

/-!
# Example: the non-Kummer front end with the antiderivative

For `θ³ + θ = x log x`, `frontNKLogShow` prints `∫ (log x + 1) = x log x` (trace part; exact part
`0`), valid by `frontNKLogW_valid` (about 30 s).
-/

namespace Curves.MT.FrontNKWEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]

#guard frontNKLogShow Fl [neg (mul x (log x)), cst 1, cst 0] [add (log x) (cst 1)] 3 =
  ["elementary; tower:", "t0 := log(x)", "antiderivative of the trace part = sum of the pieces:",
    "level t0: (((1*x))*t0)", "base (rational in x): 0", "exact part: 0"]

end Curves.MT.FrontNKWEx
