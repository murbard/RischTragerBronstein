import RischTragerBronstein.Mixed.FrontSqrtSumW

/-!
# Examples: whole integrands `e₀ + e₁ √a` with the antiderivative

`frontSqrtSumShow` prints the antiderivative of `e₀` (the pieces of `elMW`) and of `e₁ √a`
(valid by `frontSqrtSumW_valid`).
-/

namespace Curves.MT.FrontSqrtSumWEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

-- `∫ (1/x + √(log x)/x) = log x + (2/3) log x √(log x)`.
#guard frontSqrtSumShow Fl (log x) (inv x) (inv x) ps 30 (fun _ ↦ 2) 3 =
  ["elementary; tower:", "t0 := log(x)", "antiderivative of e0 = sum of the pieces:", "level t0: 0",
    "base (rational in x): sum over the roots a of 1*x of (1)/(1) * log(x - a)",
    "antiderivative of e1 sqrt(a): ((((2/3)))*t0) * sqrt(log(x))"]

end Curves.MT.FrontSqrtSumWEx
