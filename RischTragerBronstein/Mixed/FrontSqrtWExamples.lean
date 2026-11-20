import RischTragerBronstein.Mixed.FrontSqrtW

/-!
# Examples: square roots over the top level, with the antiderivative

`frontSqrtShow a e₁` prints the levels and the antiderivative of `∫ e₁ √a` (valid by
`frontSqrtEW_valid`). For `∫ √(eˣ + 1)`: `2 √(eˣ + 1) + 2 log(1 − Y) − log(N)`, `Y = √(eˣ + 1)`,
`N = 1 − (eˣ + 1)`, i.e. `2 √(eˣ + 1) + log((Y − 1)/(Y + 1))` up to a constant.
-/

namespace Curves.MT.FrontSqrtWEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

#guard frontSqrtShow Fl (add (exp x) (cst 1)) (cst 1) ps 30 (fun _ ↦ 2) =
  ["t0 := exp(x)", "elementary: (((-1)))/(-1/2) * sqrt((exp(x) + 1)) + C log(((1)) + (((-1))) Y) - (C/2) log(N), where Y = ((1)) sqrt((exp(x) + 1))/sqrt(1), C = 2 sqrt(1), N = (((1)))^2 - (((-1)))^2 ((1))^2/1 ((exp(x) + 1))"]
#guard frontSqrtShow Fl (add (exp x) (cst 1)) (exp x) ps 30 (fun _ ↦ 2) =
  ["t0 := exp(x)", "elementary: ((((2/3))) + (((2/3)))*t0)/1 * sqrt((exp(x) + 1))"]
#guard frontSqrtShow Fl (log x) (inv x) ps 30 (fun _ ↦ 2) =
  ["t0 := log(x)", "elementary: ((((2/3)))*t0) * sqrt(log(x))"]
#guard frontSqrtShow Fl (add x (log x)) (div (add (cst 1) (inv x)) (add x (log x))) ps 30
  (fun _ ↦ 2) = ["t0 := log(x)", "elementary: (((2))) * sqrt((x + log(x)))"]
#guard frontSqrtShow Fl (log x) (cst 1) ps 30 (fun _ ↦ 2) = ["t0 := log(x)", "not elementary"]

end Curves.MT.FrontSqrtWEx
