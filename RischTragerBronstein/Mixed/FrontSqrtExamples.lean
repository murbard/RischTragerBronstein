import RischTragerBronstein.Mixed.FrontSqrt

/-!
# Examples: square roots over the top level from expressions

Over the line `y = x`, `frontSqrt a e₁` decides `∫ e₁ √a` (each answer correct by
`frontSqrt_sound`): below an exponential by `keDecide`, below a logarithm by `kpDecideK`.
-/

namespace Curves.MT.FrontSqrtEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

-- `∫ √(eˣ + 1)` is elementary.
#guard frontSqrt Fl (add (exp x) (cst 1)) (cst 1) ps 30 (fun _ ↦ 2) = some true
-- `∫ eˣ √(eˣ + 1)` is elementary.
#guard frontSqrt Fl (add (exp x) (cst 1)) (exp x) ps 30 (fun _ ↦ 2) = some true
-- `∫ √(eˣ + x)` is not elementary.
#guard frontSqrt Fl (add (exp x) x) (cst 1) ps 30 (fun _ ↦ 2) = some false
-- `∫ 1/√(eˣ + 1)` is elementary.
#guard frontSqrt Fl (add (exp x) (cst 1)) (inv (add (exp x) (cst 1))) ps 30 (fun _ ↦ 2) = some true
-- `∫ √(log x)` is not elementary.
#guard frontSqrt Fl (log x) (cst 1) ps 30 (fun _ ↦ 2) = some false
-- `∫ √(log x)/x = (2/3) (log x)^{3/2}`.
#guard frontSqrt Fl (log x) (inv x) ps 30 (fun _ ↦ 2) = some true
-- `∫ √(x + log x)` is not elementary.
#guard frontSqrt Fl (add x (log x)) (cst 1) ps 30 (fun _ ↦ 2) = some false
-- `∫ (1 + 1/x)/√(x + log x) = 2 √(x + log x)`.
#guard frontSqrt Fl (add x (log x)) (div (add (cst 1) (inv x)) (add x (log x))) ps 30
  (fun _ ↦ 2) = some true

end Curves.MT.FrontSqrtEx
