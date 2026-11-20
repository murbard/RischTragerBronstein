import RischTragerBronstein.Mixed.FrontSqrtPole

/-!
# Examples: square roots with poles, from expressions

Over the line `y = x`, `frontSqrtP a e₁ cs` decides `∫ e₁ √a` with the poles `cs` (each answer
correct by `frontSqrtP_sound`).
-/

namespace Curves.MT.FrontSqrtPoleEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

-- `∫ √(log x)/(x (log x − 1))` is elementary (`u = log x`: `∫ √u/(u − 1) du`).
#guard frontSqrtP Fl (log x) (inv (mul x (add (log x) (cst (-1))))) [cst 1] ps 30 (fun _ ↦ 2) =
  some true
-- `∫ √(log x)/(log x − 1)` is not elementary.
#guard frontSqrtP Fl (log x) (inv (add (log x) (cst (-1)))) [cst 1] ps 30 (fun _ ↦ 2) = some false
-- `∫ √(eˣ + 1)/(eˣ − 1)` is elementary.
#guard frontSqrtP Fl (add (exp x) (cst 1)) (inv (add (exp x) (cst (-1)))) [cst 1] ps 30
  (fun _ ↦ 2) = some true

end Curves.MT.FrontSqrtPoleEx
