import RischTragerBronstein.Mixed.FrontSqrtSum

/-!
# Examples: whole integrands `e₀ + e₁ √a`

Over the line `y = x`, `frontSqrtSum a e₀ e₁ … N` decides `∫ (e₀ + e₁ √a)` (each answer correct by
`frontSqrtSum_sound`).
-/

namespace Curves.MT.FrontSqrtSumEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

-- `∫ (eˣ + √(eˣ + 1))` is elementary.
#guard frontSqrtSum Fl (add (exp x) (cst 1)) (exp x) (cst 1) ps 30 (fun _ ↦ 2) 3 = some true
-- `∫ (eˣ/x + √(eˣ + 1))` is not elementary (the part `eˣ/x` is not).
#guard frontSqrtSum Fl (add (exp x) (cst 1)) (div (exp x) x) (cst 1) ps 30 (fun _ ↦ 2) 3 =
  some false
-- `∫ (1/log x + √(log x)/x)` is not elementary (the part `1/log x` is not).
#guard frontSqrtSum Fl (log x) (inv (log x)) (inv x) ps 30 (fun _ ↦ 2) 3 = some false
-- `∫ (1/x + √(log x)/x) = log x + (2/3) (log x)^{3/2}`.
#guard frontSqrtSum Fl (log x) (inv x) (inv x) ps 30 (fun _ ↦ 2) 3 = some true

end Curves.MT.FrontSqrtSumEx
