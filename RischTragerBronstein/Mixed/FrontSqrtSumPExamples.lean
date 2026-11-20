import RischTragerBronstein.Mixed.FrontSqrtSumP

/-!
# Examples: integrands rational in `√a` with poles

`frontSqrtAutoP a s cs …` splits `s` into `e₀ + e₁ √a` and decides `∫ s` with the poles `cs` of
`e₁` (each answer correct by `frontSqrtAutoP_sound`).
-/

namespace Curves.MT.FrontSqrtSumPEx

open Curves Curves.MT Curves.MT.Front

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

def lx : EE := EE.log EE.x

-- `∫ 1/(x (1 + √(log x))) = 2√(log x) − 2 log(1 + √(log x))` is elementary (a pole at `log x = 1`).
#guard frontSqrtAutoP Fl lx (SE.inv (SE.mul SE.x (SE.add (SE.cst 1) SE.th))) [EE.cst 1]
  ps 30 (fun _ ↦ 2) 3 = some true
-- `∫ 1/(1 + √(log x))` is not elementary.
#guard frontSqrtAutoP Fl lx (SE.inv (SE.add (SE.cst 1) SE.th)) [EE.cst 1] ps 30 (fun _ ↦ 2) 3 =
  some false

end Curves.MT.FrontSqrtSumPEx
