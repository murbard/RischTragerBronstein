import RischTragerBronstein.Mixed.FrontSqrtAuto

/-!
# Examples: integrands rational in `√a`

`frontSqrtAuto a s …` rewrites `s` as `e₀ + e₁ √a` (`SE.split`) and decides `∫ s`
(each answer correct by `frontSqrtAuto_sound`).
-/

namespace Curves.MT.FrontSqrtAutoEx

open Curves Curves.MT Curves.MT.Front

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

def ex1 : EE := EE.add (EE.exp EE.x) (EE.cst 1)

-- `∫ 1/√(eˣ + 1)` is elementary.
#guard frontSqrtAuto Fl ex1 (SE.inv SE.th) ps 30 (fun _ ↦ 2) 3 = some true
-- `∫ eˣ/(√(eˣ + 1) + 1) = ∫ (√(eˣ + 1) − 1)` is elementary.
#guard frontSqrtAuto Fl ex1 (SE.mul (SE.exp EE.x) (SE.inv (SE.add SE.th (SE.cst 1))))
  ps 30 (fun _ ↦ 2) 3 = some true
-- `∫ (1 + √(log x))²/x` is elementary.
#guard frontSqrtAuto Fl (EE.log EE.x)
  (SE.mul (SE.mul (SE.add (SE.cst 1) SE.th) (SE.add (SE.cst 1) SE.th)) (SE.inv SE.x))
  ps 30 (fun _ ↦ 2) 3 = some true
-- `∫ (log x)^{3/2} = ∫ √(log x)³` is not elementary.
#guard frontSqrtAuto Fl (EE.log EE.x) (SE.mul SE.th (SE.mul SE.th SE.th)) ps 30 (fun _ ↦ 2) 3 =
  some false

#eval frontSqrtAutoShow Fl ex1 (SE.mul (SE.exp EE.x) (SE.inv (SE.add SE.th (SE.cst 1))))
  ps 30 (fun _ ↦ 2) 3

end Curves.MT.FrontSqrtAutoEx
