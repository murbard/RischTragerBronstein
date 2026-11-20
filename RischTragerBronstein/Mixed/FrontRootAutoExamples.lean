import RischTragerBronstein.Mixed.FrontRootAuto

/-!
# Examples: integrands rational in `θ = (log x)^{1/3}`

`frontRootAuto n a s …` rewrites `s` as `∑ eⱼ θʲ` (`SE.splitN`, inverses by the adjugate) and
decides `∫ s` (each answer correct by `frontRootAuto_sound`).
-/

namespace Curves.MT.FrontRootAutoEx

open Curves Curves.MT Curves.MT.Front

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (CPoly.toPoly (fKc Fl))) := ⟨fKc_irr_linear [0, -1]⟩

def lx : EE := EE.log EE.x

-- `∫ 1/(x (log x)^{1/3})` is elementary.
#guard frontRootAuto Fl 3 lx (SE.mul (SE.inv SE.th) (SE.inv SE.x)) 3 = some true
-- `∫ (1 + (log x)^{1/3})²/x` is elementary.
#guard frontRootAuto Fl 3 lx
  (SE.mul (SE.mul (SE.add (SE.cst 1) SE.th) (SE.add (SE.cst 1) SE.th)) (SE.inv SE.x)) 3 =
  some true
-- `∫ (θ + 1)/(x θ)`, `θ = (log x)^{1/3}`, is elementary.
#guard frontRootAuto Fl 3 lx
  (SE.mul (SE.add SE.th (SE.cst 1)) (SE.inv (SE.mul SE.x SE.th))) 3 = some true
-- `∫ 1/(log x)^{1/3}` is not elementary.
#guard frontRootAuto Fl 3 lx (SE.inv SE.th) 3 = some false
-- `∫ (log x)^{2/3}` is not elementary.
#guard frontRootAuto Fl 3 lx (SE.mul SE.th SE.th) 3 = some false

#eval frontRootAutoShow Fl 3 lx (SE.mul (SE.inv SE.th) (SE.inv SE.x)) 3

end Curves.MT.FrontRootAutoEx
