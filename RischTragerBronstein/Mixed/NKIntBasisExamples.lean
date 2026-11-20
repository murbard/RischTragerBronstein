import RischTragerBronstein.Mixed.NKIntBasis
import RischTragerBronstein.Mixed.NKExactExamples
import RischTragerBronstein.Mixed.NKInf2Decide

/-!
# Example: the exact part in a computed integral basis

`θ² + (t + 2)θ + 1 + t − t³ = 0` over `t = log x` (the node of `θ² + tθ = t³`, translated by
`θ ↦ θ + 1`). In the power basis the solver answers `none`, and the shearing search `exactTS` (which
only divides basis elements by powers of `t`) does not find a good basis; the integral basis
`(1, (θ + 1)/t)` computed by `exactTI` gives the answers: `∫ θ′ = θ`, and `θ` is not exact.
-/

namespace Curves.MT.NKIntBasisEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx

/-- `θ² + (t + 2)θ + 1 + t − t³`. -/
def F1 : BPoly ℚ := [[1, 1, 0, -1], [2, 1], [1]]
def P1 : GPoly (LC 1) := nkPC Fc ks 0 (liftCurve Fc ks 0 2 F1)
def Id2 : List (List (LC 1)) := [[onec, zer], [zer, onec]]
def d1 : GPoly (LC 1) := (dThetaC O1 P1).getD []

-- the power basis gives no answer
#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) P1 Id2 Id2 [zer, onec] = none
-- in the integral basis: `θ` is not exact, `θ′` is
#guard exactTI Fc ks 0 (primSysC Fc ks 0 ic lim0) P1 F1 2 [zer, onec] = some false
#guard exactTI Fc ks 0 (primSysC Fc ks 0 ic lim0) P1 F1 2
  ((List.range 2).map fun j ↦ d1.getD j O1.zero) = some true

/-! Irrational singular points: `(θ + t)² = (t² − 2)² (2t + 3)` (singular at `t = ±√2`). The integral
basis `(1, (θ + t)/(t² − 2))` is found over `ℚ(√2)` with rational codes (`finIntBasis`); the power
basis gives no answer. -/

def F2 : BPoly ℚ := [[-12, -8, 13, 8, -3, -2], [0, 2], [1]]
def P2 : GPoly (LC 1) := nkPC Fc ks 0 (liftCurve Fc ks 0 2 F2)
def d2 : GPoly (LC 1) := (dThetaC O1 P2).getD []

#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) P2 Id2 Id2 [zer, onec] = none
#guard exactTI Fc ks 0 (primSysC Fc ks 0 ic lim0) P2 F2 0 [zer, onec] = some false
#guard exactTI Fc ks 0 (primSysC Fc ks 0 ic lim0) P2 F2 0
  ((List.range 2).map fun j ↦ d2.getD j O1.zero) = some true

end Curves.MT.NKIntBasisEx
