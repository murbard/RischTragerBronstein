import RischTragerBronstein.Mixed.NKShear
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: the integral basis found by shearing

`θ² + t θ − t³ = 0` over `t = log x` (singular at `t = 0`). In the power basis `(1, θ)` the solver
answers `none`; `exactTS` tries the shearings by the factor `t` of the matrix denominator and finds
the basis `(1, θ/t)`: `∫ θ′ = θ`, and `θ` is not exact (`∫ θ ∉ ℚ(x, log x, θ)`), with no basis
supplied.
-/

namespace Curves.MT.NKShearEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx

def t3 : LC 1 := O1.mul (O1.mul tC tC) tC
def P4 : GPoly (LC 1) := [O1.neg t3, tC, onec]
def d4 : GPoly (LC 1) := (dThetaC O1 P4).getD []
def Id2 : List (List (LC 1)) := [[onec, zer], [zer, onec]]

#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) P4 Id2 Id2
  ((List.range 2).map fun j ↦ d4.getD j O1.zero) = none
#guard exactTS Fc ks 0 (primSysC Fc ks 0 ic lim0) P4 Id2 Id2
  ((List.range 2).map fun j ↦ d4.getD j O1.zero) = some true
#guard exactTS Fc ks 0 (primSysC Fc ks 0 ic lim0) P4 Id2 Id2 [zer, onec] = some false

/-! `θ² + tθ = t⁵` needs `(1, θ/t²)` (found by the shearing search). -/
def t5 : LC 1 := O1.mul (O1.mul (O1.mul tC tC) (O1.mul tC tC)) tC
def P6 : GPoly (LC 1) := [O1.neg t5, tC, onec]
def d6 : GPoly (LC 1) := (dThetaC O1 P6).getD []
#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) P6 Id2 Id2
  ((List.range 2).map fun j ↦ d6.getD j O1.zero) = none
#guard exactTS Fc ks 0 (primSysC Fc ks 0 ic lim0) P6 Id2 Id2
  ((List.range 2).map fun j ↦ d6.getD j O1.zero) = some true
#guard exactTS Fc ks 0 (primSysC Fc ks 0 ic lim0) P6 Id2 Id2 [zer, onec] = some false

end Curves.MT.NKShearEx
