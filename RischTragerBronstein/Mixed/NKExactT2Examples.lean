import RischTragerBronstein.Mixed.NKExactT2
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: a singular curve, with an integral basis

`θ² + t θ − t³ = 0` over `t = log x` is singular at `t = 0` (`θ/t` is integral): in the power basis
the derivation matrix has a double pole with singular leading matrix and `exactG` answers `none`.
In the basis `w = (1, θ/t)` (`exactT`, `T = diag(1, 1/t)`, `T⁻¹ = diag(1, t)`, both products
checked), `∫ θ′ = θ` is found and `∫ θ` is proved not to lie in `ℚ(x, log x, θ)` (`exactT_correct`).
-/

namespace Curves.MT.NKExT

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx

def t3 : LC 1 := O1.mul (O1.mul tC tC) tC
def P4 : GPoly (LC 1) := [O1.neg t3, tC, onec]
def d4 : GPoly (LC 1) := (dThetaC O1 P4).getD []
def Tc : List (List (LC 1)) := [[onec, zer], [zer, O1.inv tC]]
def Ti : List (List (LC 1)) := [[onec, zer], [zer, tC]]

#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) P4 Tc Ti ((List.range 2).map fun j ↦ d4.getD j O1.zero) =
  some true
#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) P4 Tc Ti [zer, onec] = some false

end Curves.MT.NKExT
