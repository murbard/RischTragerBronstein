import RischTragerBronstein.Mixed.FrontRootAutoP
import RischTragerBronstein.Mixed.FrontRootPoleExamples

/-!
# Examples: rational expressions in a cube root of a logarithm, with poles

Over the line `y = x`, with `θ³ = log x` and the number field `ℚ(ζ₃) = ℚ[X]/(X² + X + 1)`
(each answer correct by `frontRootAutoP_sound`). The norm of `1 + θ` is `1 + log x`: every
component of `1/(1 + θ)` has a pole at `log x = −1`.
-/

namespace Curves.MT.FrontRootAutoPEx

open Curves Curves.MT Curves.MT.Front Curves.MT.KYEx Curves.MT.FrontRootPoleEx

def lx : EE := EE.log EE.x
def pl : List (List EE) := [[], [EE.cst (-1)], [EE.cst (-1)]]

-- `∫ 1/(1 + θ)` is not elementary: the residues at `log x = −1` are not constant.
#guard frontRootAutoP Fc M3 3 [0, 1] lx (SE.inv (SE.add (SE.cst 1) SE.th)) pl [[], [[1]], [[1]]]
  ps 30 (fun _ ↦ 2) 8 = some false

-- `∫ 1/(x (1 + θ))` is elementary (`u = log x`: `∫ du/(1 + ∛u)`).
#guard frontRootAutoP Fc M3 3 [0, 1] lx
  (SE.inv (SE.mul SE.x (SE.add (SE.cst 1) SE.th))) pl [[], [[1]], [[1]]]
  ps 30 (fun _ ↦ 2) 8 = some true

end Curves.MT.FrontRootAutoPEx
