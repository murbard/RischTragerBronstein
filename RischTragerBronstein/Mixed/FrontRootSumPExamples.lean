import RischTragerBronstein.Mixed.FrontRootSumP
import RischTragerBronstein.Mixed.FrontRootPoleExamples

/-!
# Examples: whole integrands in a cube root of a logarithm, with poles

Over the line `y = x`, with `θ³ = log x` and the number field `ℚ(ζ₃) = ℚ[X]/(X² + X + 1)`
(each answer correct by `frontRootSumP_sound`).
-/

namespace Curves.MT.FrontRootSumPEx

open Curves Curves.MT Curves.MT.Front Curves.MT.KYEx Curves.MT.FrontRootPoleEx EE

/-- `1/(x (log x − 1))`. -/
def e1 : EE := inv (mul x (add (log x) (cst (-1))))

-- `∫ (1/x + θ/(x (log x − 1)) + θ²/x)` is elementary.
#guard frontRootSumP Fc M3 3 [0, 1] (log x) [inv x, e1, inv x] [[], [cst 1], []] [[], [[1]], []]
  ps 30 (fun _ ↦ 2) 8 = some true

-- `∫ (1/x + θ/(log x − 1) + θ²/x)` is not: the residue at `log x = 1` is not constant.
#guard frontRootSumP Fc M3 3 [0, 1] (log x) [inv x, inv (add (log x) (cst (-1))), inv x]
  [[], [cst 1], []] [[], [[1]], []] ps 30 (fun _ ↦ 2) 8 = some false

end Curves.MT.FrontRootSumPEx
