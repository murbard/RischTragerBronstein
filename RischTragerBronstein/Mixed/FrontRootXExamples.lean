import RischTragerBronstein.Mixed.FrontRootAutoX
import RischTragerBronstein.Mixed.FrontRootPoleExamples
import RischTragerBronstein.Mixed.KRIrr

/-!
# Examples: cube roots over an exponential, from expressions

Over the line `y = x`, with the number field `ℚ(ζ₃) = ℚ[X]/(X² + X + 1)`: `frontRootSumX` and
`frontRootAutoX` reach `krDecide` (no poles) and `kyDecide` (poles) below an exponential (each
answer correct by `frontRootSumX_sound`, `frontRootAutoX_sound`).
-/

namespace Curves.MT.FrontRootXEx

open Curves Curves.MT Curves.MT.Front Curves.MT.KYEx Curves.MT.FrontRootPoleEx

instance (m : ℕ) : Fact (Irreducible (CPoly.toPoly (cycK Fc m 3))) :=
  ⟨cycK_irr_linear [0, -1] m 3 (by norm_num)⟩

def ex : EE := EE.exp EE.x

-- `∫ ∛(x + eˣ)` is not elementary.
#guard frontRootAutoX Fc M3 3 [0, 1] (EE.add EE.x ex) SE.th [] [] ps 30 (fun _ ↦ 2) 8 = some false

-- `∫ ∛(1 + eˣ)/(eˣ − x)` is not elementary: the residue at `eˣ = x` is not constant.
#guard frontRootSumX Fc M3 3 [0, 1] (EE.add (EE.cst 1) ex)
  [EE.cst 0, EE.inv (EE.add ex (EE.neg EE.x))] [[], [EE.x]] [[], [[2]]] ps 30 (fun _ ↦ 2) 8 =
  some false

-- `∫ (eˣ + ∛(1 + eˣ))` is elementary.
#guard frontRootSumX Fc M3 3 [0, 1] (EE.add (EE.cst 1) ex) [ex, EE.cst 1] [] [] ps 30
  (fun _ ↦ 2) 8 = some true

end Curves.MT.FrontRootXEx
