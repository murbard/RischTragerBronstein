import RischTragerBronstein.Mixed.SysPrim
import RischTragerBronstein.Mixed.MTAlg

/-!
# Examples: coupled Risch systems at a primitive level

Tower `x`, `t = log x` (`t′ = 1/x`). Each output `(e, W)` gives the solution `W / Den` of
`Y′ + (A₀/q) Y = ∑ eₗ G₀ₗ / h` (`primSysC_sound`), and every rational solution is a constant
combination of them (`primSysC_complete`).
-/

namespace Curves.MT.SysEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def ic : GPoly (GFrac ℚ) := [([1], [0, 1])]
def one0 : GPoly (GFrac ℚ) := [([1], [1])]
def two_x : GPoly (GFrac ℚ) := [([2], [0, 1])]
def ks : (m : ℕ) → KindC m
  | 0 => .prim ic
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lim0 : List (LC 0) → List (List ℚ × LC 0) := fun ws ↦ paramLimC Fc ks lv 0 ws

/-- Does some output have right-hand-side coefficients `e`? -/
def hasCoeff {n : ℕ} (r : Option (GPoly (LC 0) × List (List ℚ × (Fin n → GPoly (LC 0)))))
    (e : List ℚ) : Bool :=
  match r with
  | some r => r.2.any fun b ↦ b.1 == e
  | none => false

-- `Y′ = 1`: `Y = x`.
#guard hasCoeff (primSysC Fc ks 0 ic lim0 1 (fun _ _ ↦ []) [one0] [one0] [fun _ ↦ [one0]]) [1]
-- `Y′ + Y/(x t) = 2/x`: `Y = t` (and the homogeneous solution `1/t`); denominator `t`.
#guard hasCoeff (primSysC Fc ks 0 ic lim0 1 (fun _ _ ↦ [ic]) [[], one0] [one0]
  [fun _ ↦ [two_x]]) [1]
-- The coupled system `Y₁′ + Y₂/(x t) = 1/x`, `Y₂′ = 1/x`: `(Y₁, Y₂) = (0, t)`.
#guard hasCoeff (primSysC Fc ks 0 ic lim0 2 (fun i j ↦ if i.1 = 0 ∧ j.1 = 1 then [ic] else [])
  [[], one0] [one0] [fun _ ↦ [ic]]) [1]

end Curves.MT.SysEx
