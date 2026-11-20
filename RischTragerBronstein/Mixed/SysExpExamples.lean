import RischTragerBronstein.Mixed.SysExp
import RischTragerBronstein.Mixed.MTAlg
import RischTragerBronstein.Mixed.SysPrimExamples

/-!
# Examples: coupled Risch systems at an exponential level

Tower `x`, `t = eˣ`. Outputs `(e, W)` give the solutions `W / Den` (`expSysC_sound`); every
rational solution is a constant combination of them (`expSysC_complete`).
-/

namespace Curves.MT.SysExpEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def one0 : GPoly (GFrac ℚ) := [([1], [1])]
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def rde0 : LC 0 → List (LC 0) → List (List ℚ × LC 0) := fun c ws ↦ prdeC Fc ks lv 0 ⟨c, []⟩ ws

-- `Y′ = eˣ`: `Y = eˣ`.
#guard SysEx.hasCoeff (expSysC Fc ks 0 xc rde0 1 (fun _ _ ↦ []) [one0] [one0]
  [fun _ ↦ [[], one0]]) [1]
-- `Y₁′ + t/((t+1)(t+2)) Y₂ = t/(t+1)`, `Y₂′ = t`: `(Y₁, Y₂) = (0, t + 2)`, denominator
-- `(t+1)²(t+2)`; the only other rational solution is the constant `(1, 0)`.
#guard SysEx.hasCoeff (expSysC Fc ks 0 xc rde0 2
  (fun i j ↦ if i.1 = 0 ∧ j.1 = 1 then [[], one0] else [])
  [[([2], [1])], [([3], [1])], one0] [one0, one0]
  [fun i ↦ if i.1 = 0 then [[], one0] else [[], one0, one0]]) [1]

end Curves.MT.SysExpEx
