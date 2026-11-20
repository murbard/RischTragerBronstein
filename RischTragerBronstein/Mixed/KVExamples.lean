import RischTragerBronstein.Mixed.KVMain
import RischTragerBronstein.Mixed.KYExamples

/-!
# Examples: radicals of order `n > 2` with ordinary poles over a logarithm

`kvDecide` over the tower `x`, `t = log x`, with the number field `N = ℚ(ζ₃) = ℚ[X]/(X² + X + 1)`
(`ζ = X`); each answer is correct by `kvDecide_correct`.
-/

namespace Curves.MT.KVEx

open Curves Curves.LT Curves.MT CPoly Curves.MT.KYEx

def xi : GPoly (GFrac ℚ) := [([1], [0, 1])]
def c0 : GPoly (GFrac ℚ) := []

/-- The tower `t₀ = log x`. -/
def ksL : (m : ℕ) → KindC m
  | 0 => .prim xi
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))

-- `∫ ∛(log x)/(log x − 1)` is not elementary: the residue at `log x = 1` is not constant.
#guard kvDecide Fc ksL lv 0 3 1 xi M3 [0, 1] [[1]] [c0, c1] [c1] 0 [c1] ps 30 (fun _ ↦ 2) =
  some false

-- `∫ ∛(log x)/(x (log x − 1))` is elementary (`∫ u^{1/3}/(u − 1) du` on the rational curve
-- `y³ = u`; the residue classes are torsion and the parametric equation has a solution).
#guard kvDecide Fc ksL lv 0 3 1 xi M3 [0, 1] [[1]] [c0, c1] [xi] 0 [c1] ps 30 (fun _ ↦ 2) =
  some true

end Curves.MT.KVEx
