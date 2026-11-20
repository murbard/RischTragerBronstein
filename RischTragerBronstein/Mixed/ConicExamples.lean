import RischTragerBronstein.Mixed.MTFinal
import RischTragerBronstein.Mixed.ExpCurveDecide

/-!
# Examples: a tower over a conic without a rational point

The base curve `y² = −x² − 1` has no rational point (so the genus-`0` reduction by a rational
parametrisation, `genus0_pt_decides`, does not apply), but it is an ordinary curve over `ℚ` for the
mixed-tower decision: `elM_sound` (any constants) makes the answers below, computed at bound `3`,
correct.
-/

namespace Curves.MT.ConicEx

open Curves Curves.LT Curves.MT CPoly

def Fc : Sup.BPoly ℚ := [[1, 0, 1], [], [1]]
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def xi : GPoly (GFrac ℚ) := [([1], [0, 1])]
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def yinv : GPoly (GFrac ℚ) := [([], [1]), ([-1], [1, 0, 1])]
def xyinv : GPoly (GFrac ℚ) := [([], [1]), ([0, -1], [1, 0, 1])]
def ks : (m : ℕ) → KindC m
  | 0 => .prim xi
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def q1 : LC 1 := (([[], yinv] : GPoly (LC 0)), ([c1] : GPoly (LC 0)))
def q2 : LC 1 := (([[], xyinv] : GPoly (LC 0)), ([c1] : GPoly (LC 0)))
#guard curveShape Fc = true
#guard certC Fc ks lv 1 = true
-- `∫ log x/√(−x² − 1)` is not elementary.
#guard elM Fc ks lv 1 q1 3 = some false
-- `∫ x log x/√(−x² − 1)` is elementary.
#guard elM Fc ks lv 1 q2 3 = some true

end Curves.MT.ConicEx
