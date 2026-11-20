import RischTragerBronstein.Mixed.KXMWExample
import RischTragerBronstein.Mixed.KXDepMain

/-!
# Examples: dependent classes in the Mordell–Weil exception (`kxDecideD`)

On `y² = t³ − t + 1` (`t = eˣ`) the pole point `(1, 1)` and `P₊ = (0, 1)` are dependent, so
neither `kxDecide` nor the independence certificates answer; `kxDecideD` finds the relation and
its witness, and decides by the parametric Risch equation. Each answer is correct by
`kxDecideD_correct`.
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly

/-- `t³ − t + 1`. -/
def Adep : GPoly (LC 0) := [[([1], [1])], cm1, c0, c1]
/-- `(t² + 3t − 1)/2`: `B θ/((t − 1) A)` is the logarithmic derivative column of the witness. -/
def Bdep : GPoly (LC 0) := [[([-1/2], [1])], [([3/2], [1])], [([1/2], [1])]]
/-- `t² + (3/2) t − 1/2`. -/
def Bdep2 : GPoly (LC 0) := [[([-1/2], [1])], [([3/2], [1])], [([1], [1])]]

-- `∫ √(e³ˣ − eˣ + 1)/(eˣ − 1)`: not elementary.
#guard kxDecide Fc ks lv 0 xc Adep [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none
#guard kxDecideD Fc ks lv 0 xc Adep [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 4 = some false
-- `∫ (e²ˣ + 3eˣ − 1) √(e³ˣ − eˣ + 1) / (2 (eˣ − 1)(e³ˣ − eˣ + 1))`: elementary (a logarithm).
#guard kxDecide Fc ks lv 0 xc Adep Bdep 0 1 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none
#guard kxDecideD Fc ks lv 0 xc Adep Bdep 0 1 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 4 = some true
-- A perturbation: not elementary.
#guard kxDecideD Fc ks lv 0 xc Adep Bdep2 0 1 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 4 = some false

end Curves.MT.KXEx
