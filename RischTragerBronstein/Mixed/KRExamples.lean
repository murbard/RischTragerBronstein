import RischTragerBronstein.Mixed.KRMain
import RischTragerBronstein.Mixed.KRIrr

/-!
# Examples: radicals of order `n > 2` over an exponential

`krDecide` over the tower `x`, `t = eˣ`; each answer is correct by `krDecide_correct` (the
`Fact` that `Φ₃` is irreducible over the code field is `cycK_irr_linear`).
-/

namespace Curves.MT.KREx

open Curves Curves.LT Curves.MT CPoly

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
instance : Fact (Irreducible (toPoly (cycK Fc 0 3))) := ⟨cycK_irr_linear [0, -1] 0 3 (by norm_num)⟩
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def c0 : GPoly (GFrac ℚ) := []
def c1 : GPoly (GFrac ℚ) := [([1], [1])]

/-- The tower `t₀ = eˣ`. -/
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def ps : List ℕ := [7, 13, 19, 31, 37, 43]

-- `∫ ∛(x + eˣ)` is not elementary (`A(0) = x` has no cube root in `ℚ(x)`: the Risch equation).
#guard krDecide Fc ks lv 0 3 1 [xc, c1] [c1] 0 0 ps 30 (fun _ ↦ 2) = some false
-- `∫ ∛(1 + eˣ)` is elementary (`Ψ` torsion on `ỹ³ = 1 + t`: witness over `ℚ(x)(ζ₃)`, its norm,
-- the column, the parametric Risch equation; about 2.5 minutes).
#guard krDecide Fc ks lv 0 3 1 [c1, c1] [c1] 0 0 ps 30 (fun _ ↦ 2) = some true
-- `∫ x ∛(1 + eˣ)` is not elementary (same torsion witness; the parametric equation with the
-- column has no solution; about 2.5 minutes).
#guard krDecide Fc ks lv 0 3 1 [c1, c1] [xc] 0 0 ps 30 (fun _ ↦ 2) = some false

end Curves.MT.KREx
