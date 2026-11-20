import RischTragerBronstein.Mixed.KZMain

/-!
# Examples: poles at the roots of `e²ˣ + 1`

`kzDecide` over the tower `x`, `t = e²ˣ`, with `N = ℚ(i) = ℚ[X]/(X² + 1)` (`Φ₄`, `ζ₂ = −1`) and
the poles `±i` of `1/(t² + 1)`; each answer is correct by `kzDecide_correct` (the `Fact`s that
`Φ₄` stays irreducible over the code fields are `liftQ_irr_linear`).
-/

namespace Curves.MT.KZEx

open Curves Curves.LT Curves.MT CPoly

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
abbrev M4 : CPoly ℚ := cycloQ 4

lemma M4_irr (m : ℕ) : Irreducible (toPoly (liftQ Fc m M4)) :=
  liftQ_irr_linear [0, -1] M4
    (by rw [cycloQ_spec 4 (by norm_num)]; exact Polynomial.cyclotomic.monic 4 ℚ)
    (by rw [cycloQ_spec 4 (by norm_num)]; exact Polynomial.cyclotomic.irreducible_rat (by norm_num)) m

instance i0 : Fact (Irreducible (toPoly (liftQ Fc 0 M4))) := ⟨M4_irr 0⟩
instance i1 : Fact (Irreducible (toPoly (liftQ Fc (0 + 1) M4))) := ⟨M4_irr 1⟩

def x2 : GPoly (GFrac ℚ) := [([0, 2], [1])]
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def c0 : GPoly (GFrac ℚ) := []
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def c34 : GPoly (GFrac ℚ) := [([3/4], [1])]
def b0 : GPoly (GFrac ℚ) := [([1, 1], [1])]

/-- The tower `t₀ = e²ˣ`. -/
def ks : (m : ℕ) → KindC m
  | 0 => .exp x2
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => x2
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def ps : List ℕ := [5, 13, 17, 29, 37, 41]

/-- The poles `±i`. -/
def ci : NFM Fc 0 M4 := NFK.mk _ [0, 1]
def cs : List (NFM Fc 0 M4) := [ci, -ci]
/-- `A = t + 3/4`: `A(±i) = (1 ± i/2)²`, so `γ = (1 ± i/2)/4`. -/
def Ac : GPoly (LC 0) := [c34, c1]
def gs : List (CPoly ℚ) := [[1/4, 1/8], [1/4, -1/8]]

-- `∫ √(e²ˣ + 3/4)/(e²ˣ + 1)` is elementary (about 80 s).
#guard kzDecide Fc ks lv 0 2 1 x2 M4 [-1] gs Ac [c1] 0 0 cs [c1, c0, c1] ps 30 (fun _ ↦ 2) =
  some true
-- `∫ x √(e²ˣ + 3/4)/(e²ˣ + 1)` is not (the residues are not constant).
#guard kzDecide Fc ks lv 0 2 1 x2 M4 [-1] gs Ac [xc] 0 0 cs [c1, c0, c1] ps 30 (fun _ ↦ 2) =
  some false
-- `∫ (1 + x(e⁴ˣ + 1)) √(e²ˣ + 3/4)/(e²ˣ + 1)` is not (same residues; the parametric equation has
-- no solution; about 80 s).
#guard kzDecide Fc ks lv 0 2 1 x2 M4 [-1] gs Ac [b0, c0, xc] 0 0 cs [c1, c0, c1] ps 30
  (fun _ ↦ 2) = some false

end Curves.MT.KZEx
