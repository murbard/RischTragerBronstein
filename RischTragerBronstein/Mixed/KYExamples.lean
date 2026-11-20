import RischTragerBronstein.Mixed.KYMain

/-!
# Examples: radicals of order `n > 2` with ordinary poles over an exponential

`kyDecide` over the tower `x`, `t = eˣ`, with the number field `N = ℚ(ζ₃) = ℚ[X]/(X² + X + 1)`
(`ζ = X`); each answer is correct by `kyDecide_correct` (the `Fact`s that `X² + X + 1` stays
irreducible over the code fields are `liftQ_irr_linear`).
-/

namespace Curves.MT.KYEx

open Curves Curves.LT Curves.MT CPoly

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
abbrev M3 : CPoly ℚ := [1, 1, 1]

lemma M3_poly : toPoly M3 = Polynomial.cyclotomic 3 ℚ := by
  rw [Polynomial.cyclotomic_three]; simp [toPoly_cons]; ring

lemma M3_irr (m : ℕ) : Irreducible (toPoly (liftQ Fc m M3)) :=
  liftQ_irr_linear [0, -1] M3 (by rw [M3_poly]; exact Polynomial.cyclotomic.monic 3 ℚ)
    (by rw [M3_poly]; exact Polynomial.cyclotomic.irreducible_rat (by norm_num)) m

instance i0 : Fact (Irreducible (toPoly (liftQ Fc 0 M3))) := ⟨M3_irr 0⟩
instance i1 : Fact (Irreducible (toPoly (liftQ Fc (0 + 1) M3))) := ⟨M3_irr 1⟩

def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def c7 : GPoly (GFrac ℚ) := [([7], [1])]

/-- The tower `t₀ = eˣ`. -/
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def ps : List ℕ := [7, 13, 19, 31, 37, 43]

-- `∫ ∛(1 + eˣ)/(eˣ − x)` is not elementary: the residue at `eˣ = x` is not constant.
#guard kyDecide Fc ks lv 0 3 1 xc M3 [0, 1] [[2]] [c1, c1] [c1] 0 0 [xc] ps 30 (fun _ ↦ 2) =
  some false

-- Not in the build (about 15 min and 4 GB each, run by `#eval`):
-- `∫ 7∛(1 + eˣ)/(eˣ − 7)` is elementary (`some true`; the residue class is torsion, and the
-- parametric equation has a solution):
--   kyDecide Fc ks lv 0 3 1 xc M3 [0, 1] [[2]] [c1, c1] [c7] 0 0 [c7] ps 30 (fun _ ↦ 2)
-- `∫ (7 + x(eˣ − 7)) ∛(1 + eˣ)/(eˣ − 7)` is not (`some false`; the same residue, plus
-- `x ∛(1 + eˣ)`):
--   kyDecide Fc ks lv 0 3 1 xc M3 [0, 1] [[2]] [c1, c1] [[([7, -7], [1])], xc] 0 0 [c7] ps 30
--     (fun _ ↦ 2)

end Curves.MT.KYEx
