import RischTragerBronstein.Mixed.EllCompute2

/-!
# A kernel-checked independence certificate

On `E : y² = x³ − x + t²` over `ℚ(t)`, the points `P = (0, t)` and `Q = (1, t)` are independent:
no relation `m P = n Q` with `(m, n) ≠ 0` (`indep_example`). The heights of `8P, 8Q, 8(P+Q)` are
computed by the executable group law (`addC`, `dblC`) and the certificate `certQ` at level `k = 3`
is checked by the kernel (`cert3`); `indep_of_certQ` turns it into the theorem.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight.Example

open scoped Classical

/-- `P = (0, t)` and `Q = (1, t)` as executable points. -/
def oP : PtC ℚ := some (([0], [1]), ([0, 1], [1]))
def oQ : PtC ℚ := some (([1], [1]), ([0, 1], [1]))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The certificate at level `3` (kernel-checked). -/
theorem cert3 : certQ [-1] 2 3 oP oQ = true := by decide +kernel

/-- `A = −1`, `B = t²`. -/
noncomputable abbrev A : ℚ[X] := -1
noncomputable abbrev B : ℚ[X] := X ^ 2

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

lemma ns_P : (shortW A B).toAffine.Nonsingular 0 (ι X) := by
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [shortW], Or.inl ?_⟩
  simp [shortW]

lemma ns_Q : (shortW A B).toAffine.Nonsingular 1 (ι X) := by
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [shortW], Or.inl ?_⟩
  simp [shortW]; norm_num

/-- The points `P = (0, t)`, `Q = (1, t)`. -/
noncomputable def P : (shortW A B).toAffine.Point := Point.some _ _ ns_P
noncomputable def Q : (shortW A B).toAffine.Point := Point.some _ _ ns_Q

lemma rel_P : Rel A B oP P := by
  refine ⟨by simp [Fr.ok, CPoly.toPoly], by simp [Fr.ok, CPoly.toPoly], ?_, ?_⟩ <;>
    simp [Fr.val, CPoly.toPoly]

lemma rel_Q : Rel A B oQ Q := by
  refine ⟨by simp [Fr.ok, CPoly.toPoly], by simp [Fr.ok, CPoly.toPoly], ?_, ?_⟩ <;>
    simp [Fr.val, CPoly.toPoly]

lemma hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp at this

lemma hD : max A.natDegree B.natDegree = 2 := by simp [A, B]

/-- **`(0, t)` and `(1, t)` are independent on `y² = x³ − x + t²`.** -/
theorem indep_example (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 :=
  indep_of_certQ [-1] [0, 0, 1] A B (by simp [A, CPoly.toPoly]) hΔ 3 oP oQ P Q rel_P rel_Q
    (by rw [hD]; exact cert3) m n hrel

end FFHeight.Example
