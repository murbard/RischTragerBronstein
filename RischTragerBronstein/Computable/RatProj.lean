import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Order.Field.Rat

/-!
# Orthogonal projections over `ℚ`

For rational vectors `k₁, …, k_p ∈ ℚʳ`, every `w ∈ ℚʳ` splits as `w = w′ + ∑ aₜ kₜ` with `w′`
orthogonal (for the dot product) to every `kₜ` (`rat_proj`): the dot product restricted to the span
is nondegenerate (a sum of squares vanishes only at `0`), so the span and its orthogonal are
complementary (`isCompl_orthogonal_of_restrict_nondegenerate`).
-/

open LinearMap

/-- **The orthogonal decomposition over `ℚ`.** -/
theorem rat_proj (Kr : List (List ℚ)) (r : ℕ) (w : Fin r → ℚ) :
    ∃ (a : ℕ → ℚ) (w' : Fin r → ℚ), (∀ j : Fin r, w j = w' j + ∑ t ∈ Finset.range Kr.length,
      a t * (Kr.getD t []).getD j 0) ∧
      ∀ t < Kr.length, ∑ j : Fin r, (Kr.getD t []).getD j 0 * w' j = 0 := by
  classical
  set v : Fin Kr.length → Fin r → ℚ := fun t j ↦ (Kr.getD t []).getD j 0 with hv
  set B : LinearMap.BilinForm ℚ (Fin r → ℚ) := Matrix.toBilin' 1 with hB
  have hBapp : ∀ x y : Fin r → ℚ, B x y = ∑ j, x j * y j := fun x y ↦ by
    rw [hB, Matrix.toBilin'_apply']
    simp [dotProduct, Matrix.mulVec, Matrix.one_apply]
  set W : Submodule ℚ (Fin r → ℚ) := Submodule.span ℚ (Set.range v) with hW
  have hrefl : B.IsRefl := fun x y h ↦ by rw [hBapp] at h ⊢; rw [← h]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hsq : ∀ x : W, (∀ y : W, B x y = 0) → x = 0 := by
    intro x hx
    have h0 := hx x
    rw [hBapp] at h0
    have hj : ∀ j, (x : Fin r → ℚ) j = 0 := by
      intro j
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ (x : Fin r → ℚ) i * (x : Fin r → ℚ) i := fun i _ ↦
        mul_self_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 j (Finset.mem_univ j)
      exact mul_self_eq_zero.mp this
    exact Subtype.ext (funext hj)
  have hnd : (B.restrict W).Nondegenerate := by
    refine ⟨fun x hx ↦ hsq x fun y ↦ ?_, fun y hy ↦ hsq y fun x ↦ ?_⟩
    · exact hx y
    · have := hy x
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at this ⊢
      rw [hBapp] at this ⊢
      rw [← this]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hcompl := BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  have hw : w ∈ W ⊔ B.orthogonal W := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨s, hs, w', hw', hsum⟩ := Submodule.mem_sup.mp hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hs
  refine ⟨fun t ↦ if h : t < Kr.length then c ⟨t, h⟩ else 0, w', fun j ↦ ?_, fun t ht ↦ ?_⟩
  · rw [← hsum, Pi.add_apply, ← hc, add_comm]
    congr 1
    rw [Finset.sum_apply, ← Fin.sum_univ_eq_sum_range (fun t ↦ (if h : t < Kr.length then
      c ⟨t, h⟩ else 0) * (Kr.getD t []).getD j 0)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp [hv, t.2]
  · have hvt : v ⟨t, ht⟩ ∈ W := Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw') _ hvt
    rw [hBapp] at this
    exact this
