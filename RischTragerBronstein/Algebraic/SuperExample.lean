import RischTragerBronstein.Algebraic.SuperHerm

/-!
# Superelliptic examples

In any differential field `E = Kc(x)(y)` with constants `Kc`, `x′ = 1` and `y³ = x² + 1`
(`y = ∛(x² + 1)`, a curve of genus 1):

* `∫ dx / ∛(x² + 1) = ∫ y² / (x² + 1) dx` is **not** elementary;
* `∫ ∛(x² + 1) dx = ∫ (x² + 1) y / (x² + 1) dx` is **not** elementary;
* `∫ x dx / ∛(x² + 1)` **is** elementary (it is `(3/4) ∛(x² + 1)²`);
* `∫ dx / (x² + 1)^{4/3} = ∫ y² / (x² + 1)² dx` is **not** elementary, while
  `∫ x dx / (x² + 1)^{4/3}` is (Hermite step on the power of `p`, `super_decides_pow`).
-/

open Polynomial Differential CPoly IntermediateField

namespace Differential.SuperExample

/-- `x² + 1`. -/
def pE : CPoly ℚ := [1, 0, 1]

lemma toPoly_pE : CPoly.toPoly pE = X ^ 2 + 1 := by
  simp [pE, CPoly.toPoly]; ring

lemma natDegree_pE : (CPoly.toPoly pE).natDegree = 2 := by
  rw [toPoly_pE]; compute_degree!

lemma squarefree_pE : Squarefree (CPoly.toPoly pE) := by
  rw [toPoly_pE]
  refine Polynomial.Separable.squarefree ?_
  refine ⟨1, -(C (1 / 2 : ℚ) * X), ?_⟩
  rw [derivative_add, derivative_X_pow, derivative_one, add_zero]
  have h2 : C (1 / 2 : ℚ) * C ((2 : ℕ) : ℚ) = 1 := by rw [← C_mul]; norm_num
  linear_combination (-(X ^ 2)) * h2

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma hy' {x y : E} (hy : y ^ 3 = x ^ 2 + 1) :
    y ^ 3 = aeval x ((CPoly.toPoly pE).map (algebraMap ℚ Kc)) := by
  rw [toPoly_pE]; simp [hy]

/-- **`∫ dx / ∛(x² + 1)` is not elementary.** -/
theorem cbrt_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 2 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    ¬HasElementaryIntegral (y ^ 2 / (x ^ 2 + 1)) := by
  have := super_decides hC hCall x y hx (algebraMap ℚ Kc) 3 pE squarefree_pE
    (by rw [natDegree_pE]; norm_num) (by rw [natDegree_pE]; decide) (hy' hy) hgen 2
    (by norm_num) (by norm_num) [1]
  rw [show aeval x ((CPoly.toPoly ([1] : CPoly ℚ)).map (algebraMap ℚ Kc)) = 1 by
    simp [CPoly.toPoly], toPoly_pE, one_mul] at this
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_add, map_pow, aeval_X, map_one] at this
  rw [this]
  decide +kernel

/-- **`∫ ∛(x² + 1) dx` is not elementary.** -/
theorem cbrt_self_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 2 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    ¬HasElementaryIntegral y := by
  have := super_decides hC hCall x y hx (algebraMap ℚ Kc) 3 pE squarefree_pE
    (by rw [natDegree_pE]; norm_num) (by rw [natDegree_pE]; decide) (hy' hy) hgen 1
    (by norm_num) (by norm_num) pE
  have hp0 : x ^ 2 + 1 ≠ 0 := by
    have htr : Transcendental Kc x :=
      transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
    intro h
    exact htr ⟨X ^ 2 + 1, by
      intro h0
      have := congrArg (fun P : Kc[X] ↦ P.coeff 0) h0
      simp at this, by simpa using h⟩
  rw [toPoly_pE] at this
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_add, map_pow, aeval_X, map_one, pow_one] at this
  rw [mul_div_cancel_left₀ _ hp0] at this
  rw [this]
  decide +kernel

/-- `∫ x dx / ∛(x² + 1)` is elementary: the algorithm answers yes. -/
theorem x_cbrt_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 2 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    HasElementaryIntegral (x * y ^ 2 / (x ^ 2 + 1)) := by
  have := super_decides hC hCall x y hx (algebraMap ℚ Kc) 3 pE squarefree_pE
    (by rw [natDegree_pE]; norm_num) (by rw [natDegree_pE]; decide) (hy' hy) hgen 2
    (by norm_num) (by norm_num) [0, 1]
  rw [show aeval x ((CPoly.toPoly ([0, 1] : CPoly ℚ)).map (algebraMap ℚ Kc)) = x by
    simp [CPoly.toPoly], toPoly_pE] at this
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_add, map_pow, aeval_X, map_one] at this
  rw [this]
  decide +kernel

/-- **`∫ dx / (x² + 1)^{4/3}` is not elementary.** -/
theorem cbrt_pow_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 2 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    ¬HasElementaryIntegral (y ^ 2 / (x ^ 2 + 1) ^ 2) := by
  have := super_decides_pow hC hCall x y hx (algebraMap ℚ Kc) 3 pE squarefree_pE
    (by rw [natDegree_pE]; norm_num) (by rw [natDegree_pE]; decide) (hy' hy) hgen 2
    (by norm_num) (by norm_num) 2 (by norm_num) [1]
  rw [show aeval x ((CPoly.toPoly ([1] : CPoly ℚ)).map (algebraMap ℚ Kc)) = 1 by
    simp [CPoly.toPoly], toPoly_pE, one_mul] at this
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_add, map_pow, aeval_X, map_one] at this
  rw [this]
  decide +kernel

/-- `∫ x dx / (x² + 1)^{4/3}` is elementary: the algorithm answers yes. -/
theorem x_cbrt_pow_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 2 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    HasElementaryIntegral (x * y ^ 2 / (x ^ 2 + 1) ^ 2) := by
  have := super_decides_pow hC hCall x y hx (algebraMap ℚ Kc) 3 pE squarefree_pE
    (by rw [natDegree_pE]; norm_num) (by rw [natDegree_pE]; decide) (hy' hy) hgen 2
    (by norm_num) (by norm_num) 2 (by norm_num) [0, 1]
  rw [show aeval x ((CPoly.toPoly ([0, 1] : CPoly ℚ)).map (algebraMap ℚ Kc)) = x by
    simp [CPoly.toPoly], toPoly_pE] at this
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_add, map_pow, aeval_X, map_one] at this
  rw [this]
  decide +kernel

end Differential.SuperExample
