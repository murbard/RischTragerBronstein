import RischTragerBronstein.Algebraic.EllCubic

/-!
# `ellDecideCubic` at work: non-monic, non-integral cubics

* `∫ dx / √(4x³ − 4)` is not elementary;
* `∫ x² dx / (2 √(x³/3 + 1)) = √(x³/3 + 1)` is elementary.
-/

open Polynomial Differential

namespace EllAlgo.CubicExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma sq_4x3m4 : Squarefree (CPoly.toPoly ([-4, 0, 0, 4] : CPoly ℚ)) := by
  have h : CPoly.toPoly ([-4, 0, 0, 4] : CPoly ℚ) = C 4 * (X ^ 3 - 1 : ℚ[X]).comp (C 1 * X) := by
    simp [CPoly.toPoly]; ring
  rw [h]
  refine squarefree_scale _ 1 4 one_ne_zero (by norm_num) ?_
  refine Polynomial.Separable.squarefree ⟨-1, C (1 / 3 : ℚ) * X, ?_⟩
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero]
  have h3 : C (1 / 3 : ℚ) * C ((3 : ℕ) : ℚ) = 1 := by rw [← C_mul]; norm_num
  linear_combination X ^ 3 * h3

/-- **`∫ dx / √(4x³ − 4)` is not elementary.** -/
theorem ex_cubic_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = 4 * x ^ 3 - 4) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / y) := by
  have h := ellDecideCubic_spec hC hCall x y hx [-4, 0, 0, 4] sq_4x3m4
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [1] [1] 10 false (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([1] : CPoly ℚ)) / (aeval x (CPoly.toPoly ([1] : CPoly ℚ)) * y) =
      1 / y := by simp [CPoly.toPoly]
  rw [e] at h
  intro h'
  exact Bool.false_ne_true (h.mpr h')

end EllAlgo.CubicExample
