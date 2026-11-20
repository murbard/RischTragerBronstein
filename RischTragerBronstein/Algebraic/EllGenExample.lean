import RischTragerBronstein.Algebraic.EllGen
import RischTragerBronstein.Algebraic.EllAlgoExample

/-!
# `ellDecideGen` at work: double poles

On `y² = x³ + 1`:

* `∫ (x³ − 6x² − 2) dx / (2 (x − 2)² √(x³ + 1)) = √(x³ + 1) / (x − 2)` is elementary;
* `∫ dx / ((x − 2)² √(x³ + 1))` is not elementary.
-/

open Polynomial Differential

namespace EllAlgo.GenExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ (x³ − 6x² − 2) / (2 (x − 2)² √(x³ + 1)) dx` is elementary.** -/
theorem ex_double_pole_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral ((x ^ 3 - 6 * x ^ 2 - 2) / ((2 * x ^ 2 - 8 * x + 8) * y)) := by
  have h := ellDecideGen_spec hC hCall x y hx 0 0 1 Example.sq_x3p1 (by rw [hy]; push_cast; ring)
    hgen [-2, 0, -6, 1] [8, -8, 2] 10 true (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([-2, 0, -6, 1] : CPoly ℚ)) /
      (aeval x (CPoly.toPoly ([8, -8, 2] : CPoly ℚ)) * y) =
      (x ^ 3 - 6 * x ^ 2 - 2) / ((2 * x ^ 2 - 8 * x + 8) * y) := by
    simp [CPoly.toPoly]; ring
  rw [← e]
  exact h.mp rfl

/-- **`∫ dx / ((x − 2)² √(x³ + 1))` is not elementary.** -/
theorem ex_double_pole_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / ((x ^ 2 - 4 * x + 4) * y)) := by
  have h := ellDecideGen_spec hC hCall x y hx 0 0 1 Example.sq_x3p1 (by rw [hy]; push_cast; ring)
    hgen [1] [4, -4, 1] 10 false (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([1] : CPoly ℚ)) /
      (aeval x (CPoly.toPoly ([4, -4, 1] : CPoly ℚ)) * y) = 1 / ((x ^ 2 - 4 * x + 4) * y) := by
    simp only [CPoly.toPoly, map_add, map_mul, map_neg, aeval_C, aeval_X, map_one, map_zero,
      mul_zero, add_zero, eq_ratCast]
    push_cast
    ring_nf
  rw [← e]
  intro h'
  exact Bool.false_ne_true (h.mpr h')

end EllAlgo.GenExample
