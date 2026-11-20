import RischTragerBronstein.Algebraic.EllAlgoTw

/-!
# `ellDecideTw` at work: residues at points with irrational `y`

* `∫ 2 dx / (x √(x³ + 2))` is elementary: the residue points `(0, ±√2)` twist to `(0, 4)` on `Y² = X³ + 16`, of order 3;
* `∫ dx / ((x − 2) √(x³ − 1))` is not elementary: `(2, ±√7)` twists
  to `(14, 49)` on `Y² = X³ − 343`, of infinite order.
-/

open Polynomial Differential

namespace EllAlgo.TwistExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- `x³ + c` (`c ≠ 0`) is squarefree. -/
lemma sq_x3_add (c : ℤ) (hc : c ≠ 0) :
    Squarefree (X ^ 3 + C ((0 : ℤ) : ℚ) * X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((c : ℤ) : ℚ)) := by
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  refine Polynomial.Separable.squarefree ⟨C (1 / (c : ℚ)), C (-1 / (3 * (c : ℚ))) * X, ?_⟩
  simp only [Int.cast_zero, map_zero, zero_mul, add_zero, derivative_add, derivative_X_pow,
    derivative_C]
  have h1 : C (1 / (c : ℚ)) * C (c : ℚ) = 1 := by rw [← C_mul, one_div_mul_cancel hcq, C_1]
  have h2 : C (-1 / (3 * (c : ℚ))) * C ((3 : ℕ) : ℚ) = -C (1 / (c : ℚ)) := by
    rw [← C_mul, ← C_neg]; congr 1; field_simp; norm_num
  linear_combination h1 + X ^ 3 * h2

/-- **`∫ 2 dx / (x √(x³ + 2))` is elementary.** -/
theorem ex_twist_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (2 / (x * y)) := by
  have h := ellDecideTw_spec hC hCall x y hx 0 0 2 (sq_x3_add 2 (by norm_num))
    (by rw [hy]; push_cast; ring) hgen 2 [] [(0, 1, 1)] 1 20 true
    (by decide +kernel)
  have e : (aeval x (CPoly.toPoly ([] : CPoly ℚ)) + ([((0 : ℚ), (1 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 * ((2 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum) / y = 2 / (x * y) := by
    simp [CPoly.toPoly]; ring
  rw [← e]
  exact h.mp rfl

/-- **`∫ dx / ((x − 2) √(x³ − 1))` is not elementary.** -/
theorem ex_twist_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 - 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / ((x - 2) * y)) := by
  have h := ellDecideTw_spec hC hCall x y hx 0 0 (-1) (sq_x3_add (-1) (by norm_num))
    (by rw [hy]; push_cast; ring) hgen 7 [] [(2, 1, 1)] 7 20 false
    (by decide +kernel)
  have e : (aeval x (CPoly.toPoly ([] : CPoly ℚ)) + ([((2 : ℚ), (1 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (7 : ℕ) * q.2.1 * ((7 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum) / y = 1 / ((x - 2) * y) := by
    simp [CPoly.toPoly]; ring
  rw [← e]
  intro h'
  exact Bool.false_ne_true (h.mpr h')

end EllAlgo.TwistExample
