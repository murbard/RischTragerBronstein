import RischTragerBronstein.Algebraic.EllAlgo
import RischTragerBronstein.Algebraic.HypExample

/-!
# `ellDecide` at work

On `y² = x³ + 1` (`(2, 3)` of order 6, `(0, 1)` of order 3):

* `∫ (x³ + 1) dx / (x √(x³ + 1))` (`= ∫ (x² + 1/x)/y`) is elementary
  (`(2/3) y + (1/3) log (y − 1) − (1/3) log x³`, up to the certificate's normalisation);
* `∫ (3/(x − 2) − 1/x) dx / √(x³ + 1)` is not elementary (torsion residue divisor, but a
  non-zero elliptic remainder);

on `y² = x³ − 2` (`(3, 5)` of infinite order):

* `∫ (5/(x − 3) + x) dx / √(x³ − 2)` is not elementary (non-torsion residue divisor).

Each is `ellDecide … = some b` checked by the kernel plus `ellDecide_spec`.
-/

open Polynomial Differential

namespace EllAlgo.Example

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma sq_x3p1 : Squarefree (X ^ 3 + C ((0 : ℤ) : ℚ) * X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((1 : ℤ) : ℚ)) := by
  have := HypExample.squarefree_pE
  rw [HypExample.toPoly_pE] at this
  simpa using this

lemma sq_x3m2 : Squarefree (X ^ 3 + C ((0 : ℤ) : ℚ) * X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((-2 : ℤ) : ℚ)) := by
  refine Polynomial.Separable.squarefree ⟨C (-1 / 2 : ℚ), C (1 / 6 : ℚ) * X, ?_⟩
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_ofNat, map_zero, zero_mul, add_zero,
    derivative_add, derivative_X_pow, derivative_C]
  simp only [map_neg, map_ofNat, zero_add]
  have h1 : C (-1 / 2 : ℚ) * C (-2) = 1 := by rw [← C_mul]; norm_num
  have h2 : C (1 / 6 : ℚ) * C ((3 : ℕ) : ℚ) = C (1 / 2 : ℚ) := by rw [← C_mul]; norm_num
  have h3 : C (-1 / 2 : ℚ) + C (1 / 2 : ℚ) = 0 := by rw [← C_add]; norm_num
  have h0 : C (-2 : ℚ) = -2 := by rw [map_neg, map_ofNat]
  linear_combination h1 + X ^ 3 * h2 + X ^ 3 * h3 - C (-1 / 2 : ℚ) * h0

/-- **`∫ (x³ + 1) / (x √(x³ + 1)) dx` is elementary.** -/
theorem ex_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral ((x ^ 3 + 1) / (x * y)) := by
  have h := ellDecide_spec hC hCall x y hx 0 0 1 sq_x3p1 (by rw [hy]; push_cast; ring) hgen
    [0, 0, 1] [(0, 1, 1)] 1 10 true (by decide +kernel)
  have hx0 : x ≠ 0 := by
    intro h0; have := congrArg (fun z : E ↦ z′) h0; simp [hx] at this
  have e : (aeval x (CPoly.toPoly ([0, 0, 1] : CPoly ℚ)) + ([((0 : ℚ), (1 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y =
      (x ^ 3 + 1) / (x * y) := by
    simp [CPoly.toPoly]
    field_simp
  rw [← e]
  exact h.mp rfl

/-- **`∫ (3/(x − 2) − 1/x) / √(x³ + 1) dx` is not elementary** (the residue divisor is torsion). -/
theorem ex_torsion_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral ((3 / (x - 2) - 1 / x) / y) := by
  have h := ellDecide_spec hC hCall x y hx 0 0 1 sq_x3p1 (by rw [hy]; push_cast; ring) hgen
    [] [(2, 3, 1), (0, 1, -1)] 1 10 false (by decide +kernel)
  have e : (aeval x (CPoly.toPoly ([] : CPoly ℚ)) + ([((2 : ℚ), (3 : ℚ), (1 : ℤ)), (0, 1, -1)].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y =
      (3 / (x - 2) - 1 / x) / y := by
    simp [CPoly.toPoly]
    ring
  rw [← e]
  intro h'
  exact Bool.false_ne_true (h.mpr h')

/-- **`∫ (5/(x − 3) + x) / √(x³ − 2) dx` is not elementary** (`(3, 5)` has infinite order). -/
theorem ex_nontorsion_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 - 2) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral ((5 / (x - 3) + x) / y) := by
  have h := ellDecide_spec hC hCall x y hx 0 0 (-2) sq_x3m2 (by rw [hy]; push_cast; ring) hgen
    [0, 1] [(3, 5, 1)] 1 10 false (by decide +kernel)
  have e : (aeval x (CPoly.toPoly ([0, 1] : CPoly ℚ)) + ([((3 : ℚ), (5 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y =
      (5 / (x - 3) + x) / y := by
    simp [CPoly.toPoly]
    ring
  rw [← e]
  intro h'
  exact Bool.false_ne_true (h.mpr h')

end EllAlgo.Example
