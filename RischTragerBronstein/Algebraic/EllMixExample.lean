import RischTragerBronstein.Algebraic.EllAlgoMix
import RischTragerBronstein.Algebraic.EllTwistExample

/-!
# `ellDecideMix` at work: residues in two quadratic classes

* `∫ (2 + 4/x − 12/(x + 4)) dx / √(x³ + 16)` is elementary: the residue point `(0, 4)` is
  rational of order 3, and `(−4, ±4√−3)` twists to `(12, 36)` on `Y² = X³ − 432`, of order 3;
  the certificate for the class `−3` leaves the polynomial remainder `−2`, cancelled by `B = 2`;
* `∫ (4/x − 12/(x + 4)) dx / √(x³ + 16)` is not (the remainder `−2/y` is an elliptic integral);
* `∫ (3/(x − 2) + 2/(x − 1)) dx / √(x³ + 1)` is not: `(1, ±√2)` twists to `(2, 4)` on
  `Y² = X³ + 8`, of infinite order.
-/

open Polynomial Differential

namespace EllAlgo.MixExample

open EllAlgo.TwistExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ (2 + 4/x − 12/(x + 4)) dx / √(x³ + 16)` is elementary.** -/
theorem ex_mix_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 16) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral ((2 + 4 / x - 12 / (x + 4)) / y) := by
  have h := ellDecideMix_spec hC hCall x y hx 0 0 16 (sq_x3_add 16 (by norm_num))
    (by rw [hy]; push_cast; ring) hgen 1 (-3) [2] [(0, 4, 1)] [(-4, 4, 1)] 1 20 true
    (by decide +kernel)
  have e : (aeval x (CPoly.toPoly ([2] : CPoly ℚ)) + ([((0 : ℚ), (4 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 * ((1 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum + ([((-4 : ℚ), (4 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 * ((-3 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum) / y = (2 + 4 / x - 12 / (x + 4)) / y := by
    simp [CPoly.toPoly]; ring
  rw [← e]
  exact h.mp rfl

/-- **`∫ (4/x − 12/(x + 4)) dx / √(x³ + 16)` is not elementary.** -/
theorem ex_mix_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 16) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral ((4 / x - 12 / (x + 4)) / y) := by
  have h := ellDecideMix_spec hC hCall x y hx 0 0 16 (sq_x3_add 16 (by norm_num))
    (by rw [hy]; push_cast; ring) hgen 1 (-3) [] [(0, 4, 1)] [(-4, 4, 1)] 1 20 false
    (by decide +kernel)
  have e : (aeval x (CPoly.toPoly ([] : CPoly ℚ)) + ([((0 : ℚ), (4 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 * ((1 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum + ([((-4 : ℚ), (4 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 * ((-3 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum) / y = (4 / x - 12 / (x + 4)) / y := by
    simp [CPoly.toPoly]; ring
  rw [← e]
  intro h'
  exact Bool.false_ne_true (h.mpr h')

/-- **`∫ (3/(x − 2) + 2/(x − 1)) dx / √(x³ + 1)` is not elementary.** -/
theorem ex_mix_not_elementary' (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral ((3 / (x - 2) + 2 / (x - 1)) / y) := by
  have h := ellDecideMix_spec hC hCall x y hx 0 0 1 (sq_x3_add 1 (by norm_num))
    (by rw [hy]; push_cast; ring) hgen 1 2 [] [(2, 3, 1)] [(1, 1, 1)] 1 20 false
    (by decide +kernel)
  have e : (aeval x (CPoly.toPoly ([] : CPoly ℚ)) + ([((2 : ℚ), (3 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 * ((1 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum + ([((1 : ℚ), (1 : ℚ), (1 : ℤ))].map
      fun q : ℚ × ℚ × ℤ ↦ (((q.2.2 : ℚ) / (1 : ℕ) * q.2.1 * ((2 : ℤ) : ℚ) : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum) / y = (3 / (x - 2) + 2 / (x - 1)) / y := by
    simp [CPoly.toPoly]
  rw [← e]
  intro h'
  exact Bool.false_ne_true (h.mpr h')

end EllAlgo.MixExample
