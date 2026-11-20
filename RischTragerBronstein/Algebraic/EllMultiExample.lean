import RischTragerBronstein.Algebraic.EllGenMultiComplete
import RischTragerBronstein.Algebraic.EllTwistExample

/-!
# The elliptic algorithm with residues in three quadratic classes

`∫ dx / ((x³ + 3x² − 4x) √(x³ + 16))` is **not elementary**: the poles `x = 0, −4, 1` lie under
points in the classes of `16, −48, 17` (rational, `√−3`, `√17`); `ellDecideEll` groups them and
decides.
-/

open Polynomial Differential

namespace EllAlgo.MultiExample

open EllAlgo.TwistExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / ((x³ + 3x² − 4x) √(x³ + 16))` is not elementary.** -/
theorem ex_multi_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 16) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / ((x ^ 3 + 3 * x ^ 2 - 4 * x) * y)) := by
  have h := ellDecideEll_spec hC hCall x y hx 0 0 16 (sq_x3_add 16 (by norm_num))
    (by rw [hy]; push_cast; ring) hgen [1] [0, -4, 3, 1] 30 false (by decide +kernel)
  rw [show aeval x (CPoly.toPoly ([1] : CPoly ℚ)) = 1 by simp [CPoly.toPoly],
    show aeval x (CPoly.toPoly ([0, -4, 3, 1] : CPoly ℚ)) = x ^ 3 + 3 * x ^ 2 - 4 * x by
      simp [CPoly.toPoly]; ring] at h
  intro h'
  exact Bool.false_ne_true (h.mpr h')

end EllAlgo.MultiExample
