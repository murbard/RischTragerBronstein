import RischTragerBronstein.Algebraic.EllQuarticPt

/-!
# Quartics without rational roots: `√(x⁴ + 1)`

* `∫ dx / √(x⁴ + 1)` is **not** elementary;
* `∫ x dx / √(x⁴ + 1)` is elementary (`= ½ asinh x²`);
* `∫ dx / (x √(x⁴ + 1))` is elementary;
* `∫ dx / √(2x⁴ + 1)` is **not** elementary (leading coefficient not a square: through the
  rational point `(0, 1)`), `∫ x dx / √(2x⁴ + 1)` is.
-/

open Polynomial Differential

namespace EllAlgo.QuarticSqExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / √(x⁴ + 1)` is not elementary.** -/
theorem ex_x4p1_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 4 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / y) := by
  have h := ellDecideQuarticSq_spec hC hCall x y hx [1, 0, 0, 0, 1]
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [1] [1] 30 false (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([1] : CPoly ℚ)) / (aeval x (CPoly.toPoly ([1] : CPoly ℚ)) * y) =
      1 / y := by simp [CPoly.toPoly]
  rw [e] at h
  intro h'
  exact Bool.false_ne_true (h.mpr h')

/-- **`∫ x dx / √(x⁴ + 1)` is elementary.** -/
theorem ex_x4p1_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 4 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (x / y) := by
  have h := ellDecideQuarticSq_spec hC hCall x y hx [1, 0, 0, 0, 1]
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [0, 1] [1] 30 true (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([0, 1] : CPoly ℚ)) /
      (aeval x (CPoly.toPoly ([1] : CPoly ℚ)) * y) = x / y := by simp [CPoly.toPoly]
  rw [e] at h
  exact h.mp rfl

/-- **`∫ dx / (x √(x⁴ + 1))` is elementary.** -/
theorem ex_x4p1_elementary' (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 4 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (1 / (x * y)) := by
  have h := ellDecideQuarticSq_spec hC hCall x y hx [1, 0, 0, 0, 1]
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [1] [0, 1] 30 true (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([1] : CPoly ℚ)) /
      (aeval x (CPoly.toPoly ([0, 1] : CPoly ℚ)) * y) = 1 / (x * y) := by simp [CPoly.toPoly]
  rw [e] at h
  exact h.mp rfl

/-- **`∫ dx / √(2x⁴ + 1)` is not elementary.** -/
theorem ex_2x4p1_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = 2 * x ^ 4 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / y) := by
  have h := ellDecideQuarticPt_spec hC hCall x y hx [1, 0, 0, 0, 2] 0
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [1] [1] 30 false (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([1] : CPoly ℚ)) / (aeval x (CPoly.toPoly ([1] : CPoly ℚ)) * y) =
      1 / y := by simp [CPoly.toPoly]
  rw [e] at h
  intro h'
  exact Bool.false_ne_true (h.mpr h')

/-- **`∫ x dx / √(2x⁴ + 1)` is elementary.** -/
theorem ex_2x4p1_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = 2 * x ^ 4 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (x / y) := by
  have h := ellDecideQuarticPt_spec hC hCall x y hx [1, 0, 0, 0, 2] 0
    (by rw [hy]; simp [CPoly.toPoly]; ring) hgen [0, 1] [1] 30 true (by decide +kernel)
  have e : aeval x (CPoly.toPoly ([0, 1] : CPoly ℚ)) /
      (aeval x (CPoly.toPoly ([1] : CPoly ℚ)) * y) = x / y := by simp [CPoly.toPoly]
  rw [e] at h
  exact h.mp rfl

end EllAlgo.QuarticSqExample
