import RischTragerBronstein.Algebraic.HypLog

/-!
# Hyperelliptic examples

In any differential field `E = Kc(x)(y)` with constants `Kc`, `x′ = 1`, `y² = x³ + 1`
(`y = √(x³ + 1)`, an elliptic curve):

* `∫ dx / √(x³ + 1)` and `∫ x dx / √(x³ + 1)` are **not** elementary (elliptic integrals);
* `∫ 3x² / (2√(x³ + 1)) dx = √(x³ + 1)` is: the algorithm answers yes.
-/

open Polynomial Differential

namespace Differential.HypExample

/-- `x³ + 1`. -/
def pE : CPoly ℚ := [1, 0, 0, 1]

lemma toPoly_pE : CPoly.toPoly pE = X ^ 3 + 1 := by
  simp [pE, CPoly.toPoly]; ring

lemma natDegree_pE : (CPoly.toPoly pE).natDegree = 3 := by
  rw [toPoly_pE]; compute_degree!

lemma squarefree_pE : Squarefree (CPoly.toPoly pE) := by
  rw [toPoly_pE]
  refine Polynomial.Separable.squarefree ?_
  refine ⟨1, -(C (1 / 3 : ℚ) * X), ?_⟩
  rw [derivative_add, derivative_X_pow, derivative_one, add_zero]
  have h3 : C (1 / 3 : ℚ) * C ((3 : ℕ) : ℚ) = 1 := by rw [← C_mul]; norm_num
  linear_combination (-(X ^ 3)) * h3

lemma odd_pE : Odd (CPoly.toPoly pE).natDegree := by rw [natDegree_pE]; decide

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / √(x³ + 1)` is not elementary.** -/
theorem elliptic_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / y) := by
  have hy' : y ^ 2 = aeval x (CPoly.toPoly pE) := by rw [toPoly_pE]; simp [hy]
  have := hyp_decides hC hCall x y hx pE squarefree_pE odd_pE hy' hgen [1]
  rw [show aeval x (CPoly.toPoly ([1] : CPoly ℚ)) = 1 by simp [CPoly.toPoly]] at this
  rw [this]
  decide +kernel

/-- **`∫ x dx / √(x³ + 1)` is not elementary.** -/
theorem elliptic_x_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (x / y) := by
  have hy' : y ^ 2 = aeval x (CPoly.toPoly pE) := by rw [toPoly_pE]; simp [hy]
  have := hyp_decides hC hCall x y hx pE squarefree_pE odd_pE hy' hgen [0, 1]
  rw [show aeval x (CPoly.toPoly ([0, 1] : CPoly ℚ)) = x by simp [CPoly.toPoly]] at this
  rw [this]
  decide +kernel

/-- `∫ 3x² / (2√(x³ + 1)) dx = √(x³ + 1)`: the algorithm answers yes. -/
theorem elliptic_deriv_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (3 / 2 * x ^ 2 / y) := by
  have hy' : y ^ 2 = aeval x (CPoly.toPoly pE) := by rw [toPoly_pE]; simp [hy]
  have := hyp_decides hC hCall x y hx pE squarefree_pE odd_pE hy' hgen [0, 0, 3 / 2]
  rw [show aeval x (CPoly.toPoly ([0, 0, 3 / 2] : CPoly ℚ)) = 3 / 2 * x ^ 2 by
    simp [CPoly.toPoly]; ring] at this
  rw [this]
  decide +kernel

end Differential.HypExample

namespace Differential.HypExample

open Polynomial

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- `∫ (x³ - 2) / (2x² √(x³ + 1)) dx = √(x³ + 1) / x`: the algorithm answers yes. -/
theorem elliptic_pole_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral ((x ^ 3 - 2) / (2 * x ^ 2 * y)) := by
  have hy' : y ^ 2 = aeval x (CPoly.toPoly pE) := by rw [toPoly_pE]; simp [hy]
  have hd : CPoly.hypCertDecide pE [-2, 0, 0, 1] [0, 0, 2] = some true := by decide +kernel
  obtain ⟨W, V, B0, hD, hV, hid, hdeg, hb⟩ := CPoly.hypCertDecide_spec _ _ _ _ hd
  have := hyp_decides_cert hC hCall x y hx pE squarefree_pE odd_pE hy' hgen _ _ _ _ _ hD hV hid hdeg
  rw [show aeval x (CPoly.toPoly ([-2, 0, 0, 1] : CPoly ℚ)) = x ^ 3 - 2 by
      simp [CPoly.toPoly]; ring,
    show aeval x (CPoly.toPoly ([0, 0, 2] : CPoly ℚ)) = 2 * x ^ 2 by simp [CPoly.toPoly]; ring]
    at this
  exact this.mpr (hb.mp rfl)

/-- **`∫ (x³ + 2x² - 2) / (2x² √(x³ + 1)) dx` is not elementary** (it is `√(x³ + 1)/x` plus the
elliptic integral `∫ dx / √(x³ + 1)`). -/
theorem elliptic_pole_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral ((x ^ 3 + 2 * x ^ 2 - 2) / (2 * x ^ 2 * y)) := by
  have hy' : y ^ 2 = aeval x (CPoly.toPoly pE) := by rw [toPoly_pE]; simp [hy]
  have hd : CPoly.hypCertDecide pE [-2, 0, 2, 1] [0, 0, 2] = some false := by decide +kernel
  obtain ⟨W, V, B0, hD, hV, hid, hdeg, hb⟩ := CPoly.hypCertDecide_spec _ _ _ _ hd
  have := hyp_decides_cert hC hCall x y hx pE squarefree_pE odd_pE hy' hgen _ _ _ _ _ hD hV hid hdeg
  rw [show aeval x (CPoly.toPoly ([-2, 0, 2, 1] : CPoly ℚ)) = x ^ 3 + 2 * x ^ 2 - 2 by
      simp [CPoly.toPoly]; ring,
    show aeval x (CPoly.toPoly ([0, 0, 2] : CPoly ℚ)) = 2 * x ^ 2 by simp [CPoly.toPoly]; ring]
    at this
  rw [this]
  intro h0
  exact Bool.false_ne_true (hb.mpr h0)

end Differential.HypExample

namespace Differential.HypExample

open Polynomial

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / (x √(x³ + 1)) = (1/3) log ((√(x³+1) - 1)² / x³)`** — an elliptic integrand with a
genuine logarithmic part (the divisor `(0, 1) - (0, -1)` is `3`-torsion), certified. -/
theorem elliptic_log_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) : HasElementaryIntegral (1 / (x * y)) := by
  have hy' : y ^ 2 = aeval x (X ^ 3 + 1 : ℚ[X]) := by simp [hy]
  have := hyp_log_cert hC x y hx (X ^ 3 + 1) (by
      intro h; have := congrArg natDegree h; simp at this) hy' 1 X 0 1 (X ^ 3 + 2) (-2) (X ^ 3) 3
    X_ne_zero one_ne_zero (pow_ne_zero _ X_ne_zero) (by norm_num)
    (by
      intro h
      have h' : ((X ^ 3 + 2) ^ 2 - (-2) ^ 2 * (X ^ 3 + 1) : ℚ[X]) = X ^ 6 := by ring
      rw [h'] at h; exact pow_ne_zero _ X_ne_zero h)
    (by
      have h' : ((X ^ 3 + 2) ^ 2 - (-2) ^ 2 * (X ^ 3 + 1) : ℚ[X]) = X ^ 6 := by ring
      rw [h']; simp only [derivative_X_pow]; push_cast
      rw [show (C (6 : ℚ) : ℚ[X]) = 6 from map_ofNat C 6,
        show (C (3 : ℚ) : ℚ[X]) = 3 from map_ofNat C 3]
      ring)
    (by
      have h' : ((X ^ 3 + 2) ^ 2 - (-2) ^ 2 * (X ^ 3 + 1) : ℚ[X]) = X ^ 6 := by ring
      rw [h']
      simp only [derivative_zero, derivative_one, derivative_add, derivative_X_pow, derivative_neg,
        derivative_ofNat, map_ofNat]
      push_cast
      rw [show (C (3 : ℚ) : ℚ[X]) = 3 from map_ofNat C 3]
      ring)
  simpa using this

end Differential.HypExample
