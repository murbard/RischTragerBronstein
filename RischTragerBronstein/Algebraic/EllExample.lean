import RischTragerBronstein.Algebraic.EllDecide
import RischTragerBronstein.Elliptic.NLBound
import RischTragerBronstein.Algebraic.EllLog
import RischTragerBronstein.Algebraic.HypExample

/-!
# An elliptic integral with a logarithmic part that is not elementary

On `y² = x³ − 2` the rational point `P = (3, 5)` has infinite order: `2P = (129/100, −383/1000)`
is not integral (Nagell–Lutz, `EllNL.not_torsion_of`). The integrand `5 / ((x − 3) √(x³ − 2))` has
residues `±1` at `(3, ±5)`, so by `ell_torsion_of_elementary` an elementary antiderivative would
make `P` torsion: **`∫ 5 dx / ((x − 3) √(x³ − 2))` is not elementary.**
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Differential.EllExample

lemma ns35 : (EllNL.W 0 0 (-2)).toAffine.Nonsingular 3 5 := by
  rw [nonsingular_iff']
  refine ⟨(EllNL.equation_W 0 0 (-2)).mpr (by unfold EllNL.OnCurve; norm_num), ?_⟩
  right; simp [EllNL.W]

lemma ns2 : (EllNL.W 0 0 (-2)).toAffine.Nonsingular (129 / 100) (-383 / 1000) := by
  rw [nonsingular_iff']
  refine ⟨(EllNL.equation_W 0 0 (-2)).mpr (by unfold EllNL.OnCurve; norm_num), ?_⟩
  right; simp [EllNL.W]

/-- `(3, 5)` has infinite order on `y² = x³ − 2`. -/
lemma not_torsion_35 : ¬IsOfFinAddOrder (Point.some _ _ ns35 : (EllNL.W 0 0 (-2)).toAffine.Point) := by
  refine EllNL.not_torsion_of 0 0 (-2) 2 ns2 ?_ (Or.inl (by norm_num))
  rw [two_smul, Point.add_self_of_Y_ne (by rw [EllNL.negY_W]; norm_num)]
  simp only [Point.some.injEq]
  constructor
  · simp [addX, slope, EllNL.W]; norm_num
  · simp [addY, negAddY, addX, slope, negY, EllNL.W]; norm_num

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ 5 dx / ((x − 3) √(x³ − 2))` is not elementary.** -/
theorem elliptic_log_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 - 2) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (5 / ((x - 3) * y)) := by
  intro h
  have hsq : Squarefree (X ^ 3 + C ((0 : ℤ) : ℚ) * X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((-2 : ℤ) : ℚ)) := by
    refine Polynomial.Separable.squarefree ⟨C (-1 / 2 : ℚ), C (1 / 6 : ℚ) * X, ?_⟩
    simp only [Int.cast_zero, Int.cast_neg, Int.cast_ofNat, map_zero, zero_mul, add_zero,
      derivative_add, derivative_X_pow, derivative_C, derivative_mul, derivative_X]
    simp only [map_neg, map_ofNat, zero_mul, zero_add, mul_one]
    have h1 : C (-1 / 2 : ℚ) * C (-2) = 1 := by rw [← C_mul]; norm_num
    have h2 : C (1 / 6 : ℚ) * C ((3 : ℕ) : ℚ) = C (1 / 2 : ℚ) := by rw [← C_mul]; norm_num
    have h3 : C (-1 / 2 : ℚ) + C (1 / 2 : ℚ) = 0 := by rw [← C_add]; norm_num
    have h0 : C (-2 : ℚ) = -2 := by rw [map_neg, map_ofNat]
    linear_combination h1 + X ^ 3 * h2 + X ^ 3 * h3 - C (-1 / 2 : ℚ) * h0
  have := ell_torsion_of_elementary hC hCall x y hx 0 0 (-2) hsq (by rw [hy]; push_cast; ring)
    hgen 0 (Finset.univ : Finset Unit) (fun _ ↦ 3) (fun _ ↦ 5) (fun _ ↦ ns35)
    (fun _ _ ↦ by norm_num) (fun _ _ _ _ _ ↦ Subsingleton.elim _ _) (fun _ ↦ 1) 1 one_ne_zero (by
      convert h using 1
      simp only [map_zero, zero_add, Finset.univ_unique, Finset.sum_singleton]
      push_cast
      rw [div_div]; ring_nf)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul] at this
  exact not_torsion_35 this

/-- `a = −(x³ + 12x² − 6x + 10)`, `b = 6(x + 1)`: `u = a + b y` on `y² = x³ + 1` has divisor
`6 (2, 3) − 6 ∞` (the point `(2, 3)` has order 6); its norm is `(x − 2)⁶`. -/
noncomputable def a23 : ℚ[X] := -(X ^ 3 + 12 * X ^ 2 - 6 * X + 10)
/-- See `a23`. -/
noncomputable def b23 : ℚ[X] := 6 * (X + 1)

/-- The certificate identity for `G = 3/(x − 2) + R'`: `G = (1/6) M/N + (R' − 1)`. -/
lemma cert_23 (R' : ℚ[X]) :
    (3 + R' * (X - 2)) * (a23 ^ 2 - b23 ^ 2 * (X ^ 3 + 1)) =
      (X - 2) * (C (1 / 6 : ℚ) * (2 * (X ^ 3 + 1) * (a23 * derivative b23 - derivative a23 * b23) +
        a23 * b23 * derivative (X ^ 3 + 1)) + (R' - 1) * (a23 ^ 2 - b23 ^ 2 * (X ^ 3 + 1))) := by
  have h6 : C (1 / 6 : ℚ) * 6 = 1 := by
    rw [show (6 : ℚ[X]) = C 6 from (map_ofNat C 6).symm, ← C_mul]; norm_num
  simp only [a23, b23, derivative_add, derivative_mul, derivative_C, derivative_X,
    derivative_X_pow, derivative_one, derivative_sub, derivative_neg, derivative_ofNat, zero_mul,
    zero_add, add_zero, mul_one, Nat.cast_ofNat, map_ofNat]
  linear_combination (-(X + 1) * ((-(X ^ 3 + 12 * X ^ 2 - 6 * X + 10)) ^ 2 -
    (6 * (X + 1)) ^ 2 * (X ^ 3 + 1))) * h6

lemma natDeg_x3 : (X ^ 3 + 1 : ℚ[X]) ≠ 0 := Monic.ne_zero (by monicity!)

lemma hX2 : (X - 2 : ℚ[X]) ≠ 0 := by
  rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm]; exact X_sub_C_ne_zero 2

/-- **`∫ 3 dx / ((x − 2) √(x³ + 1))` is not elementary**, although its residue divisor is
torsion (`(2, 3)` has order 6): after removing `(1/3) log u − (1/6) log (x − 2)⁶` there remains
`−∫ dx / √(x³ + 1)`. -/
theorem elliptic_torsion_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (3 / ((x - 2) * y)) := by
  have hy' : y ^ 2 = aeval x (X ^ 3 + 1 : ℚ[X]) := by simp [hy]
  have e := ell_log_reduce hC x y hx _ natDeg_x3 hy' (3 + 0 * (X - 2)) (X - 2) a23 b23 (0 - 1)
    (1 / 6) hX2 (by
      rw [show (a23 ^ 2 - b23 ^ 2 * (X ^ 3 + 1) : ℚ[X]) = (X - 2) ^ 6 by
        simp only [a23, b23]; ring]
      exact pow_ne_zero _ hX2) (cert_23 0)
  have hB := HypExample.elliptic_not_elementary hC hCall x y hx hy hgen
  simp only [zero_mul, add_zero, zero_sub, map_ofNat, map_sub, aeval_X, map_neg, map_one] at e
  rw [e]
  intro h
  exact hB (by simpa [neg_div] using h.neg)

/-- **`∫ (x + 1) dx / ((x − 2) √(x³ + 1))` is elementary**: it equals
`(1/3) log (a + b y) − (1/6) log (x − 2)⁶` with `a, b` as in `a23`, `b23`. -/
theorem elliptic_torsion_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) :
    HasElementaryIntegral ((x + 1) / ((x - 2) * y)) := by
  have hy' : y ^ 2 = aeval x (X ^ 3 + 1 : ℚ[X]) := by simp [hy]
  have e := ell_log_reduce hC x y hx _ natDeg_x3 hy' (3 + 1 * (X - 2)) (X - 2) a23 b23 (1 - 1)
    (1 / 6) hX2 (by
      rw [show (a23 ^ 2 - b23 ^ 2 * (X ^ 3 + 1) : ℚ[X]) = (X - 2) ^ 6 by
        simp only [a23, b23]; ring]
      exact pow_ne_zero _ hX2) (cert_23 1)
  have h3 : aeval x (3 + 1 * (X - 2) : ℚ[X]) = x + 1 := by
    simp only [map_add, map_mul, map_one, map_sub, aeval_X, map_ofNat]; ring
  rw [h3, map_sub, aeval_X, map_ofNat] at e
  rw [e]
  simp only [sub_self, map_zero, zero_div]
  simpa using hasElementaryIntegral_of_deriv (0 : E)

end Differential.EllExample