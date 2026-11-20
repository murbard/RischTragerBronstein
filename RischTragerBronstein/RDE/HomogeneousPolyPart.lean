import RischTragerBronstein.RDE.NoSolution

/-!
# `e′ + c e = 0` over `C(x)` forces the polynomial part of `c` to vanish

For `e ∈ C(x)` non-zero, `e′ / e` is a proper fraction (`deg p′ < deg p`). Hence if
`c = P + r / s` with `P ≠ 0` a polynomial and `deg r < deg s`, the homogeneous Risch equation
`e′ + c e = 0` has no non-zero solution. This is the criterion behind the special-denominator
bound at the prime `t₁` of an exponential extension: cancellation at `t₁^{-n}` needs
`g₀ - n a₁′` to be a logarithmic derivative, hence `polypart g₀ = n a₁′`.
-/

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

theorem no_rde_homogeneous_of_polyPart (hD : ∀ P : C'[X], P′ = derivative P)
    (P r s : C'[X]) (hP : P ≠ 0) (hs : s ≠ 0) (hdeg : r.natDegree < s.natDegree ∨ r = 0)
    (e : K) (he : e ≠ 0) : e′ + (φ P + φ r / φ s) * e ≠ 0 := by
  intro h
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := C'[X]) e
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hφq : φ q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq0
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact he (by rw [← hpq, map_zero, zero_div])
  rw [← hpq, Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD] at h
  simp only [smul_eq_mul] at h
  have h' : φ ((derivative p * q - p * derivative q) * s + P * p * q * s + r * p * q) = 0 := by
    simp only [map_add, map_sub, map_mul]
    field_simp at h
    linear_combination h
  have h'' : (derivative p * q - p * derivative q) * s + P * p * q * s + r * p * q = 0 :=
    hinj (by rw [h', map_zero])
  -- the term `P p q s` has the largest degree
  have hPd : P * p * q * s ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hP hp0) hq0) hs
  have hPpqs : (P * p * q * s).natDegree =
      P.natDegree + p.natDegree + q.natDegree + s.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hP hp0) hq0) hs,
      natDegree_mul (mul_ne_zero hP hp0) hq0, natDegree_mul hP hp0]
  have hconst_case : ∀ {u : C'[X]}, u.natDegree = 0 → derivative u = 0 := fun hu ↦ by
    rw [eq_C_of_natDegree_eq_zero hu, derivative_C]
  by_cases hN : P.natDegree + p.natDegree + q.natDegree + s.natDegree = 0
  · -- everything is constant: the equation reads `P p q s = 0`
    have hr0 : r = 0 := by
      rcases hdeg with hlt | hr0
      · omega
      · exact hr0
    rw [hconst_case (by omega : p.natDegree = 0), hconst_case (by omega : q.natDegree = 0),
      hr0] at h''
    simp only [zero_mul, mul_zero, sub_zero, zero_add, add_zero] at h''
    exact hPd h''
  have h1 : ((derivative p * q - p * derivative q) * s).natDegree < (P * p * q * s).natDegree := by
    rw [hPpqs]
    by_cases hpq : p.natDegree + q.natDegree = 0
    · rw [hconst_case (by omega : p.natDegree = 0), hconst_case (by omega : q.natDegree = 0)]
      simp only [zero_mul, mul_zero, sub_zero, natDegree_zero]
      omega
    refine natDegree_mul_le.trans_lt ?_
    have hsub : (derivative p * q - p * derivative q).natDegree < p.natDegree + q.natDegree := by
      refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · rcases eq_or_ne (derivative p) 0 with hdp | hdp
        · rw [hdp, zero_mul, natDegree_zero]; omega
        · have hp1 : p.natDegree ≠ 0 := fun h0 ↦ hdp (hconst_case h0)
          have := natDegree_derivative_lt hp1
          calc (derivative p * q).natDegree ≤ (derivative p).natDegree + q.natDegree :=
              natDegree_mul_le
            _ < p.natDegree + q.natDegree := by omega
      · rcases eq_or_ne (derivative q) 0 with hdq | hdq
        · rw [hdq, mul_zero, natDegree_zero]; omega
        · have hq1 : q.natDegree ≠ 0 := fun h0 ↦ hdq (hconst_case h0)
          have := natDegree_derivative_lt hq1
          calc (p * derivative q).natDegree ≤ p.natDegree + (derivative q).natDegree :=
              natDegree_mul_le
            _ < p.natDegree + q.natDegree := by omega
    omega
  have h2 : (r * p * q).natDegree < (P * p * q * s).natDegree := by
    rw [hPpqs]
    rcases hdeg with hlt | hr0
    · calc (r * p * q).natDegree ≤ r.natDegree + p.natDegree + q.natDegree := by
            refine natDegree_mul_le.trans ?_
            have := natDegree_mul_le (p := r) (q := p)
            omega
        _ < P.natDegree + p.natDegree + q.natDegree + s.natDegree := by omega
    · rw [hr0, zero_mul, zero_mul, natDegree_zero]
      omega
  have hne : (derivative p * q - p * derivative q) * s + P * p * q * s + r * p * q ≠ 0 := by
    intro h0
    have hsum : ((derivative p * q - p * derivative q) * s + P * p * q * s).natDegree =
        (P * p * q * s).natDegree := natDegree_add_eq_right_of_natDegree_lt h1
    have := congrArg natDegree h0
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [hsum]; exact h2), hsum, natDegree_zero] at this
    omega
  exact hne h''

end Differential
