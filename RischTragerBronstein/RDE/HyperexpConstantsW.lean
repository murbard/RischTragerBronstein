import RischTragerBronstein.RDE.HyperexpConstants

/-!
# A hyperexponential over `C(x)` introduces no new constants — general `η`

`t′ = η t`, `η = Gn / Gd ∈ C(x)`: if `y′ = c η y` has only the zero solution in `C(x)` for every
`c ∈ ℤ ∖ {0}` (which `CPoly.hyperexpW_homogeneous` derives from the monomial certificate), then
`P′ tⁿ = P (tⁿ)′` forces `P = e tⁿ`.
-/

open Polynomial

namespace Differential

variable {C' F : Type*} [Field C'] [CharZero C'] [Differential C'[X]]
variable [Field F] [CharZero F] [Algebra C'[X] F] [IsFractionRing C'[X] F] [Differential F]
variable [DifferentialAlgebra C'[X] F] [Differential F[X]]

theorem hyperexp_no_new_constants_W (Gn Gd : C'[X])
    (hhom : ∀ c : ℤ, c ≠ 0 → ∀ y : F,
      y′ = algebraMap C'[X] F (C (c : C')) * (algebraMap C'[X] F Gn / algebraMap C'[X] F Gd) * y →
        y = 0)
    (hDF : ∀ P : F[X], P′ =
      implicitDeriv (C (algebraMap C'[X] F Gn / algebraMap C'[X] F Gd) * X) P)
    (P : F[X]) (n : ℕ) (h : P′ * X ^ n = P * (X ^ n)′) : ∃ e : F, P = C e * X ^ n := by
  set η := algebraMap C'[X] F Gn / algebraMap C'[X] F Gd with hη
  refine ⟨P.coeff n, ?_⟩
  have hP : implicitDeriv (C η * X) P = C (n * η) * P := by
    rw [hDF, hDF, deriv_X_pow] at h
    have hX : (X : F[X]) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_right_cancel₀ hX
    rw [h]; ring
  ext j
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hjn
  · rw [hjn, mul_one]
  rw [mul_zero]
  have hc := congrArg (fun Q : F[X] ↦ Q.coeff j) hP
  simp only [coeff_implicitDeriv_C_mul_X, coeff_C_mul] at hc
  have hne : ((n : ℤ) - j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hjn)
  refine hhom ((n : ℤ) - j) hne (P.coeff j) ?_
  have hcast : algebraMap C'[X] F (C (((n : ℤ) - j : ℤ) : C')) = (n : F) - j := by
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast C, map_natCast]
  rw [hcast]
  linear_combination hc

end Differential
