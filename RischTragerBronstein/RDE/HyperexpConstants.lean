import RischTragerBronstein.RDE.ExpPolynomial
import RischTragerBronstein.RDE.RationalCoeff

/-!
# A hyperexponential over `C(x)` introduces no new constants

`t′ = η t`, `η = Gn / Gd ∈ C(x)` in lowest terms, without simple poles, `deg Gn + 1 ≠ deg Gd`
(e.g. `η = a′`, `a` a nonconstant rational function): if `P ∈ F[t]` satisfies
`P′ tⁿ = P (tⁿ)′`, then `P = e tⁿ`.
-/

open Polynomial

namespace Differential

variable {C' F : Type*} [Field C'] [CharZero C'] [Differential C'[X]]
variable [Field F] [CharZero F] [Algebra C'[X] F] [IsFractionRing C'[X] F] [Differential F]
variable [DifferentialAlgebra C'[X] F] [Differential F[X]]

theorem hyperexp_no_new_constants (hDC : ∀ P : C'[X], P′ = derivative P) (Gn Gd : C'[X])
    (hGn0 : Gn ≠ 0) (hGd0 : Gd ≠ 0) (hcop : IsCoprime Gn Gd)
    (hsq : ∀ p : C'[X], Irreducible p → p ∣ Gd → p ^ 2 ∣ Gd)
    (hdeg : Gn.natDegree + 1 ≠ Gd.natDegree)
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
  have hne : ((n : C') - j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hjn)
  refine rde_homogeneous_rational hDC Gn Gd hGn0 hGd0 hcop hsq hdeg ((n : C') - j) hne
    (P.coeff j) ?_
  have hcast : algebraMap C'[X] F (C ((n : C') - j)) = (n : F) - j := by
    rw [C_sub, map_sub, map_natCast C, map_natCast C, map_natCast, map_natCast]
  rw [hcast, ← hη]
  linear_combination hc

end Differential
