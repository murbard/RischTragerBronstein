import RischTragerBronstein.Differential.Monomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Polynomials in an exponential monomial

Give `F[t]` the derivation with `t′ = η t`, `η ∈ F` (`η = a′` is the exponential case `t = exp a`).
The no-new-constants hypothesis is used in the form

  `hconst`: if `P / t ^ n` is a constant (`P′ t ^ n = P (t ^ n)′`) then `P = e t ^ n` with `e ∈ F`.

* `deriv_X_pow`: `(t ^ n)′ = n η t ^ n`;
* `not_dvd_deriv_of_monic_ne_X`: a monic irreducible `p ≠ t` is normal — `t` is the only special
  polynomial (Bronstein, Theorem 5.1.2);
* `eq_monomial_of_deriv`: if `(P / t ^ k)′ ∈ F`, i.e. `P′ - k η P = β t ^ k`, then `P = e t ^ k`.
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F] [Differential F] (η : F)

/-- `P′` coefficientwise, for `t′ = η t`. -/
lemma coeff_implicitDeriv_C_mul_X (P : F[X]) (k : ℕ) :
    (implicitDeriv (C η * X) P).coeff k = (P.coeff k)′ + η * (k * P.coeff k) := by
  have : (C η * X * derivative P).coeff k = η * (k * P.coeff k) := by
    rw [mul_assoc, coeff_C_mul]
    cases k with
    | zero => simp
    | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  simp only [implicitDeriv, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply, Pi.smul_apply,
    Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, coeff_add, coeff_mapCoeffs,
    this]

lemma deriv_X_pow (n : ℕ) : implicitDeriv (C η * X) (X ^ n) = C (n * η) * X ^ n := by
  ext k
  rw [coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp; ring
  · simp

/-- `(y t)′ = (y′ + η y) t`. -/
lemma implicitDeriv_C_mul_X (y : F) :
    implicitDeriv (C η * X) (C y * X) = C (y′ + η * y) * X := by
  rw [Derivation.leibniz, implicitDeriv_C, implicitDeriv_X]
  simp only [smul_eq_mul, C_add, C_mul]
  ring

variable (hconst : ∀ (P : F[X]) (n : ℕ),
  implicitDeriv (C η * X) P * X ^ n = P * implicitDeriv (C η * X) (X ^ n) → ∃ e : F, P = C e * X ^ n)

include hconst in
/-- In an exponential extension without new constants, `t` is the only special monic irreducible
polynomial. -/
theorem not_dvd_deriv_of_monic_ne_X {p : F[X]} (hm : p.Monic) (hirr : Irreducible p)
    (hX : p ≠ X) : ¬p ∣ implicitDeriv (C η * X) p := by
  intro hdvd
  set n := p.natDegree with hn
  have hpos : 0 < n := hirr.natDegree_pos
  -- `p′ = n η p`
  have hR : implicitDeriv (C η * X) p - C (n * η) * p = 0 := by
    by_contra hne
    have hlt : (implicitDeriv (C η * X) p - C (n * η) * p).degree < p.degree := by
      rw [degree_eq_natDegree hm.ne_zero, degree_lt_iff_coeff_zero]
      intro m hm'
      have hm'' : n ≤ m := by exact_mod_cast hm'
      rw [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul]
      rcases hm''.eq_or_lt with h | h
      · rw [← h, hn, hm.coeff_natDegree]; simp; ring
      · rw [coeff_eq_zero_of_natDegree_lt h]; simp
    have hd : p ∣ implicitDeriv (C η * X) p - C (n * η) * p :=
      dvd_sub hdvd (Dvd.intro_left _ rfl)
    exact absurd (degree_le_of_dvd hd hne) (not_le.mpr hlt)
  have hp' : implicitDeriv (C η * X) p = C (n * η) * p := sub_eq_zero.mp hR
  obtain ⟨e, he⟩ := hconst p n (by rw [hp', deriv_X_pow]; ring)
  -- so `p = e t ^ n` is irreducible and monic: `p = t`
  obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hfac : p = X * (C e * X ^ j) := by rw [he, hj]; ring
  have hu : IsUnit (C e * X ^ j) :=
    (hirr.isUnit_or_isUnit hfac).resolve_left not_isUnit_X
  have he0 : e ≠ 0 := by rintro rfl; rw [he] at hm; simp at hm
  have hj0 : j = 0 := by
    have := natDegree_eq_zero_of_isUnit hu
    rwa [natDegree_C_mul_X_pow j e he0] at this
  subst hj0
  have he1 : e = 1 := by
    have := hm.leadingCoeff
    rw [hfac, pow_zero, mul_one, leadingCoeff_mul, leadingCoeff_X, leadingCoeff_C, one_mul] at this
    exact this
  exact hX (by rw [hfac, he1]; simp)

include hconst in
/-- If `(P / t ^ k)′ ∈ F` then `P / t ^ k ∈ F`. -/
theorem eq_monomial_of_deriv {P : F[X]} {k : ℕ} {β : F}
    (h : implicitDeriv (C η * X) P - C (k * η) * P = C β * X ^ k) :
    P = C (P.coeff k) * X ^ k := by
  ext j
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hjk
  · rw [hjk, mul_one]
  rw [mul_zero]
  have hc := congrArg (fun Q : F[X] ↦ Q.coeff j) h
  simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_X_pow, hjk, ite_false,
    mul_zero] at hc
  -- `Q = P_j t ^ j` has `Q / t ^ k` constant
  obtain ⟨e, he⟩ := hconst (C (P.coeff j) * X ^ j) k (by
    rw [Derivation.leibniz, deriv_X_pow, deriv_X_pow, implicitDeriv_C]
    simp only [smul_eq_mul]
    have : C ((P.coeff j)′) = C ((k : F) * η * P.coeff j - η * (j * P.coeff j)) := by
      congr 1; linear_combination hc
    rw [this]
    simp only [C_sub, C_mul]
    ring)
  have := congrArg (fun Q : F[X] ↦ Q.coeff j) he
  simpa [coeff_C_mul, coeff_X_pow, hjk] using this

end Differential
