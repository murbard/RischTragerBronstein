import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.CharP.Lemmas

/-!
# Stepanov's method, step 1: Hasse derivatives in characteristic `p`

In characteristic `p`, the Hasse derivatives of order `< p` treat `X^{jp}` as a constant
(`hasseDeriv_X_pow_mul`): the binomial coefficients `C(jp, i)` vanish for `0 < i < p` (Lucas).
-/

open Polynomial

namespace Stepanov

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

lemma choose_mul_cast_eq_zero (j i : ℕ) (hi0 : 0 < i) (hip : i < p) :
    (((j * p).choose i : ℕ) : R) = 0 := by
  rw [CharP.cast_eq_zero_iff R p]
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := j * p) (k := i))
  rw [Nat.mul_mod_left, Nat.mod_eq_of_lt hip, Nat.choose_eq_zero_of_lt hi0, zero_mul] at h
  exact Nat.modEq_zero_iff_dvd.mp h

lemma hasseDeriv_X_pow_mul_p (j i : ℕ) (hi0 : 0 < i) (hip : i < p) :
    hasseDeriv i ((X : R[X]) ^ (j * p)) = 0 := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial, choose_mul_cast_eq_zero j i hi0 hip,
    zero_mul, monomial_zero_right]

/-- **`X^{jp}` is a constant for the Hasse derivatives of order `< p`.** -/
theorem hasseDeriv_X_pow_mul (j k : ℕ) (hk : k < p) (h : R[X]) :
    hasseDeriv k ((X : R[X]) ^ (j * p) * h) = X ^ (j * p) * hasseDeriv k h := by
  rw [hasseDeriv_mul, Finset.sum_eq_single (0, k)]
  · simp
  · intro ij hij hne
    have hs := Finset.mem_antidiagonal.mp hij
    have h0 : 0 < ij.1 := by
      rcases Nat.eq_zero_or_pos ij.1 with h | h
      · exact absurd (Prod.ext h (by omega)) hne
      · exact h
    rw [hasseDeriv_X_pow_mul_p j ij.1 h0 (by omega), zero_mul]
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

end Stepanov
