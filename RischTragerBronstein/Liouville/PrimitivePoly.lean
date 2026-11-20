import RischTragerBronstein.Differential.Monomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Polynomials in a primitive monomial

Let `F` be a differential field of characteristic zero and give `F[t]` the derivation with
`t′ = η ∈ F` (a *primitive* monomial; `η = a′ / a` is the logarithmic case). Assume `t` introduces
no new constants, in the form: every `P ∈ F[t]` with `P′ = 0` lies in `F`. Then

* `not_dvd_deriv_of_monic`: every monic polynomial of positive degree is **normal** (`p ∤ p′`);
  there are no special polynomials (Bronstein, Theorem 5.1.1);
* `eq_linear_of_deriv_eq_C`: if `P′ ∈ F` then `P = c t + d` with `c` a constant
  (Bronstein, Lemma 5.1.2 — the fact that limits the new logarithm to appear linearly, with a
  constant coefficient, in an elementary integral).
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F] [Differential F] (η : F)

/-- `P′` coefficientwise, for `t′ = η`. -/
lemma coeff_implicitDeriv_C (P : F[X]) (k : ℕ) :
    (implicitDeriv (C η) P).coeff k = (P.coeff k)′ + η * (P.coeff (k + 1) * (k + 1)) := by
  simp [implicitDeriv, coeff_derivative]

variable (hconst : ∀ P : F[X], implicitDeriv (C η) P = 0 → ∃ e : F, P = C e)

include hconst in
/-- In a primitive extension without new constants every monic nonconstant polynomial is normal. -/
theorem not_dvd_deriv_of_monic {p : F[X]} (hm : p.Monic) (hdeg : 0 < p.natDegree) :
    ¬p ∣ implicitDeriv (C η) p := by
  intro hdvd
  have hlt : (implicitDeriv (C η) p).degree < p.degree := by
    rw [degree_eq_natDegree hm.ne_zero, degree_lt_iff_coeff_zero]
    intro m hm'
    have hm'' : p.natDegree ≤ m := by exact_mod_cast hm'
    rw [coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < m + 1)]
    rcases hm''.eq_or_lt with h | h
    · rw [← h, hm.coeff_natDegree]; simp
    · rw [coeff_eq_zero_of_natDegree_lt h]; simp
  have h0 : implicitDeriv (C η) p = 0 := by
    by_contra hne
    exact absurd (degree_le_of_dvd hdvd hne) (not_le.mpr hlt)
  obtain ⟨e, he⟩ := hconst p h0
  rw [he, natDegree_C] at hdeg
  exact lt_irrefl _ hdeg

variable [CharZero F]

include hconst in
/-- A polynomial in a primitive monomial whose derivative lies in `F` is `c t + d`, `c′ = 0`. -/
theorem eq_linear_of_deriv_eq_C {P : F[X]} {e : F} (h : implicitDeriv (C η) P = C e) :
    ∃ c d : F, c′ = 0 ∧ P = C c * X + C d := by
  have hcoeff : ∀ k, k ≠ 0 → (P.coeff k)′ + η * (P.coeff (k + 1) * (k + 1)) = 0 := fun k hk ↦ by
    rw [← coeff_implicitDeriv_C, h, coeff_C_of_ne_zero hk]
  rcases le_or_gt P.natDegree 1 with hn | hn
  · refine ⟨P.coeff 1, P.coeff 0, ?_, eq_X_add_C_of_natDegree_le_one hn⟩
    have := hcoeff 1 one_ne_zero
    rwa [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 1 + 1), zero_mul, mul_zero,
      add_zero] at this
  · exfalso
    obtain ⟨n, hn'⟩ : ∃ n, P.natDegree = n + 2 := ⟨P.natDegree - 2, by omega⟩
    set lc := P.coeff (n + 2) with hlc
    have hlc0 : lc ≠ 0 := by
      rw [hlc, ← hn']; exact leadingCoeff_ne_zero.mpr (fun h0 ↦ by simp [h0] at hn)
    have h1 : lc′ = 0 := by
      have := hcoeff (n + 2) (by omega)
      rwa [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 2 + 1), zero_mul, mul_zero,
        add_zero] at this
    have h2 : (P.coeff (n + 1))′ + η * (lc * ((n + 1 : ℕ) + 1 : F)) = 0 := by
      have := hcoeff (n + 1) (by omega)
      simpa [hlc] using this
    -- `w = (n + 2) lc t + P_{n+1}` is a constant outside `F`
    let w : F[X] := C (lc * ((n + 1 : ℕ) + 1 : F)) * X + C (P.coeff (n + 1))
    have hw : implicitDeriv (C η) w = 0 := by
      have hcast : ((lc * ((n + 1 : ℕ) + 1 : F)))′ = 0 := by
        rw [Derivation.leibniz, h1]
        have : (((n + 1 : ℕ) : F) + 1)′ = 0 := by
          rw [← Nat.cast_succ]; exact Derivation.map_natCast _ _
        simp
      simp only [w, map_add, Derivation.leibniz, implicitDeriv_C, implicitDeriv_X, hcast,
        smul_eq_mul, map_zero, mul_zero, add_zero]
      rw [← C_mul, ← C_add, add_comm,
        show (P.coeff (n + 1))′ + lc * (((n + 1 : ℕ) : F) + 1) * η = 0 by linear_combination h2, C_0]
    obtain ⟨e', he'⟩ := hconst w hw
    have : w.coeff 1 = 0 := by rw [he', coeff_C_of_ne_zero one_ne_zero]
    simp only [w, coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C_of_ne_zero one_ne_zero,
      add_zero] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hlc0 h0
    · have : ((n + 1 + 1 : ℕ) : F) = 0 := by push_cast; exact_mod_cast h0
      exact absurd this (Nat.cast_ne_zero.mpr (by omega))

include hconst in
/-- In a primitive extension without new constants, differentiation lowers the degree by at most
one: if `deg P′ ≤ d` then `deg P ≤ d + 1`. -/
theorem natDegree_le_succ_of_natDegree_deriv_le {P : F[X]} {d : ℕ}
    (h : (implicitDeriv (C η) P).natDegree ≤ d) : P.natDegree ≤ d + 1 := by
  by_contra hlt
  obtain ⟨n, hn'⟩ : ∃ n, P.natDegree = n + 2 := ⟨P.natDegree - 2, by omega⟩
  have hcoeff : ∀ k, d < k → (P.coeff k)′ + η * (P.coeff (k + 1) * (k + 1)) = 0 := fun k hk ↦ by
    rw [← coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hk)]
  set lc := P.coeff (n + 2) with hlc
  have hlc0 : lc ≠ 0 := by
    rw [hlc, ← hn']; exact leadingCoeff_ne_zero.mpr (fun h0 ↦ by simp [h0] at hn')
  have h1 : lc′ = 0 := by
    have := hcoeff (n + 2) (by omega)
    rwa [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 2 + 1), zero_mul, mul_zero,
      add_zero] at this
  have h2 : (P.coeff (n + 1))′ + η * (lc * ((n + 1 : ℕ) + 1 : F)) = 0 := by
    have := hcoeff (n + 1) (by omega)
    simpa [hlc] using this
  let w : F[X] := C (lc * ((n + 1 : ℕ) + 1 : F)) * X + C (P.coeff (n + 1))
  have hw : implicitDeriv (C η) w = 0 := by
    have hcast : ((lc * ((n + 1 : ℕ) + 1 : F)))′ = 0 := by
      rw [Derivation.leibniz, h1]
      have : (((n + 1 : ℕ) : F) + 1)′ = 0 := by
        rw [← Nat.cast_succ]; exact Derivation.map_natCast _ _
      simp
    simp only [w, map_add, Derivation.leibniz, implicitDeriv_C, implicitDeriv_X, hcast,
      smul_eq_mul, map_zero, mul_zero, add_zero]
    rw [← C_mul, ← C_add, add_comm,
      show (P.coeff (n + 1))′ + lc * (((n + 1 : ℕ) : F) + 1) * η = 0 by linear_combination h2, C_0]
  obtain ⟨e', he'⟩ := hconst w hw
  have : w.coeff 1 = 0 := by rw [he', coeff_C_of_ne_zero one_ne_zero]
  simp only [w, coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C_of_ne_zero one_ne_zero,
    add_zero] at this
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hlc0 h0
  · have : ((n + 1 + 1 : ℕ) : F) = 0 := by push_cast; exact_mod_cast h0
    exact absurd this (Nat.cast_ne_zero.mpr (by omega))

end Differential
