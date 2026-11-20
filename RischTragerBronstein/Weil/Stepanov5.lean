import RischTragerBronstein.Weil.Stepanov1
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Stepanov's method, step 5: counting zeros with multiplicity

If the Hasse derivatives of order `< M` of `R` vanish at `x`, then `(X − x)^M ∣ R`
(`X_sub_C_pow_dvd_of_hasseDeriv`, via the Taylor expansion at `x`); a non-zero `R` with such zeros
at the points of `S` has `M |S| ≤ deg R` (`mul_card_le_natDegree`).
-/

open Polynomial

namespace Stepanov

variable {K : Type*} [Field K]

theorem X_sub_C_pow_dvd_of_hasseDeriv (R : K[X]) (x : K) (M : ℕ)
    (h : ∀ k < M, (hasseDeriv k R).eval x = 0) : (X - C x) ^ M ∣ R := by
  have hT : X ^ M ∣ taylor x R := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [taylor_coeff]; exact h k hk
  obtain ⟨Q, hQ⟩ := hT
  have e : R = taylor (-x) (taylor x R) := by rw [taylor_taylor, neg_add_cancel, taylor_zero]
  refine ⟨taylor (-x) Q, ?_⟩
  rw [e, hQ, taylor_mul, taylor_pow, taylor_X, C_neg, ← sub_eq_add_neg]

theorem mul_card_le_natDegree (R : K[X]) (hR : R ≠ 0) (M : ℕ) (S : Finset K)
    (h : ∀ x ∈ S, (X - C x) ^ M ∣ R) : M * S.card ≤ R.natDegree := by
  classical
  have hdvd : ∏ x ∈ S, (X - C x) ^ M ∣ R := by
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab ↦ ?_) h
    exact ((pairwise_coprime_X_sub_C (s := fun y : K ↦ y) Function.injective_id) hab).pow
  have hdeg := natDegree_le_of_dvd hdvd hR
  rw [natDegree_prod _ _ (fun x _ ↦ pow_ne_zero _ (X_sub_C_ne_zero x))] at hdeg
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, smul_eq_mul] at hdeg
  linarith

end Stepanov
