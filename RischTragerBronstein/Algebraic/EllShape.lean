import RischTragerBronstein.Algebraic.EllGlue

/-!
# The shape of a norm: `N = λ ∏ (X − αᵢ)^{mᵢ} g` with `g ∣ p`

If every irreducible factor of `N` is some `X − αᵢ` (with exact multiplicity `mᵢ`) or a simple
factor of `p`, then `N = C λ · ∏ (X − αᵢ)^{mᵢ} · g` with `g ∣ p`.
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F]

theorem norm_shape {ι : Type*} (N p : F[X]) (hN0 : N ≠ 0) (s : Finset ι) (α : ι → F)
    (hinj : Set.InjOn α s) (m : ι → ℕ)
    (hm : ∀ i ∈ s, (X - C (α i)) ^ m i ∣ N ∧ ¬(X - C (α i)) ^ (m i + 1) ∣ N)
    (hshape : ∀ q : F[X], Irreducible q → q ∣ N →
      (∃ i ∈ s, q ∣ X - C (α i)) ∨ (q ∣ p ∧ ¬q ^ 2 ∣ N)) :
    ∃ (lam : F) (g : F[X]), lam ≠ 0 ∧ g ∣ p ∧ N = C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * g := by
  classical
  set P := ∏ i ∈ s, (X - C (α i)) ^ m i with hP
  have hPN : P ∣ N := by
    refine Finset.prod_dvd_of_coprime ?_ fun i hi ↦ (hm i hi).1
    intro i hi j hj hij
    refine IsCoprime.pow ?_
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun h ↦ hij (hinj hi hj h)).isUnit
  obtain ⟨R, hR⟩ := hPN
  have hR0 : R ≠ 0 := by rintro rfl; rw [mul_zero] at hR; exact hN0 hR
  -- every irreducible factor of `R` is a simple factor of `p`
  have hRq : ∀ q : F[X], Irreducible q → q ∣ R → q ∣ p ∧ ¬q ^ 2 ∣ R := by
    intro q hq hqR
    have hqN : q ∣ N := hR ▸ dvd_mul_of_dvd_right hqR _
    rcases hshape q hq hqN with ⟨i, hi, hqi⟩ | ⟨hqp, hqq⟩
    · exfalso
      apply (hm i hi).2
      have hPi : (X - C (α i)) ^ m i ∣ P := Finset.dvd_prod_of_mem _ hi
      have hqi' : X - C (α i) ∣ R :=
        dvd_trans (hq.dvd_symm (irreducible_X_sub_C (α i)) hqi) hqR
      rw [hR, pow_succ]
      exact mul_dvd_mul hPi hqi'
    · exact ⟨hqp, fun h ↦ hqq (hR ▸ dvd_mul_of_dvd_right h _)⟩
  -- hence `R ∣ p`
  have hRp : R ∣ p := by
    obtain ⟨h, hh⟩ := gcd_dvd_left R p
    have hunit : IsUnit h := by
      by_contra hu
      have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hR0 hh
      obtain ⟨q, hq, hqh⟩ := WfDvdMonoid.exists_irreducible_factor hu hh0
      have hqR : q ∣ R := hh ▸ dvd_mul_of_dvd_right hqh _
      have hqg : q ∣ gcd R p := dvd_gcd hqR (hRq q hq hqR).1
      exact (hRq q hq hqR).2 (by rw [hh, sq]; exact mul_dvd_mul hqg hqh)
    rw [hh]
    exact (IsUnit.mul_right_dvd hunit).mpr (gcd_dvd_right _ _)
  have hlc := leadingCoeff_ne_zero.mpr hR0
  have e : C R.leadingCoeff * (C R.leadingCoeff⁻¹ * R) = R := by
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
  refine ⟨R.leadingCoeff, C R.leadingCoeff⁻¹ * R, hlc,
    dvd_trans ⟨C R.leadingCoeff, by rw [mul_comm]; exact e.symm⟩ hRp, ?_⟩
  rw [hR, mul_comm (C R.leadingCoeff), mul_assoc, e]

end Differential
