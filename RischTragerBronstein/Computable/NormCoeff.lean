import RischTragerBronstein.Computable.EuclidDegree

/-!
# Normalisation of a fraction of polynomials

`normCoeff (n, d)` divides `n` and `d` by their gcd and makes `d` monic (`0 / 1` when `d = 0`).
`normCoeff_spec`: the value `ψ n / ψ d` is unchanged, for every injective ring homomorphism
`ψ : R[X] →+* K` into a field. This is post-composed with every operation of `R(x)` (`ops₁g`),
so that codes stay reduced.
-/

open Polynomial

namespace CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Divide numerator and denominator by their gcd and make the denominator monic. -/
def normCoeff (q : CPoly R × CPoly R) : CPoly R × CPoly R :=
  if isZero q.2 then ([], [1])
  else
    let g := (egcd q.1 q.2).1
    let d := trim (divMod q.2 g).1
    let c := (lead d)⁻¹
    (smul c (divMod q.1 g).1, smul c d)

end Defs

variable {R K : Type*} [Field R] [DecidableEq R] [Field K]

/-- The denominator of `normCoeff q` is nonzero. -/
lemma normCoeff_den_ne_zero (q : CPoly R × CPoly R) : toPoly (normCoeff q).2 ≠ 0 := by
  unfold normCoeff
  split_ifs with hz
  · simp [toPoly]
  · have hq2 : toPoly q.2 ≠ 0 := fun h ↦ hz ((isZero_iff _).mpr h)
    simp only
    obtain ⟨hg1, hg2⟩ := egcd_dvd q.1 q.2
    have hg0 : toPoly (egcd q.1 q.2).1 ≠ 0 := fun h ↦ by
      rw [h] at hg2; exact hq2 (zero_dvd_iff.mp hg2)
    have hspec := divMod_spec q.2 (egcd q.1 q.2).1
    have hrem : toPoly (egcd q.1 q.2).1 ∣ toPoly (divMod q.2 (egcd q.1 q.2).1).2 := by
      have : toPoly (divMod q.2 (egcd q.1 q.2).1).2 = toPoly q.2 -
          toPoly (divMod q.2 (egcd q.1 q.2).1).1 * toPoly (egcd q.1 q.2).1 := by rw [hspec]; ring
      rw [this]
      exact dvd_sub hg2 (Dvd.intro_left _ rfl)
    have h0 := eq_zero_of_dvd_of_degree_lt hrem (divMod_degree_lt q.2 _ hg0)
    rw [h0, add_zero] at hspec
    have hd0 : toPoly (divMod q.2 (egcd q.1 q.2).1).1 ≠ 0 := fun h ↦ hq2 (by rw [hspec, h, zero_mul])
    have hdne : trim (divMod q.2 (egcd q.1 q.2).1).1 ≠ [] := fun h ↦
      hd0 ((trim_eq_nil_iff _).mp h)
    obtain ⟨-, -, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hdne
    rw [toPoly_smul, toPoly_trim]
    exact mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hlc0)) hd0

/-- **`normCoeff` preserves the value.** -/
theorem normCoeff_spec (ψ : R[X] →+* K) (hψ : Function.Injective ψ) (q : CPoly R × CPoly R) :
    ψ (toPoly (normCoeff q).1) / ψ (toPoly (normCoeff q).2) = ψ (toPoly q.1) / ψ (toPoly q.2) := by
  unfold normCoeff
  split_ifs with hz
  · have hz' := (isZero_iff _).mp hz
    simp [toPoly, hz']
  · have hq2 : toPoly q.2 ≠ 0 := fun h ↦ hz ((isZero_iff _).mpr h)
    simp only
    obtain ⟨hg1, hg2⟩ := egcd_dvd q.1 q.2
    have hg0 : toPoly (egcd q.1 q.2).1 ≠ 0 := fun h ↦ by
      rw [h] at hg2; exact hq2 (zero_dvd_iff.mp hg2)
    have exact : ∀ p : CPoly R, toPoly (egcd q.1 q.2).1 ∣ toPoly p →
        toPoly p = toPoly (divMod p (egcd q.1 q.2).1).1 * toPoly (egcd q.1 q.2).1 := fun p hp ↦ by
      have hspec := divMod_spec p (egcd q.1 q.2).1
      have hrem : toPoly (egcd q.1 q.2).1 ∣ toPoly (divMod p (egcd q.1 q.2).1).2 := by
        have : toPoly (divMod p (egcd q.1 q.2).1).2 = toPoly p -
            toPoly (divMod p (egcd q.1 q.2).1).1 * toPoly (egcd q.1 q.2).1 := by rw [hspec]; ring
        rw [this]
        exact dvd_sub hp (Dvd.intro_left _ rfl)
      have h0 := eq_zero_of_dvd_of_degree_lt hrem (divMod_degree_lt p _ hg0)
      rwa [h0, add_zero] at hspec
    have e1 := exact q.1 hg1
    have e2 := exact q.2 hg2
    have hd0 : toPoly (divMod q.2 (egcd q.1 q.2).1).1 ≠ 0 := fun h ↦ hq2 (by rw [e2, h, zero_mul])
    have hdne : trim (divMod q.2 (egcd q.1 q.2).1).1 ≠ [] := fun h ↦
      hd0 ((trim_eq_nil_iff _).mp h)
    obtain ⟨-, -, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hdne
    have hψg : ψ (toPoly (egcd q.1 q.2).1) ≠ 0 := (map_ne_zero_iff _ hψ).mpr hg0
    have hψc : ψ (C (lead (trim (divMod q.2 (egcd q.1 q.2).1).1))⁻¹) ≠ 0 :=
      (map_ne_zero_iff _ hψ).mpr (C_ne_zero.mpr (inv_ne_zero hlc0))
    rw [toPoly_smul, toPoly_smul, toPoly_trim, map_mul, map_mul, mul_div_mul_left _ _ hψc, e1, e2,
      map_mul, map_mul, mul_div_mul_right _ _ hψg]

end CPoly

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- **`normCoeff` returns a reduced fraction.** -/
theorem normCoeff_coprime (q : CPoly R × CPoly R) :
    IsCoprime (toPoly (normCoeff q).1) (toPoly (normCoeff q).2) := by
  unfold normCoeff
  split_ifs with hz
  · have h1 : toPoly ([1] : CPoly R) = 1 := by simp [toPoly]
    rw [h1]; exact isCoprime_one_right
  · have hq2 : toPoly q.2 ≠ 0 := fun h ↦ hz ((isZero_iff _).mpr h)
    simp only
    obtain ⟨hg1, hg2⟩ := egcd_dvd q.1 q.2
    set g := (egcd q.1 q.2).1 with hg
    have hg0 : toPoly g ≠ 0 := fun h ↦ by rw [h] at hg2; exact hq2 (zero_dvd_iff.mp hg2)
    have exact : ∀ p : CPoly R, toPoly g ∣ toPoly p →
        toPoly p = toPoly (divMod p g).1 * toPoly g := fun p hp ↦ by
      have hspec := divMod_spec p g
      have hrem : toPoly g ∣ toPoly (divMod p g).2 := by
        have : toPoly (divMod p g).2 = toPoly p - toPoly (divMod p g).1 * toPoly g := by
          rw [hspec]; ring
        rw [this]
        exact dvd_sub hp (Dvd.intro_left _ rfl)
      have h0 := eq_zero_of_dvd_of_degree_lt hrem (divMod_degree_lt p _ hg0)
      rwa [h0, add_zero] at hspec
    have e1 := exact q.1 hg1
    have e2 := exact q.2 hg2
    have hbez := egcd_spec q.1 q.2
    rw [← hg, e1, e2] at hbez
    have hcopAB : IsCoprime (toPoly (divMod q.1 g).1) (toPoly (divMod q.2 g).1) :=
      ⟨toPoly (egcd q.1 q.2).2.1, toPoly (egcd q.1 q.2).2.2, mul_right_cancel₀ hg0 (by
        rw [one_mul]; linear_combination hbez)⟩
    have hd0 : toPoly (divMod q.2 g).1 ≠ 0 := fun h ↦ hq2 (by rw [e2, h, zero_mul])
    have hdne : trim (divMod q.2 g).1 ≠ [] := fun h ↦ hd0 ((trim_eq_nil_iff _).mp h)
    obtain ⟨-, -, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hdne
    have hu : IsUnit (C (lead (trim (divMod q.2 g).1))⁻¹ : R[X]) :=
      isUnit_C.mpr (inv_ne_zero hlc0).isUnit
    rw [toPoly_smul, toPoly_smul, toPoly_trim]
    exact (isCoprime_mul_unit_left_left hu _ _).mpr ((isCoprime_mul_unit_left_right hu _ _).mpr hcopAB)

end CPoly
