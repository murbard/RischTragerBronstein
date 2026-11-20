import RischTragerBronstein.Mixed.RdeLocal

/-!
# Pole bounds for the Risch equation with a logarithmic part, along a branch

**`rde_local_lowerBd_log`**: in `K⸨T⸩` (`K` of characteristic `0`), if `Z′ + (H′ + R) Z = G`,
`G` has no coefficient below `Tᵇ`, and `R` has at most a simple pole (a logarithmic derivative
with constant coefficients) whose residue `ρ` is not `−m` for any integer `m < −B`, then `Z` has no
coefficient below `T^{min(0, b+1, −B)}`. Along a branch the residue of `∑ cⱼ uⱼ′/uⱼ` is
`∑ cⱼ ord uⱼ`, so `B = ∑ ⌈|cⱼ|⌉ |ord uⱼ|` works.
-/

open Polynomial HahnSeries

namespace Curves

open LaurentSeries

section Local

variable {K : Type*} [Field K] [CharZero K]

/-- **The local pole bound for `Z′ + (H′ + R) Z = G`**, `R` with at most a simple pole. -/
theorem rde_local_lowerBd_log (Z H R G : LaurentSeries K)
    (hE : LaurentSeries.derivation Z + (LaurentSeries.derivation H + R) * Z = G) (b : ℤ)
    (hG : LowerBd G b) (hR : LowerBd R (-1)) (B : ℕ)
    (hρ : ∀ m : ℤ, m < -(B : ℤ) → (m : K) + R.coeff (-1) ≠ 0) :
    LowerBd Z (min (min 0 (b + 1)) (-(B : ℤ))) := by
  by_contra hZ
  have hex : ∃ k, k < min (min 0 (b + 1)) (-(B : ℤ)) ∧ Z.coeff k ≠ 0 := by
    unfold LowerBd at hZ; push Not at hZ; exact hZ
  have hZ0 : Z ≠ 0 := by rintro rfl; obtain ⟨k, -, hk⟩ := hex; exact hk (by simp)
  set m := Z.order with hm
  have hmZ : Z.coeff m ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hZ0
  have hZm : LowerBd Z m := fun k hk ↦ HahnSeries.coeff_eq_zero_of_lt_order hk
  have hmlt : m < min (min 0 (b + 1)) (-(B : ℤ)) := by
    obtain ⟨k, hk, hk0⟩ := hex
    exact lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero hk0) hk
  have hm0 : m < 0 := by
    have := min_le_left (min 0 (b + 1)) (-(B : ℤ)); have := min_le_left 0 (b + 1); omega
  have hmb : m - 1 < b := by
    have := min_le_left (min 0 (b + 1)) (-(B : ℤ)); have := min_le_right 0 (b + 1); omega
  have hmB : m < -(B : ℤ) := lt_of_lt_of_le hmlt (min_le_right _ _)
  have hRZ : LowerBd (R * Z) (-1 + m) := hR.mul hZm
  have hRZc : (R * Z).coeff (-1 + m) = R.coeff (-1) * Z.coeff m := coeff_mul_lowerBd hR hZm
  by_cases hH : LowerBd H 0
  · -- `H` regular: `Z′ + R Z` dominates
    have hH' : LowerBd (LaurentSeries.derivation H) 0 := fun k hk ↦ by
      rw [coeff_derivation]
      by_cases hk1 : k + 1 = 0
      · rw [hk1]; simp
      · rw [hH (k + 1) (by omega), mul_zero]
    have hprod : (LaurentSeries.derivation H * Z).coeff (m - 1) = 0 :=
      (hH'.mul hZm) (m - 1) (by omega)
    have hG1 := hG (m - 1) hmb
    rw [← hE, HahnSeries.coeff_add, add_mul, HahnSeries.coeff_add, hprod, zero_add,
      coeff_derivation, sub_add_cancel, show m - 1 = -1 + m by ring, hRZc] at hG1
    have : ((m : K) + R.coeff (-1)) * Z.coeff m = 0 := by linear_combination hG1
    rcases mul_eq_zero.mp this with h | h
    · exact hρ m hmB h
    · exact hmZ h
  · -- `H` has a pole of order `p ≥ 1`: `H′ Z` dominates
    have hH0 : H ≠ 0 := by rintro rfl; exact hH (lowerBd_zero 0)
    set q := H.order with hq
    have hqH : H.coeff q ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hH0
    have hHq : LowerBd H q := fun k hk ↦ HahnSeries.coeff_eq_zero_of_lt_order hk
    have hq0 : q < 0 := by
      by_contra hq0; push Not at hq0; exact hH (hHq.mono hq0)
    have hHd : LowerBd (LaurentSeries.derivation H) (q - 1) := fun k hk ↦ by
      rw [coeff_derivation, hHq (k + 1) (by omega), mul_zero]
    have hHdq : (LaurentSeries.derivation H).coeff (q - 1) = (q : K) * H.coeff q := by
      rw [coeff_derivation, sub_add_cancel]
    have hZd : LowerBd (LaurentSeries.derivation Z) (m - 1) := fun k hk ↦ by
      rw [coeff_derivation, hZm (k + 1) (by omega), mul_zero]
    have hG1 := hG (q - 1 + m) (by omega)
    rw [← hE, HahnSeries.coeff_add, add_mul, HahnSeries.coeff_add, hZd (q - 1 + m) (by omega),
      zero_add, hRZ (q - 1 + m) (by omega), add_zero, coeff_mul_lowerBd hHd hZm, hHdq] at hG1
    have hqK : ((q : ℤ) : K) ≠ 0 := by exact_mod_cast hq0.ne
    rcases mul_eq_zero.mp hG1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact hqK h
      · exact hqH h
    · exact hmZ h

end Local

end Curves
