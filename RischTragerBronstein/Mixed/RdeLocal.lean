import RischTragerBronstein.Curves.ProcRFSound6

/-!
# Pole bounds for the Risch equation along a branch

**`rde_local_lowerBd`**: in `K⸨T⸩` (`K` of characteristic `0`), if `Z′ + H′ Z = G` and `G` has no
coefficient below `Tᵇ`, then `Z` has none below `T^{min(0, b+1)}`. The potential `H′` is a
derivative, so it has no term `T⁻¹`, and the leading terms of `Z′` and `H′ Z` cannot cancel:
either `H` is regular (then `Z′` dominates) or `H` has a pole (then `H′ Z` dominates).
-/

open Polynomial HahnSeries

namespace Curves

open LaurentSeries

section Local

variable {K : Type*} [Field K]

/-- The coefficient of a product at the sum of lower bounds. -/
lemma coeff_mul_lowerBd {x y : LaurentSeries K} {a b : ℤ} (hx : LowerBd x a) (hy : LowerBd y b) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  obtain ⟨t, rfl⟩ := (lowerBd_iff x a).mp hx
  obtain ⟨t', rfl⟩ := (lowerBd_iff y b).mp hy
  have e : single a (1 : K) * ofPowerSeries ℤ K t * (single b 1 * ofPowerSeries ℤ K t') =
      single (a + b) (1 : K) * ofPowerSeries ℤ K (t * t') := by
    rw [map_mul, show single (a + b) (1 : K) = single a 1 * single b 1 by
      rw [single_mul_single, one_mul]]
    ring
  rw [e, LaurentSeries.coeff_single_mul, LaurentSeries.coeff_single_mul,
    LaurentSeries.coeff_single_mul, sub_self, sub_self, sub_self]
  have h0 : ∀ u : PowerSeries K, (ofPowerSeries ℤ K u).coeff 0 = PowerSeries.constantCoeff u :=
    fun u ↦ by
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [h0, h0, h0, map_mul]

variable [CharZero K]

/-- **The local pole bound for `Z′ + H′ Z = G`.** -/
theorem rde_local_lowerBd (Z H G : LaurentSeries K)
    (hE : LaurentSeries.derivation Z + LaurentSeries.derivation H * Z = G) (b : ℤ)
    (hG : LowerBd G b) : LowerBd Z (min 0 (b + 1)) := by
  by_contra hZ
  -- the first non-zero coefficient of `Z` below the bound
  have hex : ∃ k, k < min 0 (b + 1) ∧ Z.coeff k ≠ 0 := by
    unfold LowerBd at hZ; push Not at hZ; exact hZ
  have hZ0 : Z ≠ 0 := by rintro rfl; obtain ⟨k, -, hk⟩ := hex; exact hk (by simp)
  set m := Z.order with hm
  have hmZ : Z.coeff m ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hZ0
  have hZm : LowerBd Z m := fun k hk ↦ HahnSeries.coeff_eq_zero_of_lt_order hk
  have hmlt : m < min 0 (b + 1) := by
    obtain ⟨k, hk, hk0⟩ := hex
    exact lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero hk0) hk
  have hm0 : m < 0 := lt_of_lt_of_le hmlt (min_le_left _ _)
  have hmb : m - 1 < b := by have := min_le_right 0 (b + 1); omega
  by_cases hH : LowerBd H 0
  · -- `H` regular: `Z′` dominates
    have hH' : LowerBd (LaurentSeries.derivation H) 0 := fun k hk ↦ by
      rw [coeff_derivation]
      by_cases hk1 : k + 1 = 0
      · rw [hk1]; simp
      · rw [hH (k + 1) (by omega), mul_zero]
    have hprod : (LaurentSeries.derivation H * Z).coeff (m - 1) = 0 :=
      (hH'.mul hZm) (m - 1) (by omega)
    have hG1 := hG (m - 1) hmb
    rw [← hE, HahnSeries.coeff_add, hprod, add_zero, coeff_derivation, sub_add_cancel] at hG1
    have hmK : ((m : ℤ) : K) ≠ 0 := by exact_mod_cast hm0.ne
    exact hmZ ((mul_eq_zero.mp hG1).resolve_left hmK)
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
    rw [← hE, HahnSeries.coeff_add, hZd (q - 1 + m) (by omega), zero_add,
      coeff_mul_lowerBd hHd hZm, hHdq] at hG1
    have hqK : ((q : ℤ) : K) ≠ 0 := by exact_mod_cast hq0.ne
    rcases mul_eq_zero.mp hG1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact hqK h
      · exact hqH h
    · exact hmZ h

end Local

end Curves
