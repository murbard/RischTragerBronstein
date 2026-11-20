import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The naive height on a rational function field

For `x ∈ K(X)` in lowest terms `num x / denom x`, `ht x = max (deg num) (deg denom)` (the degree of
`x` as a map `ℙ¹ → ℙ¹`). This is the Weil height of the function field `K(X)` used for the height
pairing of the Mordell–Weil plan: `ht_mul_le`, `ht_inv`, `ht_add_le`, `ht_C`.
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K]

/-- The naive height of a rational function. -/
noncomputable def ht (x : RatFunc K) : ℕ := max (RatFunc.num x).natDegree (RatFunc.denom x).natDegree

lemma natDegree_le_of_dvd' {p q : K[X]} (h : p ∣ q) (hq : q ≠ 0) : p.natDegree ≤ q.natDegree :=
  natDegree_le_of_dvd h hq

theorem ht_C (k : K) : ht (RatFunc.C k) = 0 := by
  simp [ht, RatFunc.num_C, RatFunc.denom_C]

theorem ht_zero : ht (0 : RatFunc K) = 0 := by simp [ht]

theorem ht_mul_le (x y : RatFunc K) : ht (x * y) ≤ ht x + ht y := by
  by_cases hx : x = 0
  · simp [hx, ht_zero]
  by_cases hy : y = 0
  · simp [hy, ht_zero]
  have hnx : RatFunc.num x ≠ 0 := RatFunc.num_ne_zero hx
  have hny : RatFunc.num y ≠ 0 := RatFunc.num_ne_zero hy
  have hdx : RatFunc.denom x ≠ 0 := RatFunc.denom_ne_zero x
  have hdy : RatFunc.denom y ≠ 0 := RatFunc.denom_ne_zero y
  have h1 : (RatFunc.num (x * y)).natDegree ≤ (RatFunc.num x).natDegree + (RatFunc.num y).natDegree := by
    calc _ ≤ (RatFunc.num x * RatFunc.num y).natDegree :=
          natDegree_le_of_dvd (RatFunc.num_mul_dvd x y) (mul_ne_zero hnx hny)
      _ = _ := natDegree_mul hnx hny
  have h2 : (RatFunc.denom (x * y)).natDegree ≤
      (RatFunc.denom x).natDegree + (RatFunc.denom y).natDegree := by
    calc _ ≤ (RatFunc.denom x * RatFunc.denom y).natDegree :=
          natDegree_le_of_dvd (RatFunc.denom_mul_dvd x y) (mul_ne_zero hdx hdy)
      _ = _ := natDegree_mul hdx hdy
  unfold ht
  refine max_le (h1.trans ?_) (h2.trans ?_) <;> omega

theorem ht_inv_le (x : RatFunc K) : ht x⁻¹ ≤ ht x := by
  by_cases hx : x = 0
  · simp [hx]
  have hnx : RatFunc.num x ≠ 0 := RatFunc.num_ne_zero hx
  have hdx : RatFunc.denom x ≠ 0 := RatFunc.denom_ne_zero x
  unfold ht
  refine max_le ?_ ?_
  · exact (natDegree_le_of_dvd (RatFunc.num_inv_dvd hx) hdx).trans (le_max_right _ _)
  · exact (natDegree_le_of_dvd (RatFunc.denom_inv_dvd hx) hnx).trans (le_max_left _ _)

theorem ht_inv (x : RatFunc K) : ht x⁻¹ = ht x :=
  le_antisymm (ht_inv_le x) (by simpa using ht_inv_le x⁻¹)

theorem ht_add_le (x y : RatFunc K) : ht (x + y) ≤ ht x + ht y := by
  have hdx : RatFunc.denom x ≠ 0 := RatFunc.denom_ne_zero x
  have hdy : RatFunc.denom y ≠ 0 := RatFunc.denom_ne_zero y
  set p := RatFunc.num x * RatFunc.denom y + RatFunc.num y * RatFunc.denom x with hp
  have hq : RatFunc.denom x * RatFunc.denom y ≠ 0 := mul_ne_zero hdx hdy
  have hxy : x + y = algebraMap _ _ p / algebraMap _ _ (RatFunc.denom x * RatFunc.denom y) := by
    conv_lhs => rw [← RatFunc.num_div_denom x, ← RatFunc.num_div_denom y]
    have h1 : (algebraMap K[X] (RatFunc K)) (RatFunc.denom x) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hdx
    have h2 : (algebraMap K[X] (RatFunc K)) (RatFunc.denom y) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hdy
    rw [hp, map_add, map_mul, map_mul, map_mul]
    field_simp
  have hden : (RatFunc.denom (x + y)).natDegree ≤
      (RatFunc.denom x).natDegree + (RatFunc.denom y).natDegree := by
    calc _ ≤ (RatFunc.denom x * RatFunc.denom y).natDegree :=
          natDegree_le_of_dvd (RatFunc.denom_add_dvd x y) hq
      _ = _ := natDegree_mul hdx hdy
  have hnum : (RatFunc.num (x + y)).natDegree ≤ ht x + ht y := by
    by_cases hp0 : p = 0
    · have : x + y = 0 := by rw [hxy, hp0, map_zero, zero_div]
      rw [this]; simp
    have hdv : RatFunc.num (x + y) ∣ p := by
      rw [hxy]; exact RatFunc.num_div_dvd p hq
    refine (natDegree_le_of_dvd hdv hp0).trans ?_
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      unfold ht; omega
    · refine (natDegree_mul_le).trans ?_
      unfold ht; omega
  unfold ht at hnum ⊢
  refine max_le hnum (hden.trans ?_)
  omega

end FFHeight
