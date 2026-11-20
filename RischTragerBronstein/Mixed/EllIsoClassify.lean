import RischTragerBronstein.Mixed.KXRepS2
import RischTragerBronstein.Mixed.EllConstPts

/-!
# Classification of curves with constant `j`

`ConstScale A B`: `y² = x³ + A x + B` is a constant curve up to scaling (`A = u⁴ a`, `B = u⁶ b`,
`a, b ∈ K`). **`const_j_classify`**: a curve with constant `j` (`A = 0`, `B = 0` or `A³ = r B²`) is a
non-trivial twist of a constant curve (`IsoNT`, where heights are positive) or constant up to scaling
(where all points are constant, `weierstrass_const`, and the Mordell–Weil question descends to `K`).
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- Constant up to scaling. -/
def ConstScale (A B : K[X]) : Prop :=
  ∃ (u : RatFunc K) (a b : K), u ≠ 0 ∧ ι A = u ^ 4 * κ a ∧ ι B = u ^ 6 * κ b

/-- A rational function whose power is a polynomial is a polynomial. -/
theorem poly_of_pow (n : ℕ) (hn : 0 < n) (w : RatFunc K) (p : K[X]) (h : w ^ n = ι p) :
    ∃ q : K[X], w = ι q := by
  have hint : IsIntegral K[X] w := by
    refine ⟨X ^ n - Polynomial.C p, monic_X_pow_sub_C _ hn.ne', ?_⟩
    simp [eval₂_sub, h]
  obtain ⟨q, hq⟩ := (IsIntegrallyClosed.isIntegral_iff (R := K[X]) (K := RatFunc K)).mp hint
  exact ⟨q, hq.symm⟩

/-- If `c D³` is a square (`c ≠ 0`), then `D` is a constant times a square. -/
theorem sq_of_cube_sq (D : K[X]) (hD : D ≠ 0) (c : K) (hc : c ≠ 0) (w : RatFunc K)
    (h : κ c * ι D ^ 3 = w ^ 2) : ∃ v : RatFunc K, v ≠ 0 ∧ ι D = κ c⁻¹ * v ^ 2 := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hD' : ι D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hc' : κ c ≠ 0 := by simpa using hc
  refine ⟨w / ι D, div_ne_zero (fun hw ↦ ?_) hD', ?_⟩
  · rw [hw] at h; simp at h; exact absurd h (by simp [hc, hD])
  · rw [div_pow, ← h, map_inv₀]; field_simp

theorem const_j_classify (A B : K[X]) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hj : A = 0 ∨ B = 0 ∨ ∃ r : K, A ^ 3 = C r * B ^ 2) : IsoNT A B ∨ ConstScale A B := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  by_cases hA : A = 0
  · subst hA
    have hB : B ≠ 0 := by rintro rfl; simp at hΔ'
    by_cases hcube : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι B ≠ w ^ 3
    · exact Or.inl (Or.inl ⟨rfl, hB, hcube⟩)
    push_neg at hcube
    obtain ⟨c, w, hc, hcw⟩ := hcube
    -- `B = c⁻¹ w³` with `w` a polynomial
    obtain ⟨D, hD⟩ := poly_of_pow 3 (by norm_num) w (C c * B) (by
      rw [← hcw, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C])
    have hD0 : D ≠ 0 := by
      rintro rfl; rw [map_zero] at hD; rw [hD] at hcw; simp at hcw
      exact absurd hcw (by simp [hc, hB])
    have hcB : C c * B = D ^ 3 := hinj (by
      rw [map_pow, ← hD, ← hcw, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C])
    have hBD : B = C c⁻¹ * D ^ 3 := by
      rw [← hcB, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    by_cases hsq : ∀ (c' : K) (w' : RatFunc K), c' ≠ 0 → κ c' * ι D ^ 3 ≠ w' ^ 2
    · refine Or.inl (Or.inr (Or.inr ⟨0, c⁻¹, D, hD0, by simp [hc], by simp, hBD, hsq⟩))
    push_neg at hsq
    obtain ⟨c', w', hc', hcw'⟩ := hsq
    obtain ⟨v, hv, hDv⟩ := sq_of_cube_sq D hD0 c' hc' w' hcw'
    refine Or.inr ⟨v, 0, c⁻¹ * c'⁻¹ ^ 3, hv, by simp, ?_⟩
    rw [hBD, map_mul, map_pow, hDv, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
    simp only [map_mul, map_pow]; ring
  by_cases hB : B = 0
  · subst hB
    by_cases hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι A ≠ w ^ 2
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, hA, hsq⟩))
    push_neg at hsq
    obtain ⟨c, w, hc, hcw⟩ := hsq
    obtain ⟨D, hD⟩ := poly_of_pow 2 (by norm_num) w (C c * A) (by
      rw [← hcw, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C])
    have hD0 : D ≠ 0 := by
      rintro rfl; rw [map_zero] at hD; rw [hD] at hcw; simp at hcw
      exact absurd hcw (by simp [hc, hA])
    have hcA : C c * A = D ^ 2 := hinj (by
      rw [map_pow, ← hD, ← hcw, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C])
    have hAD : A = C c⁻¹ * D ^ 2 := by
      rw [← hcA, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    by_cases hsq2 : ∀ (c' : K) (w' : RatFunc K), c' ≠ 0 → κ c' * ι D ^ 3 ≠ w' ^ 2
    · refine Or.inl (Or.inr (Or.inr ⟨c⁻¹, 0, D, hD0, by simp [hc], hAD, by simp, hsq2⟩))
    push_neg at hsq2
    obtain ⟨c', w', hc', hcw'⟩ := hsq2
    obtain ⟨v, hv, hDv⟩ := sq_of_cube_sq D hD0 c' hc' w' hcw'
    refine Or.inr ⟨v, c⁻¹ * c'⁻¹ ^ 2, 0, hv, ?_, by simp⟩
    rw [hAD, map_mul, map_pow, hDv, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
    simp only [map_mul, map_pow]; ring
  -- generic constant `j`
  obtain ⟨r, hr⟩ := hj.resolve_left hA |>.resolve_left hB
  obtain ⟨D, hAD, hBD⟩ := iso_normal_form A B hA hB r hr
  have hr0 : r ≠ 0 := by rintro rfl; simp at hAD; exact hA hAD
  have hD0 : D ≠ 0 := by rintro rfl; simp at hAD; exact hA hAD
  have hΔr : 4 * r ^ 3 + 27 * r ^ 2 ≠ 0 := by
    intro h; apply hΔ'; rw [hAD, hBD]
    have : 4 * (C r * D ^ 2) ^ 3 + 27 * (C r * D ^ 3) ^ 2 = C (4 * r ^ 3 + 27 * r ^ 2) * D ^ 6 := by
      simp only [map_add, map_mul, map_pow, map_ofNat]; ring
    rw [this, h, C_0, zero_mul]
  by_cases hsq : ∀ (c' : K) (w' : RatFunc K), c' ≠ 0 → κ c' * ι D ^ 3 ≠ w' ^ 2
  · exact Or.inl (Or.inr (Or.inr ⟨r, r, D, hD0, hΔr, hAD, hBD, hsq⟩))
  push_neg at hsq
  obtain ⟨c', w', hc', hcw'⟩ := hsq
  obtain ⟨v, hv, hDv⟩ := sq_of_cube_sq D hD0 c' hc' w' hcw'
  refine Or.inr ⟨v, r * c'⁻¹ ^ 2, r * c'⁻¹ ^ 3, hv, ?_, ?_⟩
  · rw [hAD, map_mul, map_pow, hDv, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
    simp only [map_mul, map_pow]; ring
  · rw [hBD, map_mul, map_pow, hDv, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
    simp only [map_mul, map_pow]; ring

end FFHeight


namespace FFHeight

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- **Descent for curves constant up to scaling**: on `y² = x³ + A x + B` with `A = u⁴ a`,
`B = u⁶ b` (`a, b ∈ K`), every point has `x / u²` constant (`weierstrass_const` on the scaled
constant curve). So the Mordell–Weil group is that of the constant curve over `K`. -/
theorem const_scale_descent {A B : K[X]} {u : RatFunc K} {a b : K} (hu : u ≠ 0)
    (hA : ι A = u ^ 4 * κ a) (hB : ι B = u ^ 6 * κ b) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (x y : RatFunc K) (h : y ^ 2 = x ^ 3 + ι A * x + ι B) : ∃ c : K, x / u ^ 2 = RatFunc.C c := by
  apply EllConst.weierstrass_const a b hΔ (x / u ^ 2) (y / u ^ 3)
  rw [hA, hB] at h
  rw [← RatFunc.algebraMap_eq_C]
  field_simp
  linear_combination h

/-- The discriminant of the scaled constant curve is non-zero. -/
theorem const_scale_disc {A B : K[X]} {u : RatFunc K} {a b : K} (hu : u ≠ 0)
    (hA : ι A = u ^ 4 * κ a) (hB : ι B = u ^ 6 * κ b) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  intro h0
  apply hΔ'
  apply hinj
  rw [map_zero, map_add, map_mul, map_mul, map_pow, map_pow, hA, hB, map_ofNat, map_ofNat]
  have : (4 : RatFunc K) * (u ^ 4 * κ a) ^ 3 + 27 * (u ^ 6 * κ b) ^ 2 =
      u ^ 12 * κ (4 * a ^ 3 + 27 * b ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]; ring
  rw [this, h0, map_zero, mul_zero]

end FFHeight


