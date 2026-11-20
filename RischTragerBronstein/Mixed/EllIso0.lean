import RischTragerBronstein.Mixed.EllIsoGen

/-!
# Exact canonical heights on `j = 0` twists: `y² = x³ + B`

On `s = x³ / B` the duplication map of `y² = x³ + B` is the constant-coefficient degree-`4` map
`s ↦ s (s − 8)³ / (64 (s + 1)³)`, so `gT0 P = ht (x(P)³ / B)` satisfies `gT0 (2P) = 4 gT0 P` and
`|3 hN − gT0| ≤ deg B`: **`canonH_eq_gT0`**, `canonH = gT0 / 3`. If `B` is not a constant times a
cube (the cubic and sextic twists), a point of canonical height `0` is torsion (`tors_of_canonH0`),
and the height certificate is complete (`hgap_exists_0`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- Duplication numerator on `x³ / B`. -/
noncomputable def dup0P : K[X] := X * (X - 8) ^ 3
/-- Duplication denominator on `x³ / B`. -/
noncomputable def dup0Q : K[X] := 64 * (X + 1) ^ 3

theorem dup0_coprime : IsCoprime (dup0P : K[X]) dup0Q := by
  have key : (2432 * X ^ 2 + 7168 * X + 6464) * (dup0P : K[X]) +
      (-38 * X ^ 3 + 914 * X ^ 2 - 7337 * X + 19683) * dup0Q = C 1259712 := by
    simp only [dup0P, dup0Q, map_ofNat]; ring
  have h0 : (1259712 : K) ≠ 0 := by norm_num
  refine ⟨C (1259712 : K)⁻¹ * (2432 * X ^ 2 + 7168 * X + 6464),
    C (1259712 : K)⁻¹ * (-38 * X ^ 3 + 914 * X ^ 2 - 7337 * X + 19683), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, key, ← C_mul, inv_mul_cancel₀ h0, C_1]

theorem dup0_deg : max (dup0P : K[X]).natDegree (dup0Q : K[X]).natDegree = 4 := by
  have h1 : (dup0P : K[X]).natDegree = 4 := by unfold dup0P; compute_degree!
  have h2 : (dup0Q : K[X]).natDegree ≤ 4 := by unfold dup0Q; compute_degree <;> norm_num
  omega

theorem ht_pow3 (x : RatFunc K) : ht (x ^ 3) = 3 * ht x := by
  have := ht_comp' (X ^ 3 : K[X]) 1 one_ne_zero isCoprime_one_right x
  simpa using this

/-- The `j = 0` coordinate height. -/
noncomputable def gT0 (B : K[X]) : (shortW 0 B).toAffine.Point → ℕ
  | .zero => 0
  | .some x _ _ => ht (x ^ 3 / ι B)

variable {B : K[X]}

theorem gT0_double (hB : B ≠ 0) (P : (shortW 0 B).toAffine.Point) :
    gT0 B (P + P) = 4 * gT0 B P := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hB' : ι B ≠ 0 := (map_ne_zero_iff _ hinj).mpr hB
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  have hb2 : (shortW 0 B).b₂ = 0 := by simp [WeierstrassCurve.b₂, shortW]
  have hb4 : (shortW 0 B).b₄ = 0 := by simp [WeierstrassCurve.b₄, shortW]
  have hb6 : (shortW 0 B).b₆ = 4 * ι B := by simp [WeierstrassCurve.b₆, shortW]
  have hb8 : (shortW 0 B).b₈ = 0 := by simp [WeierstrassCurve.b₈, shortW]
  set s := x ^ 3 / ι B with hs
  by_cases hy : y = (shortW 0 B).toAffine.negY x y
  · rw [Point.add_self_of_Y_eq hy]
    have hden := (den_duplication_eq_zero_iff h.1).mpr hy
    rw [hb2, hb4, hb6] at hden
    have hsc : s = κ (-1) := by
      rw [hs, div_eq_iff hB', map_neg, map_one]; linear_combination hden / 4
    show 0 = 4 * ht s
    rw [hsc, RatFunc.algebraMap_eq_C, ht_C, mul_zero]
  · rw [Point.add_self_of_Y_ne hy]
    have hden := (den_duplication_eq_zero_iff h.1).not.mpr hy
    have hx2 := addX_self_of_Y_ne h.1 hy
    rw [hb2, hb4, hb6, hb8] at hx2
    rw [hb2, hb4, hb6] at hden
    show ht ((shortW 0 B).toAffine.addX x x ((shortW 0 B).toAffine.slope x x y y) ^ 3 / ι B) =
      4 * ht s
    have hq : (dup0Q : K[X]).eval₂ κ s ≠ 0 := by
      simp only [dup0Q, eval₂_mul, eval₂_add, eval₂_pow, eval₂_X, eval₂_one, eval₂_ofNat]
      intro h0; apply hden
      have : (64 : RatFunc K) * (s + 1) ^ 3 = 0 := h0
      have h1 : s + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp
        ((mul_eq_zero.mp this).resolve_left (by norm_num))
      rw [hs, div_add_one hB', div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · linear_combination 4 * h1
      · exact absurd h1 hB'
    have heq : (shortW 0 B).toAffine.addX x x ((shortW 0 B).toAffine.slope x x y y) ^ 3 / ι B =
        (dup0P : K[X]).eval₂ κ s / (dup0Q : K[X]).eval₂ κ s := by
      rw [hx2, div_pow, div_div, div_eq_div_iff (mul_ne_zero (pow_ne_zero 3 hden) hB') hq]
      simp only [dup0P, dup0Q, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
        eval₂_ofNat]
      rw [hs]
      field_simp
      ring
    rw [heq, ht_comp' _ _ (fun h0 ↦ by simp [h0] at hq) dup0_coprime, dup0_deg]

theorem hN_gT0_close (hB : B ≠ 0) (P : (shortW 0 B).toAffine.Point) :
    |3 * (hN 0 B P : ℝ) - gT0 B P| ≤ B.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hB' : ι B ≠ 0 := (map_ne_zero_iff _ hinj).mpr hB
  rcases P with _ | ⟨x, y, h⟩
  · simp [hN, gT0]
  simp only [hN, gT0]
  have h1 : ht (x ^ 3) ≤ B.natDegree + ht (x ^ 3 / ι B) := by
    have := ht_mul_le (ι B) (x ^ 3 / ι B)
    rwa [mul_div_cancel₀ _ hB', ht_ι] at this
  have h2 : ht (x ^ 3 / ι B) ≤ ht (x ^ 3) + B.natDegree := by
    have := ht_mul_le (x ^ 3) (ι B)⁻¹
    rwa [← div_eq_mul_inv, ht_inv, ht_ι] at this
  rw [ht_pow3] at h1 h2
  rw [abs_le]
  constructor
  · have : (ht (x ^ 3 / ι B) : ℝ) ≤ 3 * ht x + B.natDegree := by exact_mod_cast h2
    linarith
  · have : (3 * ht x : ℝ) ≤ B.natDegree + ht (x ^ 3 / ι B) := by exact_mod_cast h1
    linarith

/-- **The canonical height on `y² = x³ + B` is `ht (x³ / B) / 3`.** -/
theorem canonH_eq_gT0 (hB : B ≠ 0) (hΔ' : 4 * (0 : K[X]) ^ 3 + 27 * B ^ 2 ≠ 0)
    (P : (shortW 0 B).toAffine.Point) : canonH 0 B P = gT0 B P / 3 := by
  symm
  refine MWTate.canon_unique (hR_double 0 B hΔ') (fun Q ↦ (gT0 B Q : ℝ) / 3) (B.natDegree / 3)
    (fun Q ↦ ?_) (fun Q ↦ ?_) P
  · show (gT0 B (Q + Q) : ℝ) / 3 = 4 * ((gT0 B Q : ℝ) / 3)
    rw [gT0_double hB]; push_cast; ring
  · have := hN_gT0_close hB Q
    simp only [hR]
    rw [abs_le] at this ⊢
    constructor <;> linarith [this.1, this.2]

/-- **Positivity** on `j = 0` twists: if `B` is not a constant times a cube, canonical height `0`
means torsion (`2`- or `3`-torsion). -/
theorem tors_of_canonH0 (hB : B ≠ 0) (hΔ' : 4 * (0 : K[X]) ^ 3 + 27 * B ^ 2 ≠ 0)
    (hcube : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι B ≠ w ^ 3)
    (P : (shortW 0 B).toAffine.Point) (h0 : canonH 0 B P = 0) : ∃ n : ℕ, 0 < n ∧ n • P = 0 := by
  rw [canonH_eq_gT0 hB hΔ'] at h0
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hB' : ι B ≠ 0 := (map_ne_zero_iff _ hinj).mpr hB
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨1, one_pos, by rw [one_nsmul]; rfl⟩
  have hg : gT0 B (Point.some x y h) = 0 := by
    have : (gT0 B (Point.some x y h) : ℝ) = 0 := by linarith
    exact_mod_cast this
  simp only [gT0] at hg
  set s := x ^ 3 / ι B with hs
  have hsc : s = κ (s.num.coeff 0 / s.denom.coeff 0) := by
    have hn : max s.num.natDegree s.denom.natDegree = 0 := hg
    have hu0 : s.num.natDegree = 0 := by omega
    have hv0 : s.denom.natDegree = 0 := by omega
    conv_lhs => rw [← RatFunc.num_div_denom s, eq_C_of_natDegree_eq_zero hu0,
      eq_C_of_natDegree_eq_zero hv0]
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀, RatFunc.algebraMap_eq_C]
  set c := s.num.coeff 0 / s.denom.coeff 0
  have hx3 : x ^ 3 = κ c * ι B := by rw [← hsc, hs]; field_simp
  have heq := h.1
  rw [equation_iff] at heq
  simp only [shortW, zero_mul, add_zero, map_zero] at heq
  have hy2 : y ^ 2 = κ (c + 1) * ι B := by rw [heq, hx3, map_add, map_one]; ring
  by_cases hc1 : c + 1 = 0
  · have hy : y = 0 := by
      rw [hc1, map_zero, zero_mul] at hy2; exact pow_eq_zero_iff (two_ne_zero) |>.mp hy2
    exact ⟨2, two_pos, by rw [two_nsmul]; exact Point.add_self_of_Y_eq (by rw [hy]; simp [negY, shortW])⟩
  by_cases hc0 : c = 0
  · -- `x = 0`: a point of order `3`
    have hx : x = 0 := by rw [hc0, map_zero, zero_mul] at hx3; exact pow_eq_zero_iff (by norm_num) |>.mp hx3
    subst hx
    have hy0 : y ≠ 0 := by
      intro hy; rw [hy, hc0, zero_add, map_one, one_mul] at hy2
      exact hB' (by rw [← hy2]; ring)
    have hyn : y ≠ (shortW 0 B).toAffine.negY 0 y := by
      simp only [negY, shortW, zero_mul, sub_zero]
      intro h'; apply hy0; linear_combination h' / 2
    have hsl : (shortW 0 B).toAffine.slope 0 0 y y = 0 := by
      rw [slope_of_Y_ne rfl hyn]; simp [shortW]
    have h2 : Point.some 0 y h + Point.some 0 y h = -Point.some 0 y h := by
      rw [Point.add_self_of_Y_ne hyn, Point.neg_some]
      simp only [Point.some.injEq, addX, addY, negAddY, negY, hsl]
      simp [shortW]
    refine ⟨3, by norm_num, ?_⟩
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul, h2, neg_add_cancel]
  · exact absurd hx3.symm (hcube c x hc0)

/-- **Completeness of the height certificate on `j = 0` twists.** -/
theorem hgap_exists_0 (hB : B ≠ 0) (hΔ' : 4 * (0 : K[X]) ^ 3 + 27 * B ^ 2 ≠ 0)
    (hcube : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι B ≠ w ^ 3)
    (P Q : (shortW 0 B).toAffine.Point) (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k : ℕ, let C : ℝ := 11 * (max (0 : K[X]).natDegree B.natDegree : ℕ)
      let h := hR 0 B
      let d := MWPair.dbl (G := (shortW 0 B).toAffine.Point)
      C / 3 / 4 ^ k * (|h (d^[k] P) / 4 ^ k| + |h (d^[k] Q) / 4 ^ k| + C / 3 / 4 ^ k) +
        3 * (C / 3 / 4 ^ k) / 2 * (|h (d^[k] (P + Q)) / 4 ^ k - h (d^[k] P) / 4 ^ k -
          h (d^[k] Q) / 4 ^ k| + 3 * (C / 3 / 4 ^ k) / 2) <
      |h (d^[k] P) / 4 ^ k * (h (d^[k] Q) / 4 ^ k) - ((h (d^[k] (P + Q)) / 4 ^ k -
          h (d^[k] P) / 4 ^ k - h (d^[k] Q) / 4 ^ k) / 2) ^ 2| :=
  hgap_exists_gen hΔ' 3 (by norm_num)
    (fun X ↦ ⟨gT0 B X, by rw [canonH_eq_gT0 hB hΔ']; ring⟩)
    (fun X hX ↦ tors_of_canonH0 hB hΔ' hcube X hX) P Q hind

end FFHeight
