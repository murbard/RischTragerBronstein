import RischTragerBronstein.Mixed.EllIso0

/-!
# Exact canonical heights on `j = 1728` twists: `y² = x³ + A x`

On `s = x² / A` the duplication map is `s ↦ (s − 1)⁴ / (16 s (s + 1)²)` (constant coefficients,
degree `4`), so `gT1 P = ht (x(P)² / A)` satisfies `gT1 (2P) = 4 gT1 P` and `|2 hN − gT1| ≤ deg A`:
**`canonH_eq_gT1`**, `canonH = gT1 / 2`. If `A` is not a constant times a square (quartic twists;
the square case is a quadratic twist, `EllIso`), canonical height `0` means `2`-torsion
(`tors_of_canonH1`), and the height certificate is complete (`hgap_exists_1728`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- Duplication numerator on `x² / A`. -/
noncomputable def dup1P : K[X] := (X - 1) ^ 4
/-- Duplication denominator on `x² / A`. -/
noncomputable def dup1Q : K[X] := 16 * X * (X + 1) ^ 2

theorem dup1_coprime : IsCoprime (dup1P : K[X]) dup1Q := by
  have key : (208 * X ^ 2 + 448 * X + 256) * (dup1P : K[X]) +
      (-13 * X ^ 3 + 50 * X ^ 2 - 69 * X + 36) * dup1Q = C 256 := by
    simp only [dup1P, dup1Q, map_ofNat]; ring
  have h0 : (256 : K) ≠ 0 := by norm_num
  refine ⟨C (256 : K)⁻¹ * (208 * X ^ 2 + 448 * X + 256),
    C (256 : K)⁻¹ * (-13 * X ^ 3 + 50 * X ^ 2 - 69 * X + 36), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, key, ← C_mul, inv_mul_cancel₀ h0, C_1]

theorem dup1_deg : max (dup1P : K[X]).natDegree (dup1Q : K[X]).natDegree = 4 := by
  have h1 : (dup1P : K[X]).natDegree = 4 := by unfold dup1P; compute_degree!
  have h2 : (dup1Q : K[X]).natDegree ≤ 4 := by unfold dup1Q; compute_degree <;> norm_num
  omega

theorem ht_pow2 (x : RatFunc K) : ht (x ^ 2) = 2 * ht x := by
  have := ht_comp' (X ^ 2 : K[X]) 1 one_ne_zero isCoprime_one_right x
  simpa using this

/-- The `j = 1728` coordinate height. -/
noncomputable def gT1 (A : K[X]) : (shortW A 0).toAffine.Point → ℕ
  | .zero => 0
  | .some x _ _ => ht (x ^ 2 / ι A)

variable {A : K[X]}

theorem ht_const (c : K) : ht (κ c) = 0 := by rw [RatFunc.algebraMap_eq_C, ht_C]

theorem gT1_double (hA : A ≠ 0) (P : (shortW A 0).toAffine.Point) :
    gT1 A (P + P) = 4 * gT1 A P := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hA' : ι A ≠ 0 := (map_ne_zero_iff _ hinj).mpr hA
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  have hb2 : (shortW A 0).b₂ = 0 := by simp [WeierstrassCurve.b₂, shortW]
  have hb4 : (shortW A 0).b₄ = 2 * ι A := by simp [WeierstrassCurve.b₄, shortW]
  have hb6 : (shortW A 0).b₆ = 0 := by simp [WeierstrassCurve.b₆, shortW]
  have hb8 : (shortW A 0).b₈ = -(ι A) ^ 2 := by simp [WeierstrassCurve.b₈, shortW]
  set s := x ^ 2 / ι A with hs
  by_cases hy : y = (shortW A 0).toAffine.negY x y
  · rw [Point.add_self_of_Y_eq hy]
    have hden := (den_duplication_eq_zero_iff h.1).mpr hy
    rw [hb2, hb4, hb6] at hden
    show 0 = 4 * ht s
    have h' : x * (x ^ 2 + ι A) = 0 := by linear_combination hden / 4
    rcases mul_eq_zero.mp h' with hx | hx
    · rw [hs, hx]; simp [ht_zero]
    · have : s = κ (-1) := by rw [hs, div_eq_iff hA', map_neg, map_one]; linear_combination hx
      rw [this, ht_const, mul_zero]
  · rw [Point.add_self_of_Y_ne hy]
    have hden := (den_duplication_eq_zero_iff h.1).not.mpr hy
    have hx2 := addX_self_of_Y_ne h.1 hy
    rw [hb2, hb4, hb6, hb8] at hx2
    rw [hb2, hb4, hb6] at hden
    show ht ((shortW A 0).toAffine.addX x x ((shortW A 0).toAffine.slope x x y y) ^ 2 / ι A) =
      4 * ht s
    have hx0 : x ≠ 0 := by intro h0; apply hden; rw [h0]; ring
    have hxA : x ^ 2 + ι A ≠ 0 := by intro h0; apply hden; linear_combination 4 * x * h0
    have hq : (dup1Q : K[X]).eval₂ κ s ≠ 0 := by
      simp only [dup1Q, eval₂_mul, eval₂_add, eval₂_pow, eval₂_X, eval₂_one, eval₂_ofNat]
      have hs0 : s ≠ 0 := div_ne_zero (pow_ne_zero 2 hx0) hA'
      have hs1 : s + 1 ≠ 0 := by rw [hs, div_add_one hA']; exact div_ne_zero hxA hA'
      exact mul_ne_zero (mul_ne_zero (by norm_num) hs0) (pow_ne_zero 2 hs1)
    have heq : (shortW A 0).toAffine.addX x x ((shortW A 0).toAffine.slope x x y y) ^ 2 / ι A =
        (dup1P : K[X]).eval₂ κ s / (dup1Q : K[X]).eval₂ κ s := by
      rw [hx2, div_pow, div_div, div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hden) hA') hq]
      simp only [dup1P, dup1Q, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
        eval₂_ofNat]
      rw [hs]
      field_simp
      ring
    rw [heq, ht_comp' _ _ (fun h0 ↦ by simp [h0] at hq) dup1_coprime, dup1_deg]

theorem hN_gT1_close (hA : A ≠ 0) (P : (shortW A 0).toAffine.Point) :
    |2 * (hN A 0 P : ℝ) - gT1 A P| ≤ A.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hA' : ι A ≠ 0 := (map_ne_zero_iff _ hinj).mpr hA
  rcases P with _ | ⟨x, y, h⟩
  · simp [hN, gT1]
  simp only [hN, gT1]
  have h1 : ht (x ^ 2) ≤ A.natDegree + ht (x ^ 2 / ι A) := by
    have := ht_mul_le (ι A) (x ^ 2 / ι A)
    rwa [mul_div_cancel₀ _ hA', ht_ι] at this
  have h2 : ht (x ^ 2 / ι A) ≤ ht (x ^ 2) + A.natDegree := by
    have := ht_mul_le (x ^ 2) (ι A)⁻¹
    rwa [← div_eq_mul_inv, ht_inv, ht_ι] at this
  rw [ht_pow2] at h1 h2
  rw [abs_le]
  constructor
  · have : (ht (x ^ 2 / ι A) : ℝ) ≤ 2 * ht x + A.natDegree := by exact_mod_cast h2
    linarith
  · have : (2 * ht x : ℝ) ≤ A.natDegree + ht (x ^ 2 / ι A) := by exact_mod_cast h1
    linarith

/-- **The canonical height on `y² = x³ + A x` is `ht (x² / A) / 2`.** -/
theorem canonH_eq_gT1 (hA : A ≠ 0) (hΔ' : 4 * A ^ 3 + 27 * (0 : K[X]) ^ 2 ≠ 0)
    (P : (shortW A 0).toAffine.Point) : canonH A 0 P = gT1 A P / 2 := by
  symm
  refine MWTate.canon_unique (hR_double A 0 hΔ') (fun Q ↦ (gT1 A Q : ℝ) / 2) (A.natDegree / 2)
    (fun Q ↦ ?_) (fun Q ↦ ?_) P
  · show (gT1 A (Q + Q) : ℝ) / 2 = 4 * ((gT1 A Q : ℝ) / 2)
    rw [gT1_double hA]; push_cast; ring
  · have := hN_gT1_close hA Q
    simp only [hR]
    rw [abs_le] at this ⊢
    constructor <;> linarith [this.1, this.2]

/-- **Positivity** on `j = 1728` twists: if `A` is not a constant times a square, canonical
height `0` means `2`-torsion. -/
theorem tors_of_canonH1 (hA : A ≠ 0) (hΔ' : 4 * A ^ 3 + 27 * (0 : K[X]) ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι A ≠ w ^ 2)
    (P : (shortW A 0).toAffine.Point) (h0 : canonH A 0 P = 0) : ∃ n : ℕ, 0 < n ∧ n • P = 0 := by
  rw [canonH_eq_gT1 hA hΔ'] at h0
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hA' : ι A ≠ 0 := (map_ne_zero_iff _ hinj).mpr hA
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨1, one_pos, by rw [one_nsmul]; rfl⟩
  have hg : gT1 A (Point.some x y h) = 0 := by
    have : (gT1 A (Point.some x y h) : ℝ) = 0 := by linarith
    exact_mod_cast this
  simp only [gT1] at hg
  set s := x ^ 2 / ι A with hs
  have hsc : s = κ (s.num.coeff 0 / s.denom.coeff 0) := by
    have hn : max s.num.natDegree s.denom.natDegree = 0 := hg
    have hu0 : s.num.natDegree = 0 := by omega
    have hv0 : s.denom.natDegree = 0 := by omega
    conv_lhs => rw [← RatFunc.num_div_denom s, eq_C_of_natDegree_eq_zero hu0,
      eq_C_of_natDegree_eq_zero hv0]
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀, RatFunc.algebraMap_eq_C]
  set c := s.num.coeff 0 / s.denom.coeff 0
  have hx2 : x ^ 2 = κ c * ι A := by rw [← hsc, hs]; field_simp
  have heq := h.1
  rw [equation_iff] at heq
  simp only [shortW, zero_mul, add_zero, map_zero] at heq
  have two : (2 : ℕ) • Point.some x y h = 0 → ∃ n : ℕ, 0 < n ∧ n • Point.some x y h = 0 :=
    fun h2 ↦ ⟨2, two_pos, h2⟩
  have tors_of_y0 : y = 0 → ∃ n : ℕ, 0 < n ∧ n • Point.some x y h = 0 := fun hy ↦
    two (by rw [two_nsmul]; exact Point.add_self_of_Y_eq (by rw [hy]; simp [negY, shortW]))
  by_cases hc0 : c = 0
  · apply tors_of_y0
    have hx : x = 0 := by rw [hc0, map_zero, zero_mul] at hx2; exact pow_eq_zero_iff (by norm_num) |>.mp hx2
    rw [hx] at heq
    have : y ^ 2 = 0 := by rw [heq]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  by_cases hc1 : c + 1 = 0
  · apply tors_of_y0
    have : y ^ 2 = x * (κ (c + 1) * ι A) := by rw [heq, map_add, map_one]; linear_combination x * hx2
    rw [hc1, map_zero, zero_mul, mul_zero] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  · exact absurd hx2.symm (hsq c x hc0)

/-- **Completeness of the height certificate on `j = 1728` twists.** -/
theorem hgap_exists_1728 (hA : A ≠ 0) (hΔ' : 4 * A ^ 3 + 27 * (0 : K[X]) ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι A ≠ w ^ 2)
    (P Q : (shortW A 0).toAffine.Point) (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k : ℕ, let C : ℝ := 11 * (max A.natDegree (0 : K[X]).natDegree : ℕ)
      let h := hR A 0
      let d := MWPair.dbl (G := (shortW A 0).toAffine.Point)
      C / 3 / 4 ^ k * (|h (d^[k] P) / 4 ^ k| + |h (d^[k] Q) / 4 ^ k| + C / 3 / 4 ^ k) +
        3 * (C / 3 / 4 ^ k) / 2 * (|h (d^[k] (P + Q)) / 4 ^ k - h (d^[k] P) / 4 ^ k -
          h (d^[k] Q) / 4 ^ k| + 3 * (C / 3 / 4 ^ k) / 2) <
      |h (d^[k] P) / 4 ^ k * (h (d^[k] Q) / 4 ^ k) - ((h (d^[k] (P + Q)) / 4 ^ k -
          h (d^[k] P) / 4 ^ k - h (d^[k] Q) / 4 ^ k) / 2) ^ 2| :=
  hgap_exists_gen hΔ' 2 (by norm_num)
    (fun X ↦ ⟨gT1 A X, by rw [canonH_eq_gT1 hA hΔ']; ring⟩)
    (fun X hX ↦ tors_of_canonH1 hA hΔ' hsq X hX) P Q hind

end FFHeight

