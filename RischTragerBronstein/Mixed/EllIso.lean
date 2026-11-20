import RischTragerBronstein.Mixed.RatComp
import RischTragerBronstein.Mixed.EllNT

/-!
# Exact canonical heights on quadratic twists of constant curves

For `E : y² = x³ + A x + B` over `K(X)` with `A = a D²`, `B = b D³` (`a, b ∈ K`,
`4a³ + 27b² ≠ 0`): a quadratic twist of the constant curve `y² = x³ + a x + b` (constant
`j`-invariant). On the coordinate `s = x / D` the duplication map is the constant-coefficient
rational function `dupP / dupQ` of degree `4`, so by `ht_comp'` the function
`gTw P = ht (x(P) / D)` satisfies `gTw (2P) = 4 gTw P` exactly (`gTw_double`), and
`|hN − gTw| ≤ deg D`. Hence **`canonH_eq_gTw`: the canonical height is the natural number
`ht (x(P) / D)`**, and **`two_tors_of_canonH`**: if `D³` is not a constant times a square, a point
of canonical height `0` is `2`-torsion.

This is height *positivity* for these isotrivial curves (where the Manin map vanishes), by an
elementary argument (degrees of compositions), without the Lang–Néron theorem.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- Duplication numerator on the twist coordinate. -/
noncomputable def dupP (a b : K) : K[X] := X ^ 4 - 2 * C a * X ^ 2 - 8 * C b * X + C a ^ 2
/-- Duplication denominator on the twist coordinate. -/
noncomputable def dupQ (a b : K) : K[X] := C 4 * (X ^ 3 + C a * X + C b)

theorem dup_coprime (a b : K) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : IsCoprime (dupP a b) (dupQ a b) := by
  have key : (12 * X ^ 2 + 16 * C a) * dupP a b +
      (-3 * X ^ 3 + 5 * C a * X + 27 * C b) * dupQ a b =
      C (4 * (4 * a ^ 3 + 27 * b ^ 2)) := by
    simp only [dupP, dupQ, map_add, map_mul, map_pow, map_ofNat]
    ring
  have h4 : (4 * (4 * a ^ 3 + 27 * b ^ 2) : K) ≠ 0 := mul_ne_zero (by norm_num) hΔ
  refine ⟨C (4 * (4 * a ^ 3 + 27 * b ^ 2))⁻¹ * (12 * X ^ 2 + 16 * C a),
    C (4 * (4 * a ^ 3 + 27 * b ^ 2))⁻¹ * (-3 * X ^ 3 + 5 * C a * X + 27 * C b), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, key, ← C_mul, inv_mul_cancel₀ h4, C_1]

theorem dup_deg (a b : K) : max (dupP a b).natDegree (dupQ a b).natDegree = 4 := by
  have h1 : (dupP a b).natDegree = 4 := by unfold dupP; compute_degree!
  have h2 : (dupQ a b).natDegree ≤ 4 := by unfold dupQ; compute_degree <;> norm_num
  omega

/-- The cubic `X³ + a X + b`. -/
noncomputable def cubQ (a b : K) : K[X] := X ^ 3 + C a * X + C b

theorem cub_deg (a b : K) : (cubQ a b).natDegree = 3 := by unfold cubQ; compute_degree!

/-- A root in `K(X)` of a non-zero constant-coefficient cubic is constant. -/
theorem ht_root_cub (a b : K) (s : RatFunc K) (h : (cubQ a b).eval₂ κ s = 0) : ht s = 0 := by
  have := ht_comp' (cubQ a b) 1 one_ne_zero isCoprime_one_right s
  rw [h, zero_div, ht_zero, cub_deg, natDegree_one, max_eq_left (by norm_num)] at this
  omega

/-- The twist-coordinate height. -/
noncomputable def gTw (A B D : K[X]) : (shortW A B).toAffine.Point → ℕ
  | .zero => 0
  | .some x _ _ => ht (x / ι D)

theorem ht_ι (p : K[X]) : ht (ι p) = p.natDegree := by
  have := ht_div_coprime p 1 one_ne_zero isCoprime_one_right
  rw [map_one, div_one, natDegree_one, max_eq_left (Nat.zero_le _)] at this
  exact this

variable {A B D : K[X]} {a b : K}

theorem gTw_double (hD : D ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hA : A = C a * D ^ 2)
    (hB : B = C b * D ^ 3) (P : (shortW A B).toAffine.Point) :
    gTw A B D (P + P) = 4 * gTw A B D P := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hD' : ι D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hAι : ι A = κ a * ι D ^ 2 := by rw [hA, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
  have hBι : ι B = κ b * ι D ^ 3 := by rw [hB, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  have hb2 : (shortW A B).b₂ = 0 := by simp [WeierstrassCurve.b₂, shortW]
  have hb4 : (shortW A B).b₄ = 2 * ι A := by simp [WeierstrassCurve.b₄, shortW]
  have hb6 : (shortW A B).b₆ = 4 * ι B := by simp [WeierstrassCurve.b₆, shortW]
  have hb8 : (shortW A B).b₈ = -(ι A) ^ 2 := by simp [WeierstrassCurve.b₈, shortW]
  set s := x / ι D with hs
  have hx : x = ι D * s := by rw [hs]; field_simp
  by_cases hy : y = (shortW A B).toAffine.negY x y
  · rw [Point.add_self_of_Y_eq hy]
    have hden := (den_duplication_eq_zero_iff h.1).mpr hy
    rw [hb2, hb4, hb6] at hden
    have hc : (cubQ a b).eval₂ κ s = 0 := by
      simp only [cubQ, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
      have : 4 * ι D ^ 3 * (s ^ 3 + κ a * s + κ b) = 0 := by
        rw [← hden, hx, hAι, hBι]; ring
      have h4 : (4 : RatFunc K) * ι D ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hD')
      exact (mul_eq_zero.mp this).resolve_left h4
    show 0 = 4 * ht s
    rw [ht_root_cub a b s hc]
  · rw [Point.add_self_of_Y_ne hy]
    have hden := (den_duplication_eq_zero_iff h.1).not.mpr hy
    have hx2 := addX_self_of_Y_ne h.1 hy
    rw [hb2, hb4, hb6, hb8] at hx2
    rw [hb2, hb4, hb6] at hden
    show ht ((shortW A B).toAffine.addX x x ((shortW A B).toAffine.slope x x y y) / ι D) =
      4 * ht s
    have hq : (dupQ a b).eval₂ κ s ≠ 0 := by
      intro h0; apply hden
      rw [hx, hAι, hBι]
      simp only [dupQ, eval₂_mul, eval₂_add, eval₂_pow, eval₂_X, eval₂_C, eval₂_ofNat,
        map_ofNat] at h0
      linear_combination ι D ^ 3 * h0
    have heq : (shortW A B).toAffine.addX x x ((shortW A B).toAffine.slope x x y y) / ι D =
        (dupP a b).eval₂ κ s / (dupQ a b).eval₂ κ s := by
      rw [hx2, div_div, div_eq_div_iff (mul_ne_zero hden hD') hq]
      simp only [dupP, dupQ, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
        eval₂_ofNat, map_ofNat]
      rw [hx, hAι, hBι]
      ring
    rw [heq, ht_comp' _ _ (fun h0 ↦ by simp [h0] at hq) (dup_coprime a b hΔ), dup_deg]

theorem hN_gTw_close (hD : D ≠ 0) (P : (shortW A B).toAffine.Point) :
    |(hN A B P : ℝ) - gTw A B D P| ≤ D.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hD' : ι D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  rcases P with _ | ⟨x, y, h⟩
  · simp [hN, gTw]
  simp only [hN, gTw]
  have h1 : ht x ≤ D.natDegree + ht (x / ι D) := by
    have := ht_mul_le (ι D) (x / ι D)
    rwa [mul_div_cancel₀ _ hD', ht_ι] at this
  have h2 : ht (x / ι D) ≤ ht x + D.natDegree := by
    have := ht_mul_le x (ι D)⁻¹
    rwa [← div_eq_mul_inv, ht_inv, ht_ι] at this
  rw [abs_le]
  constructor
  · have : (ht (x / ι D) : ℝ) ≤ ht x + D.natDegree := by exact_mod_cast h2
    linarith
  · have : (ht x : ℝ) ≤ D.natDegree + ht (x / ι D) := by exact_mod_cast h1
    linarith

/-- **The canonical height on a quadratic twist of a constant curve is `ht (x / D)`.** -/
theorem canonH_eq_gTw (hD : D ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hA : A = C a * D ^ 2)
    (hB : B = C b * D ^ 3) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (P : (shortW A B).toAffine.Point) :
    canonH A B P = gTw A B D P := by
  symm
  refine MWTate.canon_unique (hR_double A B hΔ') (fun Q ↦ (gTw A B D Q : ℝ)) D.natDegree
    (fun Q ↦ ?_) (fun Q ↦ ?_) P
  · show (gTw A B D (Q + Q) : ℝ) = 4 * gTw A B D Q
    rw [gTw_double hD hΔ hA hB]; push_cast; ring
  · have := hN_gTw_close (A := A) (B := B) hD Q
    rw [abs_sub_comm]; exact this

/-- **Positivity**: if `D³` is not a constant times a square in `K(X)`, a point of canonical
height `0` is `2`-torsion. -/
theorem two_tors_of_canonH (hD : D ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hA : A = C a * D ^ 2)
    (hB : B = C b * D ^ 3) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι D ^ 3 ≠ w ^ 2)
    (P : (shortW A B).toAffine.Point) (h0 : canonH A B P = 0) : P + P = 0 := by
  rw [canonH_eq_gTw hD hΔ hA hB hΔ'] at h0
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hD' : ι D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  simp only [gTw, Nat.cast_eq_zero] at h0
  -- `x / D` is a constant `c₀`
  set s := x / ι D with hs
  have hsc : s = κ (s.num.coeff 0 / s.denom.coeff 0) := by
    have hn : max s.num.natDegree s.denom.natDegree = 0 := h0
    have hu0 : s.num.natDegree = 0 := by omega
    have hv0 : s.denom.natDegree = 0 := by omega
    conv_lhs => rw [← RatFunc.num_div_denom s, eq_C_of_natDegree_eq_zero hu0,
      eq_C_of_natDegree_eq_zero hv0]
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀, RatFunc.algebraMap_eq_C]
  set c₀ := s.num.coeff 0 / s.denom.coeff 0
  have hx : x = κ c₀ * ι D := by rw [← hsc, hs]; field_simp
  have heq := h.1
  rw [equation_iff] at heq
  simp only [shortW, zero_mul, add_zero, zero_add] at heq
  have hAι : ι A = κ a * ι D ^ 2 := by rw [hA, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
  have hBι : ι B = κ b * ι D ^ 3 := by rw [hB, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
  rw [hx, hAι, hBι] at heq
  have hy2 : y ^ 2 = κ (c₀ ^ 3 + a * c₀ + b) * ι D ^ 3 := by
    rw [heq]; simp only [map_add, map_mul, map_pow]; ring
  by_cases hc : c₀ ^ 3 + a * c₀ + b = 0
  · have hy : y = 0 := by rw [hc, map_zero, zero_mul] at hy2; exact pow_eq_zero_iff (two_ne_zero) |>.mp hy2
    exact Point.add_self_of_Y_eq (by rw [hy]; simp [negY, shortW])
  · exact absurd hy2.symm (hsq _ y hc)

end FFHeight

