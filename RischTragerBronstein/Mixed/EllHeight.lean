import RischTragerBronstein.Mixed.EllDup
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The naive height on an elliptic curve over `K(X)`: doubling

For `E : y² = x³ + A x + B` over `K(X)` (`A, B ∈ K[X]`, `4A³ + 27B² ≠ 0`), the naive height of a
point is `hN P = ht (x P)` (`0` at the origin). **`hN_double`**: with `D = max (deg A) (deg B)`,
`4 hN P ≤ hN (2P) + 11 D` and `hN (2P) ≤ 4 hN P + 2 D`, on Mathlib's group `W.Point`.
This is the bounded doubling defect of `MWTate`, for the actual group law.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

/-- The short Weierstrass curve `y² = x³ + A x + B` over `K(X)`. -/
noncomputable def shortW (A B : K[X]) : WeierstrassCurve (RatFunc K) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := algebraMap K[X] (RatFunc K) A
  a₆ := algebraMap K[X] (RatFunc K) B

/-- The naive height of a point. -/
noncomputable def hN (A B : K[X]) : (shortW A B).toAffine.Point → ℕ
  | .zero => 0
  | .some x _ _ => ht x

local notation "ι" => algebraMap K[X] (RatFunc K)

omit [CharZero K] in
lemma ht_root_cubic (A B u v : K[X]) (hc : IsCoprime u v)
    (h : u ^ 3 + A * u * v ^ 2 + B * v ^ 3 = 0) :
    4 * max u.natDegree v.natDegree ≤ 2 * max A.natDegree B.natDegree := by
  have hvu : v ∣ u ^ 3 := ⟨-(A * u * v + B * v ^ 2), by linear_combination h⟩
  have hvunit : IsUnit v := (hc.pow_left (m := 3)).symm.isUnit_of_dvd' (dvd_refl v) hvu
  have hv0 : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hvunit
  rw [hv0]
  by_cases hu : u = 0
  · rw [hu]; simp
  have e : u ^ 3 = -(A * u * v ^ 2 + B * v ^ 3) := by linear_combination h
  have h1 : (u ^ 3).natDegree = 3 * u.natDegree := by rw [natDegree_pow]
  have h2 : (-(A * u * v ^ 2 + B * v ^ 3)).natDegree ≤
      max (A.natDegree + u.natDegree) B.natDegree := by
    rw [natDegree_neg]
    refine (natDegree_add_le _ _).trans (max_le_max ?_ ?_)
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_pow, hv0, mul_zero, add_zero]; exact natDegree_mul_le
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_pow, hv0, mul_zero, add_zero]
  rw [e] at h1
  have := le_max_left A.natDegree B.natDegree
  have := le_max_right A.natDegree B.natDegree
  omega

/-- **The doubling estimate on the group of points.** -/
theorem hN_double (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (P : (shortW A B).toAffine.Point) :
    4 * hN A B P ≤ hN A B (P + P) + 11 * max A.natDegree B.natDegree ∧
      hN A B (P + P) ≤ 4 * hN A B P + 2 * max A.natDegree B.natDegree := by
  rcases P with _ | ⟨x, y, h⟩
  · have e : (Point.zero : (shortW A B).toAffine.Point) + Point.zero = Point.zero := rfl
    simp [e, hN]
  set u := RatFunc.num x
  set v := RatFunc.denom x
  have hv : v ≠ 0 := RatFunc.denom_ne_zero x
  have hc : IsCoprime u v := RatFunc.isCoprime_num_denom x
  have hx : x = ι u / ι v := (RatFunc.num_div_denom x).symm
  have hιv : ι v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hv
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hhtx : ht x = max u.natDegree v.natDegree := by rw [hx]; exact ht_div_coprime u v hv hc
  have hb2 : (shortW A B).b₂ = 0 := by simp [WeierstrassCurve.b₂, shortW]
  have hb4 : (shortW A B).b₄ = 2 * ι A := by simp [WeierstrassCurve.b₄, shortW]
  have hb6 : (shortW A B).b₆ = 4 * ι B := by simp [WeierstrassCurve.b₆, shortW]
  have hb8 : (shortW A B).b₈ = -(ι A) ^ 2 := by simp [WeierstrassCurve.b₈, shortW]
  by_cases hy : y = (shortW A B).toAffine.negY x y
  · -- `2P = 0`: `x` is a root of `x³ + A x + B`
    rw [Point.add_self_of_Y_eq hy]
    have hden := (den_duplication_eq_zero_iff h.1).mpr hy
    rw [hb2, hb4, hb6, hx] at hden
    have hpoly : u ^ 3 + A * u * v ^ 2 + B * v ^ 3 = 0 := by
      apply hinj
      rw [map_zero]
      have : ι (u ^ 3 + A * u * v ^ 2 + B * v ^ 3) =
          (ι v) ^ 3 / 4 * (4 * (ι u / ι v) ^ 3 + 0 * (ι u / ι v) ^ 2 + 2 * (2 * ι A) * (ι u / ι v) +
            4 * ι B) := by
        simp only [map_add, map_mul, map_pow]; field_simp; ring
      rw [this, hden, mul_zero]
    have := ht_root_cubic A B u v hc hpoly
    simp only [hN, hhtx]
    omega
  · rw [Point.add_self_of_Y_ne hy]
    have hden := (den_duplication_eq_zero_iff h.1).not.mpr hy
    have hx2 := addX_self_of_Y_ne h.1 hy
    rw [hb2, hb4, hb6, hb8] at hx2
    rw [hb2, hb4, hb6] at hden
    -- the homogeneous forms
    have hphi : ι (WE.ev A B u v phiE) = (ι v) ^ 4 *
        ((ι u / ι v) ^ 4 - 2 * ι A * (ι u / ι v) ^ 2 - 2 * (4 * ι B) * (ι u / ι v) - -(ι A) ^ 2) := by
      simp only [WE.ev, phiE, map_add, map_sub, map_mul, map_pow, map_intCast]
      field_simp; push_cast; ring
    have hpsi : ι (WE.ev A B u v psiE) = (ι v) ^ 4 *
        (4 * (ι u / ι v) ^ 3 + 0 * (ι u / ι v) ^ 2 + 2 * (2 * ι A) * (ι u / ι v) + 4 * ι B) := by
      simp only [WE.ev, psiE, map_add, map_mul, map_pow, map_intCast]
      field_simp; push_cast; ring
    rw [hx] at hden hx2
    have hψ : WE.ev A B u v psiE ≠ 0 := by
      intro h0
      have := congrArg ι h0
      rw [hpsi, map_zero] at this
      exact mul_ne_zero (pow_ne_zero 4 hιv) hden this
    have hΔ' : WE.ev A B u v deltaE ≠ 0 := by
      simp only [WE.ev, deltaE]; push_cast; exact hΔ
    have hx2' : (shortW A B).toAffine.addX x x ((shortW A B).toAffine.slope x x y y) =
        ι (WE.ev A B u v phiE) / ι (WE.ev A B u v psiE) := by
      rw [hphi, hpsi, mul_div_mul_left _ _ (pow_ne_zero 4 hιv)]
      conv_lhs => rw [hx]
      exact hx2
    obtain ⟨h1, h2⟩ := dup_height A B u v hc hv hΔ' hψ
    simp only [hN]
    rw [hx2', hhtx]
    rw [ht_div_coprime u v hv hc] at h1 h2
    exact ⟨h1, h2⟩

end FFHeight
