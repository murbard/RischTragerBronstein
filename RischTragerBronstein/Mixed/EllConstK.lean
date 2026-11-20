import RischTragerBronstein.Mixed.KXCertBridgeCK

/-!
# Points with rational coordinates on constant curves over `K(X)`

For any field `K` of characteristic zero: the curve `y² = x³ + a x + b` (`a, b ∈ ℤ`) over `K(X)` is the
base change of `E/ℚ` (`qW_baseChangeK`), `E(ℚ) ↪ E(K(X))` (`ιQK`), so a point with rational
coordinates of infinite order (`QHeight.certH`) has infinite order over `K(X)` (`nontors_constK`),
and two independent ones stay independent (`indep_constK`). Used for constant curves at the levels
`m + 1` (`K = Kₘ`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

lemma qW_baseChangeK (a b : ℤ) :
    ((QHeight.qW a b).toAffine⁄(RatFunc K)) =
      (shortW (Polynomial.C (a : K)) (Polynomial.C (b : K))).toAffine := by
  simp [QHeight.qW, shortW, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    RatFunc.algebraMap_C]

/-- **The embedding** `E(ℚ) → E(K(x))`. -/
noncomputable def ιQK (a b : ℤ) :
    (QHeight.qW a b).toAffine.Point →+
      (shortW (Polynomial.C (a : K)) (Polynomial.C (b : K))).toAffine.Point :=
  have hself : (QHeight.qW a b).toAffine = ((QHeight.qW a b).toAffine⁄ℚ) := by
    simp [QHeight.qW, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  (castHom (qW_baseChangeK a b)).comp
    ((Point.map (W' := (QHeight.qW a b).toAffine) (Algebra.ofId ℚ (RatFunc K))).comp
      (castHom hself))

lemma ιQK_injective (a b : ℤ) : Function.Injective (ιQK (K := K) a b) :=
  (castHom_injective _).comp ((Point.map_injective _).comp (castHom_injective _))

lemma shortW_mapK (a b : ℤ) :
    (shortW (Polynomial.C (a : K)) (Polynomial.C (b : K))).toAffine =
      (QHeight.qW a b).toAffine.map (algebraMap ℚ (RatFunc K)) := by
  rw [← qW_baseChangeK]; rfl

lemma ιQK_some (a b : ℤ) (x y : ℚ) (h : (QHeight.qW a b).toAffine.Nonsingular x y) :
    ∃ h', ιQK (K := K) a b (Point.some x y h) =
      Point.some (algebraMap ℚ (RatFunc K) x) (algebraMap ℚ (RatFunc K) y) h' := by
  unfold ιQK
  simp only [AddMonoidHom.comp_apply]
  erw [castHom_some]
  refine ⟨?w, ?e⟩
  case e => rfl
  case w =>
    rw [shortW_mapK]
    exact (Affine.map_nonsingular (W := (QHeight.qW a b).toAffine)
      (algebraMap ℚ (RatFunc K)).injective x y).mpr h

variable [DecidableEq K]

/-- **Rational points come from `E(ℚ)`.** -/
theorem const_pointK (a b : ℤ) (fx fy : Fr K) (x0 y0 : ℚ)
    (hx : Fr.val fx = algebraMap ℚ (RatFunc K) x0) (hy : Fr.val fy = algebraMap ℚ (RatFunc K) y0)
    (A B : K[X]) (hA : A = Polynomial.C (a : K)) (hB : B = Polynomial.C (b : K))
    (PD : (shortW A B).toAffine.Point) (hR : Rel _ _ (some (fx, fy)) PD) :
    ∃ h0 : (QHeight.qW a b).toAffine.Nonsingular x0 y0,
      castHom (by rw [hA, hB]) PD = ιQK a b (Point.some _ _ h0) := by
  subst hA hB
  rcases PD with _ | ⟨X, Y, hXY⟩
  · exact absurd hR (by simp [Rel])
  obtain ⟨-, -, hX, hY⟩ := hR
  have eX : X = algebraMap ℚ (RatFunc K) x0 := by rw [← hX, hx]
  have eY : Y = algebraMap ℚ (RatFunc K) y0 := by rw [← hY, hy]
  subst eX eY
  have h0 : (QHeight.qW a b).toAffine.Nonsingular x0 y0 := by
    have := hXY
    rw [shortW_mapK] at this
    exact (Affine.map_nonsingular (W := (QHeight.qW a b).toAffine)
      (algebraMap ℚ (RatFunc K)).injective _ _).mp this
  obtain ⟨h1, e1⟩ := ιQK_some (K := K) a b _ _ h0
  refine ⟨h0, ?_⟩
  rw [e1]
  rfl

/-- **Rational points of infinite order.** -/
theorem nontors_constK (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (k : ℕ) (fx fy : Fr K)
    (x0 y0 : ℚ) (hx : Fr.val fx = algebraMap ℚ (RatFunc K) x0)
    (hy : Fr.val fy = algebraMap ℚ (RatFunc K) y0) (hc : QHeight.certH a b k x0 = true)
    (A B : K[X]) (hA : A = Polynomial.C (a : K)) (hB : B = Polynomial.C (b : K))
    (PD : (shortW A B).toAffine.Point)
    (hR : Rel _ _ (some (fx, fy)) PD) (n : ℤ) (hn : n • PD = 0) : n = 0 := by
  obtain ⟨h0, e0⟩ := const_pointK a b fx fy x0 y0 hx hy A B hA hB PD hR
  have := congrArg (castHom (by rw [hA, hB] : (shortW A B).toAffine =
    (shortW (Polynomial.C (a : K)) (Polynomial.C (b : K))).toAffine)) hn
  rw [map_zsmul, e0, ← map_zsmul, map_zero] at this
  exact QHeight.nontors_of_certH a b hΔ k x0 y0 h0 hc n
    (ιQK_injective a b (this.trans (map_zero _).symm))

/-- **Two rational points with a passing `ℚ`-certificate are independent.** -/
theorem indep_constK (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (k : ℕ) (fx fy gx gy : Fr K)
    (x1 y1 x2 y2 : ℚ) (hx1 : Fr.val fx = algebraMap ℚ (RatFunc K) x1)
    (hy1 : Fr.val fy = algebraMap ℚ (RatFunc K) y1) (hx2 : Fr.val gx = algebraMap ℚ (RatFunc K) x2)
    (hy2 : Fr.val gy = algebraMap ℚ (RatFunc K) y2)
    (hc : QHeight.certG a b k x1 y1 x2 y2 = true)
    (A B : K[X]) (hA : A = Polynomial.C (a : K)) (hB : B = Polynomial.C (b : K))
    (PD PZ : (shortW A B).toAffine.Point) (hRD : Rel _ _ (some (fx, fy)) PD)
    (hRZ : Rel _ _ (some (gx, gy)) PZ) (m n : ℤ) (hrel : m • PD = n • PZ) : m = 0 ∧ n = 0 := by
  obtain ⟨h1, e1⟩ := const_pointK a b fx fy x1 y1 hx1 hy1 A B hA hB PD hRD
  obtain ⟨h2, e2⟩ := const_pointK a b gx gy x2 y2 hx2 hy2 A B hA hB PZ hRZ
  have := congrArg (castHom (by rw [hA, hB] : (shortW A B).toAffine =
    (shortW (Polynomial.C (a : K)) (Polynomial.C (b : K))).toAffine)) hrel
  rw [map_zsmul, map_zsmul, e1, e2, ← map_zsmul, ← map_zsmul] at this
  exact QHeight.indepQ_of_certG a b hΔ k _ _ _ _ h1 h2 hc m n (ιQK_injective a b this)

/-- Constant fractions: `p.tail = 0`. -/
def isConstK (p : CPoly K) : Bool := p.tail.all (· == 0)

lemma toPoly_of_isConstK {p : CPoly K} (h : isConstK p = true) :
    CPoly.toPoly p = Polynomial.C (p.headD 0) := by
  rcases p with _ | ⟨c, t⟩
  · simp [CPoly.toPoly]
  · have ht : CPoly.toPoly t = 0 := by
      rw [← CPoly.isZero_iff]
      simp only [isConstK, List.tail_cons, List.all_eq_true, beq_iff_eq] at h
      simpa [CPoly.isZero, List.all_eq_true] using h
    simp [CPoly.toPoly_cons, ht]

/-- **The value of a constant fraction with a rational ratio.** -/
lemma val_of_constK (f : Fr K) (h1 : isConstK f.1 = true) (h2 : isConstK f.2 = true) (x0 : ℚ)
    (hx : f.1.headD 0 / f.2.headD 0 = (x0 : K)) :
    Fr.val f = algebraMap ℚ (RatFunc K) x0 := by
  simp only [Fr.val, toPoly_of_isConstK h1, toPoly_of_isConstK h2, RatFunc.algebraMap_C, ← map_div₀,
    hx]
  rw [map_ratCast]; exact (eq_ratCast _ x0).symm

end FFHeight
