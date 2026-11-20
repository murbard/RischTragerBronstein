import RischTragerBronstein.Mixed.EllCompute2
import RischTragerBronstein.Mixed.FFBase
import RischTragerBronstein.Mixed.EllTwist

/-!
# Extending the constants of the height certificate

For a field extension `f : k →+* k'`, points of `y² = x³ + A x + B` over `k(X)` map to points over
`k'(X)` by a group homomorphism (`mapE`, Mathlib's `Point.map` along `k(X) → k'(X)`) that preserves
the naive height (`hN_mapE`, from `FFHeight.ht_map`). Hence an independence certificate computed over
`k` (e.g. `ℚ(√κ)`) proves independence of the images over `k'` (e.g. the constants of the tower):
`indep_mapE_of_certQ`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {k k' : Type*} [Field k] [Field k'] [CharZero k] [CharZero k'] (f : k →+* k')

/-- The induced map `k(X) → k'(X)`. -/
noncomputable def ratMap : RatFunc k →+* RatFunc k' :=
  RatFunc.mapRingHom (Polynomial.mapRingHom f) (map_nzd f)

lemma ratMap_alg (p : k[X]) :
    ratMap f (algebraMap k[X] (RatFunc k) p) = algebraMap k'[X] (RatFunc k') (p.map f) := by
  have := RatFunc.map_apply_div (Polynomial.mapRingHom f) (map_nzd f) p 1
  simp only [map_one, div_one] at this
  rw [ratMap, RatFunc.coe_mapRingHom_eq_coe_map, this]; rfl

/-- **The map of points** `E(k(X)) → E(k'(X))`. -/
noncomputable def mapE (A B : k[X]) :
    (shortW A B).toAffine.Point →+ (shortW (A.map f) (B.map f)).toAffine.Point :=
  letI : Algebra (RatFunc k) (RatFunc k') := (ratMap f).toAlgebra
  have hself : (shortW A B).toAffine = ((shortW A B).toAffine⁄(RatFunc k)) := by
    simp [shortW, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have hbc : ((shortW A B).toAffine⁄(RatFunc k')) = (shortW (A.map f) (B.map f)).toAffine := by
    simp only [shortW, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      RingHom.algebraMap_toAlgebra, map_zero]
    congr 1 <;> exact ratMap_alg f _
  (castHom hbc).comp ((Point.map (W' := (shortW A B).toAffine) (Algebra.ofId (RatFunc k)
    (RatFunc k'))).comp (castHom hself))

lemma mapE_some (A B : k[X]) (x y : RatFunc k) (h : (shortW A B).toAffine.Nonsingular x y) :
    ∃ h', mapE f A B (Point.some x y h) = Point.some (ratMap f x) (ratMap f y) h' := by
  letI : Algebra (RatFunc k) (RatFunc k') := (ratMap f).toAlgebra
  unfold mapE
  simp only [AddMonoidHom.comp_apply]
  erw [castHom_some]
  refine ⟨?w, ?e⟩
  case e => rfl
  case w =>
    have hW : (shortW (A.map f) (B.map f)).toAffine = ((shortW A B).toAffine.map (ratMap f)) := by
      simp only [shortW, Affine.map, WeierstrassCurve.map, map_zero, ratMap_alg]
    rw [hW]
    exact (Affine.map_nonsingular (W := (shortW A B).toAffine) (ratMap f).injective x y).mpr h

/-- **Heights are preserved.** -/
lemma hN_mapE (A B : k[X]) (P : (shortW A B).toAffine.Point) :
    hN (A.map f) (B.map f) (mapE f A B P) = hN A B P := by
  rcases P with _ | ⟨x, y, h⟩
  · show hN _ _ (mapE f A B 0) = hN A B 0
    rw [map_zero]; rfl
  · obtain ⟨h', e⟩ := mapE_some f A B x y h
    rw [e]
    simp only [hN]
    rw [ratMap, RatFunc.coe_mapRingHom_eq_coe_map]
    exact ht_map f x

lemma hR_mapE (A B : k[X]) (P : (shortW A B).toAffine.Point) :
    hR (A.map f) (B.map f) (mapE f A B P) = hR A B P := by
  simp only [hR, hN_mapE]

lemma mapE_dbl (A B : k[X]) (n : ℕ) (P : (shortW A B).toAffine.Point) :
    mapE f A B (MWPair.dbl^[n] P) = MWPair.dbl^[n] (mapE f A B P) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', MWPair.dbl,
      MWPair.dbl, map_add, ih]

/-- **A certificate over `k` proves independence of the images over `k'`.** -/
theorem indep_mapE_of_certQ [DecidableEq k] (Ac : CPoly k) (A B : k[X]) (hA : CPoly.toPoly Ac = A)
    (hΔ' : 4 * (A.map f) ^ 3 + 27 * (B.map f) ^ 2 ≠ 0) (kk : ℕ) (oP oQ : PtC k)
    (P Q : (shortW A B).toAffine.Point) (hP : Rel A B oP P) (hQ : Rel A B oQ Q)
    (hc : certQ Ac (max A.natDegree B.natDegree) kk oP oQ = true)
    (m n : ℤ) (hrel : m • mapE f A B P = n • mapE f A B Q) : m = 0 ∧ n = 0 := by
  refine ell_indep (A.map f) (B.map f) hΔ' _ _ kk ?_ m n hrel
  have e1 := htC_spec A B _ _ (dblC_spec Ac A B hA kk oP P hP)
  have e2 := htC_spec A B _ _ (dblC_spec Ac A B hA kk oQ Q hQ)
  have e3 := htC_spec A B _ _ (dblC_spec Ac A B hA kk _ _ (addC_spec Ac A B hA oP oQ P Q hP hQ))
  simp only [certQ, decide_eq_true_eq] at hc
  have hd : max (A.map f).natDegree (B.map f).natDegree = max A.natDegree B.natDegree := by
    rw [natDegree_map, natDegree_map]
  simp only [← map_add, ← mapE_dbl, hR_mapE, hd]
  simp only [hR]
  rw [← e1, ← e2, ← e3]
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  push_cast [Rat.cast_abs] at hc' ⊢
  exact hc'

/-- Map the coefficients of an executable fraction. -/
def frMap (f : k →+* k') (g : Fr k) : Fr k' := (g.1.map f, g.2.map f)

lemma toPoly_map (p : CPoly k) : CPoly.toPoly (p.map f) = (CPoly.toPoly p).map f := by
  induction p with
  | nil => simp [CPoly.toPoly]
  | cons a p ih => simp [CPoly.toPoly_cons, ih]

lemma frMap_ok (g : Fr k) (hg : Fr.ok g) : Fr.ok (frMap f g) := by
  simp only [Fr.ok, frMap, toPoly_map] at hg ⊢
  exact (Polynomial.map_ne_zero_iff f.injective).mpr hg

/-- **Values of mapped fractions.** -/
lemma frMap_val (g : Fr k) : Fr.val (frMap f g) = ratMap f (Fr.val g) := by
  simp only [Fr.val, frMap, toPoly_map, map_div₀, ratMap_alg]

lemma shortW_map (A B : k[X]) :
    (shortW (A.map f) (B.map f)).toAffine = ((shortW A B).toAffine.map (ratMap f)) := by
  simp only [shortW, Affine.map, WeierstrassCurve.map, map_zero, ratMap_alg]

/-- **Points with executable preimages**: a point over `k'(X)` whose coordinates are the images of
executable fractions over `k` is the image under `mapE` of the point those fractions represent. -/
lemma pt_of_image [DecidableEq k] (A B : k[X]) (fx fy : Fr k) (ox : Fr.ok fx) (oy : Fr.ok fy)
    (h' : (shortW (A.map f) (B.map f)).toAffine.Nonsingular (ratMap f (Fr.val fx))
      (ratMap f (Fr.val fy))) :
    ∃ Pk : (shortW A B).toAffine.Point, Rel A B (some (fx, fy)) Pk ∧
      mapE f A B Pk = WeierstrassCurve.Affine.Point.some _ _ h' := by
  have hk : (shortW A B).toAffine.Nonsingular (Fr.val fx) (Fr.val fy) := by
    rw [shortW_map] at h'
    exact (Affine.map_nonsingular (W := (shortW A B).toAffine) (ratMap f).injective _ _).mp h'
  refine ⟨Point.some _ _ hk, ⟨ox, oy, rfl, rfl⟩, ?_⟩
  obtain ⟨h2, e⟩ := mapE_some f A B _ _ hk
  rw [e]

/-- **Constant factors**: `val (g · ρ)` maps to `(image of g) · ρ`. -/
lemma frMap_mulConst [DecidableEq k] (g : Fr k) (hg : Fr.ok g) (ρ : k) :
    ratMap f (Fr.val (Fr.mul g (Fr.ofPoly [ρ]))) =
      ratMap f (Fr.val g) * algebraMap k' (RatFunc k') (f ρ) := by
  rw [Fr.val_mul hg (Fr.ok_ofPoly _), Fr.val_ofPoly, map_mul, ratMap_alg]
  congr 1
  simp [CPoly.toPoly, RatFunc.algebraMap_C]

end FFHeight
