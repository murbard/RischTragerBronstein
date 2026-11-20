import RischTragerBronstein.Mixed.EllTrans

/-!
# Galois descent of points, and independence over quadratic extensions

For an elliptic curve `W` over `F` and an `F`-automorphism `σ` of `K'` with fixed field `F`
(`hfix`):

* `fixed_descends`: a point of `W(K')` fixed by `σ` comes from `W(F)`;
* `anti_descends`: on `y² = x³ + a x + b`, if `K' = F(δ)` with `δ² = d ∈ F`, `σ δ = −δ`, a point
  with `σ Q = −Q` comes from the quadratic twist `y² = x³ + d²a x + d³b` over `F`
  (`(x₀, y₀) ↦ (x₀/d, y₀ δ/d²)`, `twistP`);
* `indep_of_trace`, `indep_of_twist`: a relation `m • D = n • Z` in `W(K')` gives the same relation
  between the descents of `D + σD, Z + σZ` (in `W(F)`) and of `D − σD, Z − σZ` (in the twist), so
  independence certified over `F` (e.g. by `EllNT.ell_indep` for `F = K(X)`) transfers to `K'`.

Relations among points of `W(K')` hold in `W(K')` iff they hold over any extension (base change is
injective, `Point.map_injective`), so it suffices to certify over a field of definition.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

section Fixed

variable {F K' : Type*} [Field F] [Field K'] [Algebra F K']
variable (W : Affine F) (σ : K' →ₐ[F] K')

/-- **Fixed points descend.** -/
theorem fixed_descends (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (Q : (W⁄K').Point) (hQ : Point.map σ Q = Q) :
    ∃ Q₀ : (W⁄F).Point, Point.map (Algebra.ofId F K') Q₀ = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  rw [Point.map_some, Point.some.injEq] at hQ
  obtain ⟨x0, hx0⟩ := hfix x hQ.1
  obtain ⟨y0, hy0⟩ := hfix y hQ.2
  have h0 : (W⁄F).Nonsingular x0 y0 := by
    rw [← baseChange_nonsingular (W := W) (f := Algebra.ofId F K') (Algebra.ofId F K').injective]
    simpa [Algebra.ofId_apply, hx0, hy0] using h
  refine ⟨Point.some _ _ h0, ?_⟩
  rw [Point.map_some, Point.some.injEq]
  exact ⟨by simpa [Algebra.ofId_apply] using hx0, by simpa [Algebra.ofId_apply] using hy0⟩

/-- **Trace transfer**: a relation in `W(K')` gives one between descents of `D + σD`, `Z + σZ`. -/
theorem indep_of_trace (D Z : (W⁄K').Point) (D₀ Z₀ : (W⁄F).Point)
    (hD : Point.map (Algebra.ofId F K') D₀ = D + Point.map σ D)
    (hZ : Point.map (Algebra.ofId F K') Z₀ = Z + Point.map σ Z)
    (hind : ∀ m n : ℤ, m • D₀ = n • Z₀ → m = 0 ∧ n = 0)
    (m n : ℤ) (hrel : m • D = n • Z) : m = 0 ∧ n = 0 := by
  apply hind
  apply Point.map_injective (Algebra.ofId F K')
  rw [map_zsmul, map_zsmul, hD, hZ, zsmul_add, zsmul_add, ← map_zsmul, ← map_zsmul, hrel]

end Fixed

section Twist

variable {F K' : Type*} [Field F] [Field K'] [Algebra F K']

/-- The short curve over `F`, base-changed, is the short curve with mapped coefficients. -/
lemma shortF_baseChange (a b : F) :
    ((shortF a b).toAffine⁄K') = (shortF (algebraMap F K' a) (algebraMap F K' b)).toAffine := by
  simp [shortF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- **Anti-fixed points come from the twist.** -/
theorem anti_descends (a b d : F) (δ : K') (σ : K' →ₐ[F] K') (hδ : δ ^ 2 = algebraMap F K' d)
    (hδ0 : δ ≠ 0) (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (x y : K') (h : y ^ 2 = x ^ 3 + algebraMap F K' a * x + algebraMap F K' b)
    (hx : σ x = x) (hy : σ y = -y) :
    ∃ x0 y0 : F, y0 ^ 2 = x0 ^ 3 + d ^ 2 * a * x0 + d ^ 3 * b ∧
      algebraMap F K' x0 = algebraMap F K' d * x ∧
      algebraMap F K' y0 = algebraMap F K' d * δ * y := by
  have hd0 : algebraMap F K' d ≠ 0 := by rw [← hδ]; exact pow_ne_zero 2 hδ0
  obtain ⟨x1, hx1⟩ := hfix x hx
  obtain ⟨y1, hy1⟩ := hfix (δ * y) (by rw [map_mul, hσδ, hy]; ring)
  refine ⟨d * x1, d * y1, ?_, by rw [map_mul, hx1], ?_⟩
  · apply (algebraMap F K').injective
    simp only [map_mul, map_pow, map_add]
    rw [hx1, hy1, mul_pow, mul_pow, ← hδ, h]; ring
  · rw [map_mul, hy1]; ring

/-- **Twist transfer**: given descents `D₀, Z₀` on the twist of `D − σD`, `Z − σZ` through an
injective homomorphism `ι` from the twist to `W(K')`, independence of `D₀, Z₀` gives independence
of `D, Z`. -/
theorem indep_of_twist {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ι : G →+ H)
    (hι : Function.Injective ι) (s : H →+ H) (D Z : H) (D₀ Z₀ : G)
    (hD : ι D₀ = D - s D) (hZ : ι Z₀ = Z - s Z)
    (hind : ∀ m n : ℤ, m • D₀ = n • Z₀ → m = 0 ∧ n = 0)
    (m n : ℤ) (hrel : m • D = n • Z) : m = 0 ∧ n = 0 := by
  apply hind
  apply hι
  rw [map_zsmul, map_zsmul, hD, hZ, zsmul_sub, zsmul_sub, ← map_zsmul, ← map_zsmul, hrel]

end Twist

end FFHeight
