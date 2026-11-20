import RischTragerBronstein.Mixed.EllCombine

/-!
# The quadratic twist homomorphism

For `K' = F(δ)`, `δ² = d ∈ F`, `σ δ = −δ`, the map `ι : E^d(F) → E(K')`,
`(x₀, y₀) ↦ (x₀/d, y₀/(dδ))`, from the twist `y² = x³ + d²a x + d³b` is an injective group
homomorphism (`twistHom`: base change, then scaling by `u = δ⁻¹`), and every point with
`σ Q = −Q` is in its image (`anti_in_range`); hence `twistDesc : E(K') →+ E^d(F)`,
`P ↦ ι⁻¹(P − σP)`. With `traceHom` and `indep_of_pulls` this gives the complete independence
test over quadratic extensions.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

/-- Transport of points along an equality of curves. -/
def castHom {F : Type*} [Field F] [DecidableEq F] {W1 W2 : Affine F} (h : W1 = W2) :
    W1.Point →+ W2.Point := h ▸ AddMonoidHom.id _

lemma castHom_some {F : Type*} [Field F] [DecidableEq F] {W1 W2 : Affine F} (h : W1 = W2)
    {x y : F} (hxy : W1.Nonsingular x y) : castHom h (Point.some x y hxy) = Point.some x y (h ▸ hxy) := by
  subst h; rfl

lemma castHom_injective {F : Type*} [Field F] [DecidableEq F] {W1 W2 : Affine F} (h : W1 = W2) :
    Function.Injective (castHom h) := by
  subst h; exact fun _ _ e ↦ e

/-- Scaling with the target coefficients given by equations. -/
def scaleHomEq {F : Type*} [Field F] (a b a' b' u : F) (hu : u ≠ 0) (ha : a' = u ^ 4 * a)
    (hb : b' = u ^ 6 * b) : (shortF a b).toAffine.Point →+ (shortF a' b').toAffine.Point := by
  subst ha hb; exact scaleHom a b u hu

lemma scaleHomEq_some {F : Type*} [Field F] (a b a' b' u : F) (hu : u ≠ 0) (ha : a' = u ^ 4 * a)
    (hb : b' = u ^ 6 * b) {x y : F} (h : (shortF a b).toAffine.Nonsingular x y) :
    ∃ h', scaleHomEq a b a' b' u hu ha hb (Point.some x y h) = Point.some (u ^ 2 * x) (u ^ 3 * y) h' := by
  subst ha hb; exact ⟨_, rfl⟩

lemma scaleHomEq_injective {F : Type*} [Field F] (a b a' b' u : F) (hu : u ≠ 0)
    (ha : a' = u ^ 4 * a) (hb : b' = u ^ 6 * b) : Function.Injective (scaleHomEq a b a' b' u hu ha hb) := by
  subst ha hb; exact scaleHom_injective a b u hu

variable {F K' : Type*} [Field F] [Field K'] [Algebra F K']
variable (a b d : F) (δ : K') (hδ : δ ^ 2 = algebraMap F K' d) (hδ0 : δ ≠ 0)

include hδ hδ0 in
lemma twist_a : algebraMap F K' a = δ⁻¹ ^ 4 * algebraMap F K' (d ^ 2 * a) := by
  rw [map_mul, map_pow, ← hδ]; field_simp

include hδ hδ0 in
lemma twist_b : algebraMap F K' b = δ⁻¹ ^ 6 * algebraMap F K' (d ^ 3 * b) := by
  rw [map_mul, map_pow, ← hδ]; field_simp

/-- **The twist homomorphism** `E^d(F) →+ E(K')`. -/
noncomputable def twistHom : ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point →+
    ((shortF a b).toAffine⁄K').Point :=
  (castHom (shortF_baseChange a b).symm).comp <|
    (scaleHomEq _ _ _ _ δ⁻¹ (inv_ne_zero hδ0) (twist_a a d δ hδ hδ0) (twist_b b d δ hδ hδ0)).comp <|
      (castHom (shortF_baseChange (d ^ 2 * a) (d ^ 3 * b))).comp <|
        Point.map (W' := (shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine) (Algebra.ofId F K')

lemma twistHom_injective : Function.Injective (twistHom a b d δ hδ hδ0) := by
  unfold twistHom
  exact (castHom_injective _).comp ((scaleHomEq_injective _ _ _ _ _ _ _ _).comp
    ((castHom_injective _).comp
      (Point.map_injective (W' := (shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine) (Algebra.ofId F K'))))

lemma twistHom_some (x0 y0 : F) (h0 : ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Nonsingular x0 y0) :
    ∃ h', twistHom a b d δ hδ hδ0 (Point.some x0 y0 h0) =
      Point.some (δ⁻¹ ^ 2 * Algebra.ofId F K' x0) (δ⁻¹ ^ 3 * Algebra.ofId F K' y0) h' := by
  unfold twistHom
  simp only [AddMonoidHom.comp_apply, Point.map_some, castHom_some]
  obtain ⟨h', e⟩ := scaleHomEq_some _ _ _ _ δ⁻¹ (inv_ne_zero hδ0) (twist_a a d δ hδ hδ0)
    (twist_b b d δ hδ hδ0)
    ((shortF_baseChange (K' := K') (d ^ 2 * a) (d ^ 3 * b)) ▸
      (baseChange_nonsingular (W := (shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine)
        (f := Algebra.ofId F K') (Algebra.ofId F K').injective x0 y0).mpr h0)
  rw [e, castHom_some]
  exact ⟨by rw [shortF_baseChange]; exact h', rfl⟩

lemma ns_baseChange_short (x y : K') :
    ((shortF a b).toAffine⁄K').Nonsingular x y ↔
      (shortF (algebraMap F K' a) (algebraMap F K' b)).toAffine.Nonsingular x y := by
  rw [shortF_baseChange]

lemma negY_baseChange_short (x y : K') : ((shortF a b).toAffine⁄K').negY x y = -y := by
  rw [shortF_baseChange, negY_shortF]

/-- **Anti-fixed points lie in the image of the twist.** -/
theorem anti_in_range (σ : K' →ₐ[F] K') (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (P : ((shortF a b).toAffine⁄K').Point) (hP : Point.map σ P = -P) :
    ∃ Q₀, twistHom a b d δ hδ hδ0 Q₀ = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, map_zero _⟩
  rw [Point.map_some, Point.neg_some, Point.some.injEq, negY_baseChange_short] at hP
  have hs := (ns_baseChange_short a b x y).mp h
  have heq : y ^ 2 = x ^ 3 + algebraMap F K' a * x + algebraMap F K' b := ((ns_short _ _ x y).mp hs).1
  obtain ⟨x0, y0, he0, hx0, hy0⟩ := anti_descends a b d δ σ hδ hδ0 hσδ hfix x y heq hP.1 hP.2
  -- nonsingularity on the twist over `F`
  have hsc := ns_scale _ _ δ x y hδ0 hs
  have hA : δ ^ 4 * algebraMap F K' a = algebraMap F K' (d ^ 2 * a) := by
    rw [map_mul, map_pow, ← hδ]; ring
  have hB : δ ^ 6 * algebraMap F K' b = algebraMap F K' (d ^ 3 * b) := by
    rw [map_mul, map_pow, ← hδ]; ring
  have hX : δ ^ 2 * x = algebraMap F K' x0 := by rw [hx0, ← hδ]
  have hY : δ ^ 3 * y = algebraMap F K' y0 := by rw [hy0, ← hδ]; ring
  rw [hA, hB, hX, hY, ← shortF_baseChange] at hsc
  have h0 : ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Nonsingular x0 y0 :=
    (baseChange_nonsingular (W := (shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine)
      (f := Algebra.ofId F K') (Algebra.ofId F K').injective x0 y0).mp
      (by simpa [Algebra.ofId_apply] using hsc)
  refine ⟨Point.some x0 y0 h0, ?_⟩
  obtain ⟨h', e⟩ := twistHom_some a b d δ hδ hδ0 x0 y0 h0
  rw [e, Point.some.injEq]
  simp only [Algebra.ofId_apply]
  constructor
  · rw [← hX]; field_simp
  · rw [← hY]; field_simp

lemma anti_of (σ : K' →ₐ[F] K') (hσ : ∀ z, σ (σ z) = z) (P : ((shortF a b).toAffine⁄K').Point) :
    Point.map σ (P - Point.map σ P) = -(P - Point.map σ P) := by
  rw [map_sub, map_invol _ σ hσ]; abel

/-- The twist descent of `P − σP`. -/
noncomputable def twistDescP (σ : K' →ₐ[F] K') (hσ : ∀ z, σ (σ z) = z) (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (P : ((shortF a b).toAffine⁄K').Point) : ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point :=
  (anti_in_range a b d δ hδ hδ0 σ hσδ hfix _ (anti_of a b σ hσ P)).choose

lemma twistDescP_spec (σ : K' →ₐ[F] K') (hσ : ∀ z, σ (σ z) = z) (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (P : ((shortF a b).toAffine⁄K').Point) :
    twistHom a b d δ hδ hδ0 (twistDescP a b d δ hδ hδ0 σ hσ hσδ hfix P) = P - Point.map σ P :=
  (anti_in_range a b d δ hδ hδ0 σ hσδ hfix _ (anti_of a b σ hσ P)).choose_spec

/-- **The twist descent homomorphism** `E(K') →+ E^d(F)`, `P ↦ ι⁻¹(P − σP)`. -/
noncomputable def twistDesc (σ : K' →ₐ[F] K') (hσ : ∀ z, σ (σ z) = z) (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z) :
    ((shortF a b).toAffine⁄K').Point →+ ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point where
  toFun := twistDescP a b d δ hδ hδ0 σ hσ hσδ hfix
  map_zero' := by
    apply twistHom_injective a b d δ hδ hδ0
    rw [twistDescP_spec, map_zero, map_zero, sub_zero]
  map_add' := fun P Q ↦ by
    apply twistHom_injective a b d δ hδ hδ0
    rw [map_add, twistDescP_spec, twistDescP_spec, twistDescP_spec, map_add]
    abel

/-- **The complete test over a quadratic extension**: symmetric pairings `B₁` on `E(F)` and `B₂`
on the twist `E^d(F)` (e.g. Néron–Tate pairings), pulled back along the trace and the twist
descent; a non-zero Gram determinant of their sum on `D, Z` rules out every relation in `E(K')`. -/
theorem quad_indep (σ : K' →ₐ[F] K') (hσ : ∀ z, σ (σ z) = z) (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (B₁ : ((shortF a b).toAffine⁄F).Point →+ ((shortF a b).toAffine⁄F).Point →+ ℝ)
    (B₂ : ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point →+
      ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point →+ ℝ)
    (h₁ : ∀ P Q, B₁ P Q = B₁ Q P) (h₂ : ∀ P Q, B₂ P Q = B₂ Q P)
    (D Z : ((shortF a b).toAffine⁄K').Point)
    (hg : MWPair.gram (pullPair B₁ (traceHom (shortF a b).toAffine σ hσ hfix) +
      pullPair B₂ (twistDesc a b d δ hδ hδ0 σ hσ hσδ hfix)) D Z ≠ 0)
    (m n : ℤ) (hrel : m • D = n • Z) : m = 0 ∧ n = 0 :=
  indep_of_pulls B₁ B₂ h₁ h₂ _ _ D Z hg m n hrel

/-- **The pairing over a quadratic extension**, from pairings on `E(F)` and on the twist:
iterating `quadPair` along a tower `F ⊂ F(√d₁) ⊂ F(√d₁, √d₂) ⊂ …` gives symmetric pairings over
multi-quadratic extensions, to which `MWPair.gram_ne_zero_indep` applies. -/
noncomputable def quadPair (σ : K' →ₐ[F] K') (hσ : ∀ z, σ (σ z) = z) (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (B₁ : ((shortF a b).toAffine⁄F).Point →+ ((shortF a b).toAffine⁄F).Point →+ ℝ)
    (B₂ : ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point →+
      ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point →+ ℝ) :
    ((shortF a b).toAffine⁄K').Point →+ ((shortF a b).toAffine⁄K').Point →+ ℝ :=
  pullPair B₁ (traceHom (shortF a b).toAffine σ hσ hfix) +
    pullPair B₂ (twistDesc a b d δ hδ hδ0 σ hσ hσδ hfix)

lemma quadPair_symm (σ : K' →ₐ[F] K') (hσ : ∀ z, σ (σ z) = z) (hσδ : σ δ = -δ)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z)
    (B₁ : ((shortF a b).toAffine⁄F).Point →+ ((shortF a b).toAffine⁄F).Point →+ ℝ)
    (B₂ : ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point →+
      ((shortF (d ^ 2 * a) (d ^ 3 * b)).toAffine⁄F).Point →+ ℝ)
    (h₁ : ∀ P Q, B₁ P Q = B₁ Q P) (h₂ : ∀ P Q, B₂ P Q = B₂ Q P) (P Q) :
    quadPair a b d δ hδ hδ0 σ hσ hσδ hfix B₁ B₂ P Q = quadPair a b d δ hδ hδ0 σ hσ hσδ hfix B₁ B₂ Q P := by
  simp only [quadPair, AddMonoidHom.add_apply, pullPair_symm B₁ h₁, pullPair_symm B₂ h₂]

end FFHeight
