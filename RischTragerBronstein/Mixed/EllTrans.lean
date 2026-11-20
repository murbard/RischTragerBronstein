import RischTragerBronstein.Mixed.EllScale

/-!
# From a cubic model to short Weierstrass form

`θ² = c₃t³ + c₂t² + c₁t + c₀` (`c₃ ≠ 0`) becomes `Y² = X³ + a₂X² + a₄X + a₆` with `X = c₃t`,
`Y = c₃θ` (`a₂ = c₂`, `a₄ = c₁c₃`, `a₆ = c₀c₃²`, `cubic_to_W`). Over a field of characteristic `0`
the translation `X ↦ X + a₂/3` is an **injective group homomorphism** from the points of
`y² = x³ + a₂x² + a₄x + a₆` to those of the short curve with `a = a₄ − a₂²/3`,
`b = a₆ − a₂a₄/3 + 2a₂³/27` (`transHom`, `transHom_injective`). With `EllScale` this reduces every
genus-one cubic model over `K(X)` to the setting of `EllNT`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {F : Type*} [Field F] [CharZero F]

/-- The curve `y² = x³ + a₂x² + a₄x + a₆`. -/
def longF (a2 a4 a6 : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := a2
  a₃ := 0
  a₄ := a4
  a₆ := a6

/-- The short form of `longF a₂ a₄ a₆`. -/
noncomputable def shortOf (a2 a4 a6 : F) : WeierstrassCurve F :=
  shortF (a4 - a2 ^ 2 / 3) (a6 - a2 * a4 / 3 + 2 * a2 ^ 3 / 27)

omit [CharZero F] in
/-- The cubic model, scaled by its leading coefficient. -/
theorem cubic_to_W (c3 c2 c1 c0 t θ : F) (h : θ ^ 2 = c3 * t ^ 3 + c2 * t ^ 2 + c1 * t + c0) :
    (c3 * θ) ^ 2 = (c3 * t) ^ 3 + c2 * (c3 * t) ^ 2 + (c1 * c3) * (c3 * t) + c0 * c3 ^ 2 := by
  rw [mul_pow, h]; ring

variable (a2 a4 a6 : F)

omit [CharZero F] in
lemma ns_long (x y : F) : (longF a2 a4 a6).toAffine.Nonsingular x y ↔
    y ^ 2 = x ^ 3 + a2 * x ^ 2 + a4 * x + a6 ∧ (0 ≠ 3 * x ^ 2 + 2 * a2 * x + a4 ∨ y ≠ -y) := by
  rw [nonsingular_iff, equation_iff]; simp [longF]

lemma ns_trans (x y : F) (h : (longF a2 a4 a6).toAffine.Nonsingular x y) :
    (shortOf a2 a4 a6).toAffine.Nonsingular (x + a2 / 3) y := by
  rw [ns_long] at h
  rw [shortOf, ns_short]
  obtain ⟨he, hn⟩ := h
  refine ⟨by rw [he]; ring, ?_⟩
  rcases hn with hn | hn
  · left; intro h0; apply hn; linear_combination h0
  · right; exact hn

/-- The translation on points. -/
noncomputable def transP : (longF a2 a4 a6).toAffine.Point → (shortOf a2 a4 a6).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (x + a2 / 3) y (ns_trans a2 a4 a6 x y h)

omit [CharZero F] in
lemma negY_long (x y : F) : (longF a2 a4 a6).toAffine.negY x y = -y := by simp [negY, longF]

omit [CharZero F] in
lemma negY_shortOf (x y : F) : (shortOf a2 a4 a6).toAffine.negY x y = -y := by
  simp [negY, shortOf, shortF]

lemma slope_trans (x1 x2 y1 y2 : F) :
    (shortOf a2 a4 a6).toAffine.slope (x1 + a2 / 3) (x2 + a2 / 3) y1 y2 =
      (longF a2 a4 a6).toAffine.slope x1 x2 y1 y2 := by
  have ex : x1 + a2 / 3 = x2 + a2 / 3 ↔ x1 = x2 := add_left_inj _
  unfold slope
  simp only [negY_long, negY_shortOf, ex]
  split_ifs with h1 h2
  · rfl
  · simp only [shortOf, shortF, longF]
    congr 1; ring
  · congr 1; ring

lemma add_trans (P Q : (longF a2 a4 a6).toAffine.Point) :
    transP a2 a4 a6 (P + Q) = transP a2 a4 a6 P + transP a2 a4 a6 Q := by
  rcases P with _ | ⟨x1, y1, h1⟩
  · rfl
  rcases Q with _ | ⟨x2, y2, h2⟩
  · rfl
  by_cases hxy : x1 = x2 ∧ y1 = (longF a2 a4 a6).toAffine.negY x2 y2
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    have h' : y1 = (shortOf a2 a4 a6).toAffine.negY (x2 + a2 / 3) y2 := by
      rw [negY_shortOf, hxy.2, negY_long]
    exact (Point.add_of_Y_eq (by rw [hxy.1]) h').symm
  · rw [Point.add_some hxy]
    have hxy' : ¬(x1 + a2 / 3 = x2 + a2 / 3 ∧
        y1 = (shortOf a2 a4 a6).toAffine.negY (x2 + a2 / 3) y2) := by
      rintro ⟨e1, e2⟩; apply hxy
      refine ⟨add_right_cancel e1, ?_⟩
      rw [negY_shortOf] at e2; rw [negY_long]; exact e2
    simp only [transP]
    rw [Point.add_some hxy']
    simp only [Point.some.injEq]
    rw [slope_trans]
    constructor
    · simp only [addX, shortOf, shortF, longF]; ring
    · simp only [addY, negAddY, addX, negY, shortOf, shortF, longF]; ring

/-- **The translation homomorphism.** -/
noncomputable def transHom : (longF a2 a4 a6).toAffine.Point →+ (shortOf a2 a4 a6).toAffine.Point where
  toFun := transP a2 a4 a6
  map_zero' := rfl
  map_add' := add_trans a2 a4 a6

lemma transHom_apply (P : (longF a2 a4 a6).toAffine.Point) :
    transHom a2 a4 a6 P = transP a2 a4 a6 P := rfl

lemma transHom_injective : Function.Injective (transHom a2 a4 a6) := by
  rintro (_ | ⟨x1, y1, h1⟩) (_ | ⟨x2, y2, h2⟩) h
  · rfl
  · simp [transHom_apply, transP] at h
  · simp [transHom_apply, transP] at h
  · simp only [transHom_apply, transP, Point.some.injEq] at h
    obtain ⟨e1, e2⟩ := h
    have e1' := add_right_cancel e1
    subst e1'; subst e2; rfl

/-- Independence transfers along the translation. -/
theorem indep_of_trans (P Q : (longF a2 a4 a6).toAffine.Point)
    (h : ∀ m n : ℤ, m • transHom a2 a4 a6 P = n • transHom a2 a4 a6 Q → m = 0 ∧ n = 0)
    (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 :=
  h m n (by rw [← map_zsmul, ← map_zsmul, hrel])

end FFHeight
