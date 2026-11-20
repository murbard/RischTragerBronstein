import RischTragerBronstein.Elliptic.Abel

/-!
# The scaling isomorphism `(x, y) ↦ (u²x, u³y)`

For `W : y² = x³ + a₂x² + a₄x + a₆` and `u ≠ 0`, the map `(x, y) ↦ (u²x, u³y)` sends the points of
`W` to those of `W' : y² = x³ + a₂'x² + a₄'x + a₆'` with `a₂' = u²a₂`, `a₄' = u⁴a₄`, `a₆' = u⁶a₆`;
it is an injective group homomorphism (`scaleHom`). Used for quadratic twists: the points
`(α, γ√d)` of `W` over `ℚ(√d)` are the images of the rational points of the twist.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllAbel

variable {F : Type*} [Field F] [DecidableEq F] {a₂ a₄ a₆ a₂' a₄' a₆' u : F}

lemma equation_W' (x y : F) : (W a₂ a₄ a₆).toAffine.Equation x y ↔
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by
  rw [equation_iff]; simp only [W]; constructor <;> intro h <;> linear_combination h

lemma nonsingular_W' (x y : F) : (W a₂ a₄ a₆).toAffine.Nonsingular x y ↔
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ ∧
      (3 * x ^ 2 + 2 * a₂ * x + a₄ ≠ 0 ∨ 2 * y ≠ 0) := by
  rw [nonsingular_iff', equation_W']
  simp only [W, zero_mul, sub_zero, zero_sub, neg_ne_zero, add_zero]

variable (h₂ : a₂' = u ^ 2 * a₂) (h₄ : a₄' = u ^ 4 * a₄) (h₆ : a₆' = u ^ 6 * a₆) (hu : u ≠ 0)
include h₂ h₄ h₆ hu

lemma scale_nonsingular {x y : F} (h : (W a₂ a₄ a₆).toAffine.Nonsingular x y) :
    (W a₂' a₄' a₆').toAffine.Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
  rw [nonsingular_W'] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by rw [h₂, h₄, h₆]; linear_combination u ^ 6 * he, ?_⟩
  rcases hn with hn | hn
  · left
    rw [h₂, h₄]
    intro h0
    apply hn
    have : u ^ 4 * (3 * x ^ 2 + 2 * a₂ * x + a₄) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu)
  · right
    intro h0
    apply hn
    have : u ^ 3 * (2 * y) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu)

/-- The scaling map on points. -/
noncomputable def scale : (W a₂ a₄ a₆).toAffine.Point → (W a₂' a₄' a₆').toAffine.Point
  | 0 => 0
  | .some x y h => .some _ _ (scale_nonsingular h₂ h₄ h₆ hu h)

lemma scale_some {x y : F} (h : (W a₂ a₄ a₆).toAffine.Nonsingular x y) :
    scale h₂ h₄ h₆ hu (Point.some x y h) = Point.some _ _ (scale_nonsingular h₂ h₄ h₆ hu h) := rfl

lemma scale_slope (x₁ x₂ y₁ y₂ : F) (hxy : ¬(x₁ = x₂ ∧ y₁ = (W a₂ a₄ a₆).toAffine.negY x₂ y₂)) :
    (W a₂' a₄' a₆').toAffine.slope (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * (W a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (W a₂ a₄ a₆).toAffine.negY x₂ y₂ := fun h ↦ hxy ⟨hx, h⟩
    have hy' : u ^ 3 * y₁ ≠ (W a₂' a₄' a₆').toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
      rw [negY_W] at hy ⊢
      intro h0; apply hy
      have : u ^ 3 * (y₁ + y₂) = 0 := by linear_combination h0
      linear_combination (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu)
    rw [slope_of_Y_ne (by rw [hx]) hy', slope_of_Y_ne hx hy]
    simp only [negY_W]
    simp only [W, zero_mul, sub_zero]
    rw [h₂, h₄]
    have key : ∀ K Y : F, (u ^ 4 * K) / (u ^ 3 * Y) = u * (K / Y) := by
      intro K Y
      rw [show u ^ 4 * K = u ^ 3 * (u * K) by ring, mul_div_mul_left _ _ (pow_ne_zero 3 hu),
        mul_div_assoc]
    convert key (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄) (y₁ - -y₁) using 2 <;> ring
  · have hx' : u ^ 2 * x₁ ≠ u ^ 2 * x₂ := fun h ↦ hx (mul_left_cancel₀ (pow_ne_zero _ hu) h)
    rw [slope_of_X_ne hx', slope_of_X_ne hx]
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp

lemma scale_add (P Q : (W a₂ a₄ a₆).toAffine.Point) :
    scale h₂ h₄ h₆ hu (P + Q) = scale h₂ h₄ h₆ hu P + scale h₂ h₄ h₆ hu Q := by
  rcases P with _ | ⟨x₁, y₁, hP⟩
  · show scale h₂ h₄ h₆ hu (0 + Q) = 0 + scale h₂ h₄ h₆ hu Q
    rw [zero_add, zero_add]
  rcases Q with _ | ⟨x₂, y₂, hQ⟩
  · show scale h₂ h₄ h₆ hu (Point.some x₁ y₁ hP + 0) = scale h₂ h₄ h₆ hu (Point.some x₁ y₁ hP) + 0
    rw [add_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (W a₂ a₄ a₆).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    simp only [scale]
    rw [Point.add_of_Y_eq (by rw [hxy.1]) (by rw [negY_W, hxy.2, negY_W]; ring)]
  · have hxy' : ¬(u ^ 2 * x₁ = u ^ 2 * x₂ ∧
        u ^ 3 * y₁ = (W a₂' a₄' a₆').toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
      rintro ⟨h1, h2⟩
      apply hxy
      refine ⟨mul_left_cancel₀ (pow_ne_zero _ hu) h1, ?_⟩
      rw [negY_W] at h2 ⊢
      have : u ^ 3 * (y₁ + y₂) = 0 := by linear_combination h2
      linear_combination (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hu)
    rw [Point.add_some hxy]
    simp only [scale]
    rw [Point.add_some hxy']
    simp only [Point.some.injEq]
    rw [scale_slope h₂ h₄ h₆ hu x₁ x₂ y₁ y₂ hxy]
    simp only [addX, addY, negAddY, negY_W]
    simp only [W, zero_mul, add_zero, h₂]
    constructor <;> ring

/-- **The scaling isomorphism** as an additive homomorphism. -/
noncomputable def scaleHom : (W a₂ a₄ a₆).toAffine.Point →+ (W a₂' a₄' a₆').toAffine.Point where
  toFun := scale h₂ h₄ h₆ hu
  map_zero' := rfl
  map_add' := scale_add h₂ h₄ h₆ hu

lemma scale_injective : Function.Injective (scale h₂ h₄ h₆ hu) := by
  rintro (_ | ⟨x₁, y₁, hP⟩) (_ | ⟨x₂, y₂, hQ⟩) h
  · rfl
  · simp [scale] at h
  · simp [scale] at h
  · simp only [scale, Point.some.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := mul_left_cancel₀ (pow_ne_zero _ hu) h1
    have e2 := mul_left_cancel₀ (pow_ne_zero _ hu) h2
    subst e1 e2
    rfl

end EllAbel
