import RischTragerBronstein.Mixed.EllNT

/-!
# Scaling isomorphisms of short Weierstrass curves, and certificates over any coefficients

For `u ≠ 0`, `(x, y) ↦ (u²x, u³y)` maps `y² = x³ + a x + b` to `y² = x³ + u⁴a x + u⁶b`; it is an
**injective group homomorphism** of the groups of points (`scaleHom`, `scaleHom_injective`; Mathlib
has no isomorphisms of points under changes of variables). Every short curve over `K(X)` scales to
one with polynomial coefficients (`exists_poly_scale`), so the independence certificate `ell_indep`
applies to points of any short Weierstrass curve over `K(X)` (`ell_indep_any`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {F : Type*} [Field F]

/-- The short Weierstrass curve `y² = x³ + a x + b` over a field. -/
def shortF (a b : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := a
  a₆ := b

lemma ns_short (a b x y : F) : (shortF a b).toAffine.Nonsingular x y ↔
    y ^ 2 = x ^ 3 + a * x + b ∧ (0 ≠ 3 * x ^ 2 + a ∨ y ≠ -y) := by
  rw [nonsingular_iff, equation_iff]; simp [shortF]

lemma ns_scale (a b u x y : F) (hu : u ≠ 0) (h : (shortF a b).toAffine.Nonsingular x y) :
    (shortF (u ^ 4 * a) (u ^ 6 * b)).toAffine.Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
  rw [ns_short] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by rw [show (u ^ 3 * y) ^ 2 = u ^ 6 * y ^ 2 by ring, he]; ring, ?_⟩
  rcases hn with hn | hn
  · left; intro h0; apply hn
    have : u ^ 4 * (3 * x ^ 2 + a) = 0 := by linear_combination -h0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h1) hu
    · exact h1.symm
  · right; intro h0; apply hn
    have : u ^ 3 * (2 * y) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h1) hu
    · linear_combination h1

variable (a b u : F)

/-- The scaling map on points. -/
def scaleP (hu : u ≠ 0) : (shortF a b).toAffine.Point → (shortF (u ^ 4 * a) (u ^ 6 * b)).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (u ^ 2 * x) (u ^ 3 * y) (ns_scale a b u x y hu h)

lemma negY_shortF (x y : F) : (shortF a b).toAffine.negY x y = -y := by simp [negY, shortF]

lemma slope_scale (hu : u ≠ 0) (x1 x2 y1 y2 : F) :
    (shortF (u ^ 4 * a) (u ^ 6 * b)).toAffine.slope (u ^ 2 * x1) (u ^ 2 * x2) (u ^ 3 * y1)
      (u ^ 3 * y2) = u * (shortF a b).toAffine.slope x1 x2 y1 y2 := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  have ex : u ^ 2 * x1 = u ^ 2 * x2 ↔ x1 = x2 := mul_right_inj' hu2
  have ey : u ^ 3 * y1 = -(u ^ 3 * y2) ↔ y1 = -y2 := by
    rw [← mul_neg]; exact mul_right_inj' hu3
  unfold slope
  simp only [negY_shortF, ex, ey]
  split_ifs with h1 h2
  · ring
  · simp only [shortF]
    by_cases hy : y1 - -y1 = 0
    · have : u ^ 3 * y1 - -(u ^ 3 * y1) = u ^ 3 * (y1 - -y1) := by ring
      rw [this, hy]; simp
    · field_simp
      ring
  · have hx : x1 - x2 ≠ 0 := sub_ne_zero.mpr h1
    field_simp

lemma add_scale (hu : u ≠ 0) (P Q : (shortF a b).toAffine.Point) :
    scaleP a b u hu (P + Q) = scaleP a b u hu P + scaleP a b u hu Q := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  rcases P with _ | ⟨x1, y1, h1⟩
  · rfl
  rcases Q with _ | ⟨x2, y2, h2⟩
  · rfl
  by_cases hxy : x1 = x2 ∧ y1 = (shortF a b).toAffine.negY x2 y2
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    have h' : u ^ 3 * y1 = (shortF (u ^ 4 * a) (u ^ 6 * b)).toAffine.negY (u ^ 2 * x2) (u ^ 3 * y2) := by
      rw [negY_shortF, hxy.2, negY_shortF]; ring
    exact (Point.add_of_Y_eq (by rw [hxy.1]) h').symm
  · rw [Point.add_some hxy]
    have hxy' : ¬(u ^ 2 * x1 = u ^ 2 * x2 ∧
        u ^ 3 * y1 = (shortF (u ^ 4 * a) (u ^ 6 * b)).toAffine.negY (u ^ 2 * x2) (u ^ 3 * y2)) := by
      rintro ⟨e1, e2⟩; apply hxy
      refine ⟨mul_left_cancel₀ hu2 e1, ?_⟩
      rw [negY_shortF] at e2 ⊢
      apply mul_left_cancel₀ hu3; rw [e2]; ring
    simp only [scaleP]
    rw [Point.add_some hxy']
    simp only [Point.some.injEq]
    rw [slope_scale a b u hu]
    constructor
    · simp only [addX, shortF]; ring
    · simp only [addY, negAddY, addX, negY, shortF]; ring

/-- **The scaling homomorphism.** -/
def scaleHom (hu : u ≠ 0) : (shortF a b).toAffine.Point →+ (shortF (u ^ 4 * a) (u ^ 6 * b)).toAffine.Point where
  toFun := scaleP a b u hu
  map_zero' := rfl
  map_add' := add_scale a b u hu

lemma scaleHom_apply (hu : u ≠ 0) (P : (shortF a b).toAffine.Point) :
    scaleHom a b u hu P = scaleP a b u hu P := rfl

lemma scaleHom_injective (hu : u ≠ 0) : Function.Injective (scaleHom a b u hu) := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  rintro (_ | ⟨x1, y1, h1⟩) (_ | ⟨x2, y2, h2⟩) h
  · rfl
  · simp [scaleHom_apply, scaleP] at h
  · simp [scaleHom_apply, scaleP] at h
  · simp only [scaleHom_apply, scaleP, Point.some.injEq] at h
    obtain ⟨e1, e2⟩ := h
    have e1' := mul_left_cancel₀ hu2 e1
    have e2' := mul_left_cancel₀ hu3 e2
    subst e1'; subst e2'; rfl

/-- A relation on the scaled curve pulls back: independence transfers. -/
theorem indep_of_scale (hu : u ≠ 0) (P Q : (shortF a b).toAffine.Point)
    (h : ∀ m n : ℤ, m • scaleHom a b u hu P = n • scaleHom a b u hu Q → m = 0 ∧ n = 0)
    (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 :=
  h m n (by rw [← map_zsmul, ← map_zsmul, hrel])

end FFHeight

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

omit [CharZero K] in
/-- Every short curve over `K(X)` scales to one with polynomial coefficients. -/
theorem exists_poly_scale (a b : RatFunc K) :
    ∃ u : RatFunc K, u ≠ 0 ∧ ∃ A B : K[X], u ^ 4 * a = ι A ∧ u ^ 6 * b = ι B := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  obtain ⟨na, da, hda0, ha⟩ : ∃ n d : K[X], d ≠ 0 ∧ a = ι n / ι d :=
    ⟨_, _, RatFunc.denom_ne_zero a, (RatFunc.num_div_denom a).symm⟩
  obtain ⟨nb, db, hdb0, hb⟩ : ∃ n d : K[X], d ≠ 0 ∧ b = ι n / ι d :=
    ⟨_, _, RatFunc.denom_ne_zero b, (RatFunc.num_div_denom b).symm⟩
  have hda : ι da ≠ 0 := (map_ne_zero_iff _ hinj).mpr hda0
  have hdb : ι db ≠ 0 := (map_ne_zero_iff _ hinj).mpr hdb0
  refine ⟨ι (da * db), by rw [map_mul]; exact mul_ne_zero hda hdb,
    na * da ^ 3 * db ^ 4, nb * da ^ 6 * db ^ 5, ?_, ?_⟩
  · rw [ha]; simp only [map_mul, map_pow]; field_simp
  · rw [hb]; simp only [map_mul, map_pow]; field_simp

omit [CharZero K] in
lemma shortW_eq (A B : K[X]) : shortW A B = shortF (ι A) (ι B) := rfl

end FFHeight
