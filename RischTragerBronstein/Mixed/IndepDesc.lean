import RischTragerBronstein.Mixed.ClassifyCS
import RischTragerBronstein.Mixed.KFConstTail

/-!
# Descending point codes on curves constant up to scaling

For `A = a v⁴`, `B = b v⁶` (`a b ∈ K`, `v ∈ K[X]`), every point of `y² = x³ + A x + B` over `K(X)`
comes from `E_{a,b}(K)` (`mem_range_ΦCS`). `descPt v` reads off the constant coordinates
`(x / v², y / v³)` of a point code (normalizing the fractions); **`descPt_sound`**: the result
represents a point `P'` of `E_{a,b}(K)` with `ΦCS P' = P`; **`descPt_complete`**: it always answers.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine CPoly

namespace FFHeight

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- Constant point codes on `E_{a,b}` over `K`. -/
def RelC (a b : K) : Option (K × K) → (shortF a b).toAffine.Point → Prop
  | none, .zero => True
  | some (x, y), .some x' y' _ => x = x' ∧ y = y'
  | _, _ => False

/-- The constant value of a fraction (if constant after reduction). -/
def constFr (f : Fr K) : Option K :=
  let g := Fr.norm f
  if isConstK g.1 && isConstK g.2 then some (g.1.headD 0 / g.2.headD 0) else none

lemma constFr_sound {f : Fr K} {c : K} (h : constFr f = some c) (hf : Fr.ok f) :
    Fr.val f = κ c := by
  unfold constFr at h
  dsimp only at h
  split_ifs at h with hc
  cases h
  simp only [Bool.and_eq_true] at hc
  rw [← Fr.val_norm hf]
  simp only [Fr.val, toPoly_of_isConstK hc.1, toPoly_of_isConstK hc.2, RatFunc.algebraMap_C,
    ← map_div₀]
  rfl

lemma constFr_complete {f : Fr K} (hf : Fr.ok f) (c : K) (hv : Fr.val f = κ c) :
    constFr f = some c := by
  obtain ⟨h1, h2, h3⟩ := isConstK_norm f hf c hv
  unfold constFr; dsimp only; rw [if_pos (by rw [h1, h2]; rfl), h3]

/-- **Descent of a point code** by the scaling `v`. -/
def descPt (v : CPoly K) : PtC K → Option (Option (K × K))
  | none => some none
  | some (fx, fy) =>
    match constFr (fx.1, mul fx.2 (powCR v 2)), constFr (fy.1, mul fy.2 (powCR v 3)) with
    | some x0, some y0 => some (some (x0, y0))
    | _, _ => none

open scoped Classical

variable {A B : K[X]} {a b : K}

lemma ΦCS_some (v : K[X]) (hu : ι v ≠ 0) (hA : ι A = ι v ^ 4 * κ a) (hB : ι B = ι v ^ 6 * κ b)
    (c e : K) (hns : (shortF a b).toAffine.Nonsingular c e) :
    ∃ h', ΦCS hu hA hB (Point.some c e hns) = Point.some (ι v ^ 2 * κ c) (ι v ^ 3 * κ e) h' := by
  obtain ⟨h1, e1⟩ := ιK_some a b c e hns
  obtain ⟨h2, e2⟩ := scaleHomEq_some (κ a) (κ b) (ι A) (ι B) (ι v) hu hA hB h1
  unfold ΦCS
  simp only [AddMonoidHom.comp_apply]
  rw [e1, e2, castHom_some]
  exact ⟨h2, rfl⟩

/-- **Soundness of the descent.** -/
theorem descPt_sound (v : CPoly K) (hv : toPoly v ≠ 0) (hA : ι A = ι (toPoly v) ^ 4 * κ a)
    (hB : ι B = ι (toPoly v) ^ 6 * κ b) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hu : ι (toPoly v) ≠ 0) (o : PtC K) (p : Option (K × K)) (hd : descPt v o = some p)
    (P : (shortW A B).toAffine.Point) (hR : Rel A B o P) :
    ∃ P', RelC a b p P' ∧ ΦCS hu hA hB P' = P := by
  obtain ⟨P', hP'⟩ := mem_range_ΦCS hu hA hB hΔ P
  refine ⟨P', ?_, hP'⟩
  rcases o with _ | ⟨fx, fy⟩
  · simp only [descPt, Option.some.injEq] at hd
    subst hd
    rcases P with _ | ⟨x, y, h⟩
    · have : P' = 0 := ΦCS_injective hu hA hB (by rw [hP', map_zero]; rfl)
      subst this; trivial
    · simp [Rel] at hR
  rcases P with _ | ⟨x, y, h⟩
  · simp [Rel] at hR
  obtain ⟨hfx, hfy, rfl, rfl⟩ := hR
  simp only [descPt] at hd
  split at hd
  · rename_i x0 y0 hx0 hy0
    simp only [Option.some.injEq] at hd
    subst hd
    have hok2 : Fr.ok (fx.1, mul fx.2 (powCR v 2)) := by
      show toPoly (mul fx.2 (powCR v 2)) ≠ 0
      rw [toPoly_mul, toPoly_powCR]; exact mul_ne_zero hfx (pow_ne_zero _ hv)
    have hok3 : Fr.ok (fy.1, mul fy.2 (powCR v 3)) := by
      show toPoly (mul fy.2 (powCR v 3)) ≠ 0
      rw [toPoly_mul, toPoly_powCR]; exact mul_ne_zero hfy (pow_ne_zero _ hv)
    have ex := constFr_sound hx0 hok2
    have ey := constFr_sound hy0 hok3
    simp only [Fr.val, toPoly_mul, toPoly_powCR, map_mul, map_pow] at ex ey
    rcases P' with _ | ⟨c, e, hns⟩
    · have h0 : ΦCS hu hA hB (0 : (shortF a b).toAffine.Point) = 0 := map_zero _
      erw [h0] at hP'; cases hP'
    obtain ⟨h', e'⟩ := ΦCS_some (toPoly v) hu hA hB c e hns
    rw [e'] at hP'
    simp only [Point.some.injEq] at hP'
    obtain ⟨hx, hy⟩ := hP'
    have hι2 : ι (toPoly fx.2) ≠ 0 := Fr.ι_ne hfx
    have hι3 : ι (toPoly fy.2) ≠ 0 := Fr.ι_ne hfy
    refine ⟨(algebraMap K (RatFunc K)).injective ?_, (algebraMap K (RatFunc K)).injective ?_⟩
    · simp only [Fr.val] at hx; rw [eq_div_iff hι2] at hx
      rw [← ex, div_eq_iff (mul_ne_zero hι2 (pow_ne_zero 2 hu)), ← hx]; ring
    · simp only [Fr.val] at hy; rw [eq_div_iff hι3] at hy
      rw [← ey, div_eq_iff (mul_ne_zero hι3 (pow_ne_zero 3 hu)), ← hy]; ring
  · exact absurd hd (by simp)

/-- **The descent always answers** on represented points. -/
theorem descPt_complete (v : CPoly K) (hv : toPoly v ≠ 0) (hA : ι A = ι (toPoly v) ^ 4 * κ a)
    (hB : ι B = ι (toPoly v) ^ 6 * κ b) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hu : ι (toPoly v) ≠ 0) (o : PtC K) (P : (shortW A B).toAffine.Point) (hR : Rel A B o P) :
    (descPt v o).isSome := by
  rcases o with _ | ⟨fx, fy⟩
  · rfl
  rcases P with _ | ⟨x, y, h⟩
  · simp [Rel] at hR
  obtain ⟨hfx, hfy, rfl, rfl⟩ := hR
  obtain ⟨P', hP'⟩ := mem_range_ΦCS hu hA hB hΔ (Point.some _ _ h)
  rcases P' with _ | ⟨c, e, hns⟩
  · have h0 : ΦCS hu hA hB (0 : (shortF a b).toAffine.Point) = 0 := map_zero _
    erw [h0] at hP'; cases hP'
  obtain ⟨h', e'⟩ := ΦCS_some (toPoly v) hu hA hB c e hns
  rw [e'] at hP'
  simp only [Point.some.injEq] at hP'
  obtain ⟨hx, hy⟩ := hP'
  have hok2 : Fr.ok (fx.1, mul fx.2 (powCR v 2)) := by
    show toPoly (mul fx.2 (powCR v 2)) ≠ 0
    rw [toPoly_mul, toPoly_powCR]; exact mul_ne_zero hfx (pow_ne_zero _ hv)
  have hok3 : Fr.ok (fy.1, mul fy.2 (powCR v 3)) := by
    show toPoly (mul fy.2 (powCR v 3)) ≠ 0
    rw [toPoly_mul, toPoly_powCR]; exact mul_ne_zero hfy (pow_ne_zero _ hv)
  have hι2 : ι (toPoly fx.2) ≠ 0 := Fr.ι_ne hfx
  have hι3 : ι (toPoly fy.2) ≠ 0 := Fr.ι_ne hfy
  have c1 := constFr_complete hok2 c (by
    simp only [Fr.val, toPoly_mul, toPoly_powCR, map_mul, map_pow]
    have : Fr.val fx = ι (toPoly v) ^ 2 * κ c := hx.symm
    simp only [Fr.val] at this
    field_simp; rw [div_eq_iff hι2] at this; rw [this]; ring)
  have c2 := constFr_complete hok3 e (by
    simp only [Fr.val, toPoly_mul, toPoly_powCR, map_mul, map_pow]
    have : Fr.val fy = ι (toPoly v) ^ 3 * κ e := hy.symm
    simp only [Fr.val] at this
    field_simp; rw [div_eq_iff hι3] at this; rw [this]; ring)
  simp [descPt, c1, c2]

end FFHeight
