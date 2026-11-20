import RischTragerBronstein.Mixed.AbelSum
import RischTragerBronstein.Mixed.EllTrans

/-!
# Abel's theorem for a general cubic `y² = c₃x³ + c₂x² + c₁x + c₀`

The general form of `AbelSum`: Mathlib's curve `W' : Y² = X³ + c₂X² + c₁c₃X + c₀c₃²` (`WG`) with
the point `(X, Y)` of `W'` at `(X/c₃, Y/c₃)` on `y² = p(x)` (`δG`). The line through two points of
`W'` corresponds to `y = ℓx + (Y₁ − ℓX₁)/c₃` (`line_poly_gen`: `(ℓx + ν)² − p = −c₃ ∏ (x − Xᵢ/c₃)`),
the vertical at `R` to `x − X_R/c₃`. **`abel_sumG`**: a function with affine divisor `∑ nᵢ δG Pᵢ`
forces `∑ nᵢ Pᵢ = 0` in `W'(C)`. This covers the curves `θ² = A(t)`, `deg A = 3`, of the
`kxDecide` Mordell–Weil exception.
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

namespace SuperData

open scoped Classical

variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [Algebra C L]
variable {S : SuperData C L} {c3 c2 c1 c0 : C}

/-- Mathlib's model `Y² = X³ + c₂X² + c₁c₃X + c₀c₃²`. -/
abbrev WG (c3 c2 c1 c0 : C) : Affine C := (FFHeight.longF c2 (c1 * c3) (c0 * c3 ^ 2)).toAffine

variable (c3 c2 c1 c0) in
/-- The indicator of the point `(X/c₃, Y/c₃)` (`0` for the origin). -/
noncomputable def δG : (WG c3 c2 c1 c0).Point → C × C → ℤ
  | .zero => 0
  | .some x y _ => fun Q ↦ if Q = (x / c3, y / c3) then 1 else 0

lemma eq_of_pointG {x y : C} (h : (WG c3 c2 c1 c0).Nonsingular x y) :
    y ^ 2 = x ^ 3 + c2 * x ^ 2 + c1 * c3 * x + c0 * c3 ^ 2 := by
  have := (equation_iff x y).mp h.1
  simp [FFHeight.longF] at this; linear_combination this

lemma negY_G (x y : C) : (WG c3 c2 c1 c0).negY x y = -y := by simp [negY, FFHeight.longF]

/-- **The cubic of a line, general form.** -/
theorem line_poly_gen (hc3 : c3 ≠ 0) (x1 y1 x2 y2 : C) (h1 : (WG c3 c2 c1 c0).Equation x1 y1)
    (h2 : (WG c3 c2 c1 c0).Equation x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = (WG c3 c2 c1 c0).negY x2 y2)) :
    (Polynomial.C ((WG c3 c2 c1 c0).slope x1 x2 y1 y2) * X +
        Polynomial.C ((y1 - (WG c3 c2 c1 c0).slope x1 x2 y1 y2 * x1) / c3)) ^ 2 -
        (Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X + Polynomial.C c0) =
      -(Polynomial.C c3 * ((X - Polynomial.C (x1 / c3)) * (X - Polynomial.C (x2 / c3)) *
        (X - Polynomial.C ((WG c3 c2 c1 c0).addX x1 x2
          ((WG c3 c2 c1 c0).slope x1 x2 y1 y2) / c3)))) := by
  have key := addPolynomial_slope h1 h2 hxy
  generalize (WG c3 c2 c1 c0).slope x1 x2 y1 y2 = ℓ at key ⊢
  generalize hx3 : (WG c3 c2 c1 c0).addX x1 x2 ℓ = x3 at key ⊢
  simp only [addPolynomial, linePolynomial, Affine.polynomial, FFHeight.longF] at key
  apply Polynomial.funext
  intro t
  have := congrArg (Polynomial.eval (c3 * t)) key
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_neg, map_zero, zero_mul,
    add_zero, sub_zero, map_sub, map_mul, map_add, map_pow] at this ⊢
  field_simp
  linear_combination this


variable (hn2 : S.n = 2) (hc3 : c3 ≠ 0)
  (hpE : S.p = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X + Polynomial.C c0)
include hn2 hc3 hpE

lemma curve_eqG {α β : C} (hv : β ^ S.n = (S.p.map (algebraMap C C)).eval α) :
    β ^ 2 = c3 * α ^ 3 + c2 * α ^ 2 + c1 * α + c0 := by
  have h := hv; rw [hn2] at h; rw [h, hpE]; simp

lemma pt_eqG {x y : C} (h : (WG c3 c2 c1 c0).Nonsingular x y) :
    (y / c3) ^ 2 = c3 * (x / c3) ^ 3 + c2 * (x / c3) ^ 2 + c1 * (x / c3) + c0 := by
  have := eq_of_pointG h
  have key : c3 * (x / c3) ^ 3 + c2 * (x / c3) ^ 2 + c1 * (x / c3) + c0 - (y / c3) ^ 2 =
      (x ^ 3 + c2 * x ^ 2 + c1 * c3 * x + c0 * c3 ^ 2 - y ^ 2) / c3 ^ 2 := by
    field_simp; try ring
  rw [this, sub_self, zero_div] at key
  linear_combination -key

open Classical in
/-- **The divisor of a line, general form.** -/
theorem ordAt_line_three_gen (x1 y1 x2 y2 : C) (h1 : (WG c3 c2 c1 c0).Equation x1 y1)
    (h2 : (WG c3 c2 c1 c0).Equation x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = (WG c3 c2 c1 c0).negY x2 y2)) (α β : C)
    (hv : β ^ S.n = (S.p.map (algebraMap C C)).eval α) :
    let ℓ := (WG c3 c2 c1 c0).slope x1 x2 y1 y2
    let x3 := (WG c3 c2 c1 c0).addX x1 x2 ℓ
    S.ordAt C (S.lineF ℓ ((y1 - ℓ * x1) / c3)) α β =
      (if α = x1 / c3 ∧ β = y1 / c3 then 1 else 0) +
      (if α = x2 / c3 ∧ β = y2 / c3 then 1 else 0) +
      (if α = x3 / c3 ∧ β = (ℓ * x3 + (y1 - ℓ * x1)) / c3 then 1 else 0) := by
  intro ℓ x3
  set ν := (y1 - ℓ * x1) / c3 with hν
  have hpoly := line_poly_gen hc3 x1 y1 x2 y2 h1 h2 hxy
  have hqe : (Polynomial.C ℓ * X + Polynomial.C ν) ^ 2 - S.p =
      Polynomial.C (-c3) * ((X - Polynomial.C (x1 / c3)) * (X - Polynomial.C (x2 / c3)) *
        (X - Polynomial.C (x3 / c3))) := by
    rw [hpE, hpoly, map_neg, neg_mul]
  have hprod : ((X - Polynomial.C (x1 / c3)) * (X - Polynomial.C (x2 / c3)) *
      (X - Polynomial.C (x3 / c3)) : C[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  have hq : (Polynomial.C ℓ * X + Polynomial.C ν) ^ 2 - S.p ≠ 0 := by
    rw [hqe]; exact mul_ne_zero (by simpa using hc3) hprod
  rw [S.ordAt_line_all (K := C) hn2 ℓ ν hq α β hv, hqe]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.map_id]
  have hy2 : y2 = ℓ * x2 + (y1 - ℓ * x1) := by
    by_cases hx : x1 = x2
    · have hy : y1 ≠ (WG c3 c2 c1 c0).negY x2 y2 := fun h ↦ hxy ⟨hx, h⟩
      have := Y_eq_of_Y_ne h1 h2 hx hy
      rw [← hx, ← this]; ring
    · have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
      have hl : ℓ = (y1 - y2) / (x1 - x2) := slope_of_X_ne hx
      rw [hl]; field_simp; ring
  have hmul : (Polynomial.C (-c3) * ((X - Polynomial.C (x1 / c3)) * (X - Polynomial.C (x2 / c3)) *
      (X - Polynomial.C (x3 / c3)))).rootMultiplicity α =
      (if α = x1 / c3 then 1 else 0) + (if α = x2 / c3 then 1 else 0) +
        (if α = x3 / c3 then 1 else 0) := by
    rw [rootMultiplicity_mul (mul_ne_zero (by simpa using hc3) hprod), rootMultiplicity_C, zero_add,
      rootMultiplicity_mul hprod,
      rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
  have on1 : y1 / c3 = ℓ * (x1 / c3) + ν := by rw [hν]; field_simp; try ring
  have on2 : y2 / c3 = ℓ * (x2 / c3) + ν := by rw [hν, hy2]; field_simp; try ring
  have on3 : (ℓ * x3 + (y1 - ℓ * x1)) / c3 = ℓ * (x3 / c3) + ν := by rw [hν]; field_simp; try ring
  by_cases hon : β = ℓ * α + ν
  · rw [if_pos hon, hmul]
    have e1 : (α = x1 / c3 ∧ β = y1 / c3) ↔ α = x1 / c3 :=
      ⟨fun h ↦ h.1, fun h ↦ ⟨h, by rw [hon, h, on1]⟩⟩
    have e2 : (α = x2 / c3 ∧ β = y2 / c3) ↔ α = x2 / c3 :=
      ⟨fun h ↦ h.1, fun h ↦ ⟨h, by rw [hon, h, on2]⟩⟩
    have e3 : (α = x3 / c3 ∧ β = (ℓ * x3 + (y1 - ℓ * x1)) / c3) ↔ α = x3 / c3 :=
      ⟨fun h ↦ h.1, fun h ↦ ⟨h, by rw [hon, h, on3]⟩⟩
    simp only [e1, e2, e3]
    push_cast
    split_ifs <;> simp
  · rw [if_neg hon]
    have n1 : ¬(α = x1 / c3 ∧ β = y1 / c3) := by
      rintro ⟨h, h'⟩; apply hon; rw [h', h, on1]
    have n2 : ¬(α = x2 / c3 ∧ β = y2 / c3) := by
      rintro ⟨h, h'⟩; apply hon; rw [h', h, on2]
    have n3 : ¬(α = x3 / c3 ∧ β = (ℓ * x3 + (y1 - ℓ * x1)) / c3) := by
      rintro ⟨h, h'⟩; apply hon; rw [h', h, on3]
    rw [if_neg n1, if_neg n2, if_neg n3]; rfl

/-- **Verticals, general form**: `x − X_R/c₃` has divisor `δG R + δG (−R)`. -/
lemma divIs_vertG (x y : C) (h : (WG c3 c2 c1 c0).Nonsingular x y) :
    S.DivIs (S.polyX (X - Polynomial.C (x / c3)))
      (δG c3 c2 c1 c0 (Point.some x y h) + δG c3 c2 c1 c0 (-Point.some x y h)) := by
  intro α β hv
  rw [S.ordAt_polyX _ (X_sub_C_ne_zero (x / c3)) α β hv]
  simp only [Point.neg_some, δG, Pi.add_apply, Prod.mk.injEq]
  rw [negY_G, Algebra.algebraMap_self, Polynomial.map_id, rootMultiplicity_X_sub_C]
  have hc := curve_eqG hn2 hc3 hpE hv
  have hP := pt_eqG hn2 hc3 hpE h
  by_cases hα : α = x / c3
  · subst hα
    have hb : β ^ 2 = (y / c3) ^ 2 := by rw [hc, hP]
    have hb' : (β - y / c3) * (β + y / c3) = 0 := by linear_combination hb
    have hneg : -y / c3 = -(y / c3) := neg_div _ _
    rcases mul_eq_zero.mp hb' with h1 | h1
    · have hβ : β = y / c3 := sub_eq_zero.mp h1
      rw [hneg, hβ]
      by_cases h0 : y / c3 = 0
      · rw [h0]; simp [hn2]
      · have hne : ¬ y / c3 = -(y / c3) := fun h ↦ h0 (by linear_combination h / 2)
        simp [h0, hne]
    · have hβ : β = -(y / c3) := by linear_combination h1
      rw [hneg, hβ]
      by_cases h0 : y / c3 = 0
      · rw [h0]; simp [hn2]
      · have hne : ¬ -(y / c3) = y / c3 := fun h ↦ h0 (by linear_combination -h / 2)
        have hne' : -(y / c3) ≠ 0 := neg_ne_zero.mpr h0
        simp [hne, hne']
  · simp [hα]

/-- **Lines, general form.** -/
lemma divIs_lineG (x1 y1 x2 y2 : C) (h1 : (WG c3 c2 c1 c0).Nonsingular x1 y1)
    (h2 : (WG c3 c2 c1 c0).Nonsingular x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = (WG c3 c2 c1 c0).negY x2 y2)) :
    S.DivIs (S.lineF ((WG c3 c2 c1 c0).slope x1 x2 y1 y2)
        ((y1 - (WG c3 c2 c1 c0).slope x1 x2 y1 y2 * x1) / c3))
      (δG c3 c2 c1 c0 (Point.some x1 y1 h1) + δG c3 c2 c1 c0 (Point.some x2 y2 h2) +
        δG c3 c2 c1 c0 (-(Point.some x1 y1 h1 + Point.some x2 y2 h2))) := by
  intro α β hv
  have := ordAt_line_three_gen hn2 hc3 hpE x1 y1 x2 y2 h1.1 h2.1 hxy α β hv
  rw [this, Point.add_some hxy, Point.neg_some]
  simp only [δG, Pi.add_apply, Prod.mk.injEq]
  have e : (WG c3 c2 c1 c0).negY ((WG c3 c2 c1 c0).addX x1 x2 ((WG c3 c2 c1 c0).slope x1 x2 y1 y2))
      ((WG c3 c2 c1 c0).addY x1 x2 y1 ((WG c3 c2 c1 c0).slope x1 x2 y1 y2)) =
      (WG c3 c2 c1 c0).slope x1 x2 y1 y2 * (WG c3 c2 c1 c0).addX x1 x2 ((WG c3 c2 c1 c0).slope x1 x2 y1 y2) +
        (y1 - (WG c3 c2 c1 c0).slope x1 x2 y1 y2 * x1) := by
    rw [addY, negY_negY]; simp only [negAddY, FFHeight.longF]; ring
  rw [e]

omit hn2 hc3 hpE in
lemma δG_nonneg (P : (WG c3 c2 c1 c0).Point) (z : C × C) : 0 ≤ δG c3 c2 c1 c0 P z := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [δG]
  · simp only [δG]; split_ifs <;> norm_num

omit hn2 hc3 hpE in
lemma δG_self (x y : C) (h : (WG c3 c2 c1 c0).Nonsingular x y) :
    δG c3 c2 c1 c0 (Point.some x y h) (x / c3, y / c3) = 1 := by
  simp [δG]

lemma point_onG (x y : C) (h : (WG c3 c2 c1 c0).Nonsingular x y) :
    (y / c3) ^ S.n = (S.p.map (algebraMap C C)).eval (x / c3) := by
  have := pt_eqG hn2 hc3 hpE h
  rw [hn2, hpE]
  simp only [Algebra.algebraMap_self, Polynomial.map_id, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  exact this

/-- **For all `P, Q`: a function with divisor `δ P + δ Q − δ (P + Q)`.** -/
lemma exists_gG (P Q : (WG c3 c2 c1 c0).Point) :
    ∃ g : C⟮S.x⟯⟮S.y⟯, g ≠ 0 ∧ S.DivIs g (δG c3 c2 c1 c0 P + δG c3 c2 c1 c0 Q - δG c3 c2 c1 c0 (P + Q)) := by
  rcases P with _ | ⟨x1, y1, h1⟩
  · refine ⟨1, one_ne_zero, divIs_congr divIs_one ?_⟩
    have e : (Point.zero : (WG c3 c2 c1 c0).Point) + Q = Q := zero_add Q
    rw [e]; funext z; simp [δG]
  rcases Q with _ | ⟨x2, y2, h2⟩
  · refine ⟨1, one_ne_zero, divIs_congr divIs_one ?_⟩
    have e : Point.some x1 y1 h1 + (Point.zero : (WG c3 c2 c1 c0).Point) = Point.some x1 y1 h1 := add_zero _
    rw [e]; funext z; simp [δG]
  by_cases hxy : x1 = x2 ∧ y1 = (WG c3 c2 c1 c0).negY x2 y2
  · -- `Q = −P`: the vertical at `P`
    have hv := divIs_vertG (S := S) hn2 hc3 hpE x1 y1 h1
    refine ⟨S.polyX (X - Polynomial.C (x1 / c3)), S.polyX_ne_zero (X_sub_C_ne_zero (x1 / c3)), divIs_congr hv ?_⟩
    rw [Point.add_of_Y_eq hxy.1 hxy.2]
    have hQ : -Point.some x1 y1 h1 = Point.some x2 y2 h2 := by
      rw [Point.neg_some]; simp only [Point.some.injEq]
      refine ⟨hxy.1, ?_⟩
      rw [hxy.2, ← hxy.1, negY_negY]
    rw [hQ]; funext z; simp [δG]
  · -- the line through `P, Q` over the vertical at `P + Q`
    have hl := divIs_lineG (S := S) hn2 hc3 hpE x1 y1 x2 y2 h1 h2 hxy
    set R := Point.some x1 y1 h1 + Point.some x2 y2 h2 with hR
    have hRe : R = Point.some _ _ (nonsingular_add h1 h2 hxy) := Point.add_some hxy
    set x3 := (WG c3 c2 c1 c0).addX x1 x2 ((WG c3 c2 c1 c0).slope x1 x2 y1 y2)
    set y3 := (WG c3 c2 c1 c0).addY x1 x2 y1 ((WG c3 c2 c1 c0).slope x1 x2 y1 y2)
    have h3 : (WG c3 c2 c1 c0).Nonsingular x3 y3 := nonsingular_add h1 h2 hxy
    have hvt := divIs_vertG (S := S) hn2 hc3 hpE x3 y3 h3
    have hlne : S.lineF ((WG c3 c2 c1 c0).slope x1 x2 y1 y2) ((y1 - (WG c3 c2 c1 c0).slope x1 x2 y1 y2 * x1) / c3) ≠ 0 :=
      ne_zero_of_divIs hl (x1 / c3) (y1 / c3) (point_onG hn2 hc3 hpE x1 y1 h1) (by
        have e1 := δG_self x1 y1 h1
        have e2 := δG_nonneg (Point.some x2 y2 h2) (x1 / c3, y1 / c3)
        have e3 := δG_nonneg (-R) (x1 / c3, y1 / c3)
        simp only [Pi.add_apply]; omega)
    have hvne : S.polyX (X - Polynomial.C (x3 / c3)) ≠ 0 := S.polyX_ne_zero (X_sub_C_ne_zero (x3 / c3))
    refine ⟨_ * (S.polyX (X - Polynomial.C (x3 / c3)))⁻¹, mul_ne_zero hlne (inv_ne_zero hvne),
      divIs_congr (divIs_mul hlne (inv_ne_zero hvne) hl (divIs_inv hvt)) ?_⟩
    rw [hRe]
    funext z; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring

/-- The divisor `∑ nᵢ δ Pᵢ` and the sum `∑ nᵢ Pᵢ` of a list. -/
noncomputable def divLG : List (ℤ × (WG c3 c2 c1 c0).Point) → C × C → ℤ
  | [] => 0
  | e :: l => e.1 • δG c3 c2 c1 c0 e.2 + divLG l

/-- The group sum `∑ nᵢ Pᵢ`. -/
noncomputable def sumLG : List (ℤ × (WG c3 c2 c1 c0).Point) → (WG c3 c2 c1 c0).Point
  | [] => 0
  | e :: l => e.1 • e.2 + sumLG l

/-- **Adding `n` copies of `P`.** -/
lemma step_nG (E : C × C → ℤ) (s P : (WG c3 c2 c1 c0).Point) (h : C⟮S.x⟯⟮S.y⟯) (hh : h ≠ 0)
    (hd : S.DivIs h (E - δG c3 c2 c1 c0 s)) (n : ℤ) :
    ∃ h' : C⟮S.x⟯⟮S.y⟯, h' ≠ 0 ∧ S.DivIs h' (E + n • δG c3 c2 c1 c0 P - δG c3 c2 c1 c0 (s + n • P)) := by
  induction n using Int.induction_on with
  | zero => exact ⟨h, hh, divIs_congr hd (by simp)⟩
  | succ k ih =>
    obtain ⟨h', hh', hd'⟩ := ih
    obtain ⟨g, hg, hdg⟩ := exists_gG (S := S) hn2 hc3 hpE (s + (k : ℤ) • P) P
    refine ⟨h' * g, mul_ne_zero hh' hg, divIs_mul' hh' hg hd' hdg ?_⟩
    have e : s + ((k : ℤ) + 1) • P = s + (k : ℤ) • P + P := by rw [add_smul, one_smul, add_assoc]
    push_cast
    rw [e]
    funext z; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  | pred k ih =>
    obtain ⟨h', hh', hd'⟩ := ih
    obtain ⟨g, hg, hdg⟩ := exists_gG (S := S) hn2 hc3 hpE (s + (-(k : ℤ) - 1) • P) P
    refine ⟨h' * g⁻¹, mul_ne_zero hh' (inv_ne_zero hg), divIs_mul' hh' (inv_ne_zero hg) hd'
      (divIs_inv hdg) ?_⟩
    have e : s + (-(k : ℤ) - 1) • P + P = s + -(k : ℤ) • P := by
      rw [sub_smul, one_smul]; abel
    rw [e]
    funext z; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring

/-- **A function with divisor `∑ nᵢ δ Pᵢ − δ (∑ nᵢ Pᵢ)`.** -/
lemma exists_hG (l : List (ℤ × (WG c3 c2 c1 c0).Point)) :
    ∃ h : C⟮S.x⟯⟮S.y⟯, h ≠ 0 ∧ S.DivIs h (divLG l - δG c3 c2 c1 c0 (sumLG l)) := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, divIs_congr divIs_one (by funext z; simp [divLG, sumLG]; rfl)⟩
  | cons e l ih =>
    obtain ⟨h, hh, hd⟩ := ih
    obtain ⟨h', hh', hd'⟩ := step_nG (S := S) hn2 hc3 hpE (divLG l) (sumLG l) e.2 h hh hd e.1
    refine ⟨h', hh', divIs_congr hd' ?_⟩
    simp only [divLG, sumLG]
    rw [add_comm (sumLG l)]
    funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring

/-- **Abel's theorem (the direction needed)**: a function with affine divisor `∑ nᵢ (Pᵢ)` forces
`∑ nᵢ Pᵢ = 0` in the group of points. -/
theorem abel_sumG (l : List (ℤ × (WG c3 c2 c1 c0).Point)) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hdiv : S.DivIs w (divLG l)) : sumLG l = 0 := by
  obtain ⟨h, hh, hd⟩ := exists_hG (S := S) hn2 hc3 hpE l
  have hq := divIs_mul' hw (inv_ne_zero hh) hdiv (divIs_inv hd) (F := δG c3 c2 c1 c0 (sumLG l))
    (by funext z; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring)
  by_contra hs
  rcases hR : sumLG l with _ | ⟨α₀, β₀, h₀⟩
  · exact hs hR
  rw [hR] at hq
  have hd3 : S.p.natDegree = 3 := by rw [hpE]; compute_degree!
  refine S.no_simple_pole (K := C) hn2 hd3 _ (mul_ne_zero hw (inv_ne_zero hh)) (α₀ / c3) (β₀ / c3)
    (point_onG hn2 hc3 hpE α₀ β₀ h₀) (fun α β hv ↦ ?_)
  rw [hq α β hv]
  simp only [δG, Prod.mk.injEq]

section Nonsing

omit hn2 hc3 hpE [IsAlgClosed C] in
/-- **Every point of the model of a squarefree cubic is nonsingular**: `(X, Y)` with
`Y² = X³ + c₂X² + c₁c₃X + c₀c₃²` and `p = c₃X³ + c₂X² + c₁X + c₀` separable. -/
theorem ns_of_eq {c3 c2 c1 c0 : C} (hc3 : c3 ≠ 0)
    (hsep : (Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0).Separable) (x y : C)
    (h : y ^ 2 = x ^ 3 + c2 * x ^ 2 + c1 * c3 * x + c0 * c3 ^ 2) :
    (WG c3 c2 c1 c0).Nonsingular x y := by
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [FFHeight.longF]; linear_combination h, ?_⟩
  simp only [WG, FFHeight.longF, zero_mul, sub_zero, zero_sub]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hy : y = 0 := by linear_combination h2 / 2
  set α := x / c3
  have hp : (Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0).eval α = 0 := by
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, α]
    rw [hy] at h
    field_simp
    linear_combination -h
  have hd := hsep.aeval_derivative_ne_zero (x := α) (by simpa using hp)
  apply hd
  have hder : derivative (Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0) = Polynomial.C (3 * c3) * X ^ 2 + Polynomial.C (2 * c2) * X + Polynomial.C c1 := by
    simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X, zero_mul,
      zero_add, map_mul]
    simp only [Polynomial.C_ofNat, Nat.cast_ofNat]; ring
  rw [hder, aeval_def, eval₂_eq_eval_map, Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, Algebra.algebraMap_self, RingHom.id_apply]
  have hx : x = c3 * α := by simp only [α]; field_simp
  rw [hx] at h1
  have : c3 * (3 * c3 * α ^ 2 + 2 * c2 * α + c1) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hc3
  · linear_combination h0

end Nonsing

end SuperData

end Differential
