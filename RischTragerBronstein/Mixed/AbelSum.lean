import RischTragerBronstein.Mixed.AbelLine2
import RischTragerBronstein.Algebraic.AbelPole

/-!
# Abel's theorem for `y² = x³ + a x + b` (Abel bridge, step B3)

Over an algebraically closed `C`, for the superelliptic `S : y² = x³ + ax + b` and Mathlib's group
`W(C)` of `y² = x³ + ax + b`: **if `w ≠ 0` has affine divisor `∑ nᵢ (Pᵢ)`, then `∑ nᵢ Pᵢ = 0`**
(`abel_sum`). Divisors are functions `C × C → ℤ` (`DivIs w D`: `ord_{(α,β)} w = D(α, β)` on the
curve), `δ P` the indicator of an affine point. Lines and verticals give, for all `P, Q`, a function
`g` with divisor `δ P + δ Q − δ (P + Q)` (`exists_g`); multiplying them along the divisor gives `h`
with divisor `∑ nᵢ δ Pᵢ − δ (∑ nᵢ Pᵢ)` (`exists_h`), and `w / h` has divisor `δ R`, which is
impossible for `R ≠ 0` (`no_simple_pole`).
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

namespace SuperData

open scoped Classical

variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [Algebra C L]
variable (S : SuperData C L) (a b : C)

/-- The short curve over `C`. -/
abbrev WA (a b : C) : Affine C := (FFHeight.shortF a b).toAffine


/-- `w` has (affine) divisor `D`. -/
def DivIs (w : C⟮S.x⟯⟮S.y⟯) (D : C × C → ℤ) : Prop :=
  ∀ α β : C, β ^ S.n = (S.p.map (algebraMap C C)).eval α → S.ordAt C w α β = D (α, β)

/-- The indicator of a point (`0` for the origin). -/
noncomputable def δ : (WA a b).Point → C × C → ℤ
  | .zero => 0
  | .some x y _ => fun Q ↦ if Q = (x, y) then 1 else 0

variable {S a b}

lemma divIs_mul {f g : C⟮S.x⟯⟮S.y⟯} {D E : C × C → ℤ} (hf : f ≠ 0) (hg : g ≠ 0)
    (h1 : S.DivIs f D) (h2 : S.DivIs g E) : S.DivIs (f * g) (D + E) := fun α β hv ↦ by
  rw [S.ordAt_mul hv hf hg, h1 α β hv, h2 α β hv]; rfl

lemma divIs_inv {f : C⟮S.x⟯⟮S.y⟯} {D : C × C → ℤ} (h1 : S.DivIs f D) : S.DivIs f⁻¹ (-D) :=
  fun α β hv ↦ by rw [S.ordAt_inv, h1 α β hv]; exacts [rfl, hv]

lemma divIs_one : S.DivIs 1 0 := fun α β hv ↦ by
  have h := S.ordAt_mul (K := C) hv (one_ne_zero (α := C⟮S.x⟯⟮S.y⟯)) one_ne_zero
  rw [mul_one] at h
  simp only [Pi.zero_apply]; omega

lemma divIs_congr {f : C⟮S.x⟯⟮S.y⟯} {D E : C × C → ℤ} (h : S.DivIs f D) (hDE : D = E) :
    S.DivIs f E := hDE ▸ h

variable (hn2 : S.n = 2) (hpE : S.p = X ^ 3 + Polynomial.C a * X + Polynomial.C b)
include hn2 hpE

lemma curve_eq {α β : C} (hv : β ^ S.n = (S.p.map (algebraMap C C)).eval α) :
    β ^ 2 = α ^ 3 + a * α + b := by
  rw [← hn2, hv, hpE]; simp

lemma eq_of_point {x y : C} (h : (WA a b).Nonsingular x y) : y ^ 2 = x ^ 3 + a * x + b := by
  have := (equation_iff x y).mp h.1
  simpa [FFHeight.shortF] using this

/-- **Verticals**: `x − x_R` has divisor `δ R + δ (−R)`. -/
lemma divIs_vert (x y : C) (h : (WA a b).Nonsingular x y) :
    S.DivIs (S.polyX (X - Polynomial.C x)) (δ a b (Point.some x y h) + δ a b (-Point.some x y h)) := by
  intro α β hv
  rw [S.ordAt_polyX _ (X_sub_C_ne_zero x) α β hv]
  simp only [Point.neg_some, δ, Pi.add_apply, Prod.mk.injEq]
  rw [FFHeight.negY_shortF, Algebra.algebraMap_self, Polynomial.map_id, rootMultiplicity_X_sub_C]
  have hc := curve_eq hn2 hpE hv
  have hP := eq_of_point hn2 hpE h
  by_cases hα : α = x
  · subst hα
    have hb : β ^ 2 = y ^ 2 := by rw [hc, hP]
    have hb' : (β - y) * (β + y) = 0 := by linear_combination hb
    rcases mul_eq_zero.mp hb' with h1 | h1
    · have hβ : β = y := sub_eq_zero.mp h1
      subst hβ
      by_cases h0 : β = 0
      · subst h0; simp [hn2]
      · have hne : ¬ β = -β := fun h ↦ h0 (by linear_combination h / 2)
        simp [h0, hne]
    · have hβ : β = -y := by linear_combination h1
      subst hβ
      by_cases h0 : y = 0
      · subst h0; simp [hn2]
      · have hne : ¬ -y = y := fun h ↦ h0 (by linear_combination -h / 2)
        have hne' : -y ≠ 0 := neg_ne_zero.mpr h0
        simp [hne, hne']
  · simp [hα]

/-- **Lines**: for `P ≠ −Q` affine, the line has divisor `δ P + δ Q + δ (−(P + Q))`. -/
lemma divIs_line (x1 y1 x2 y2 : C) (h1 : (WA a b).Nonsingular x1 y1) (h2 : (WA a b).Nonsingular x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = (WA a b).negY x2 y2)) :
    S.DivIs (S.lineF ((WA a b).slope x1 x2 y1 y2) (y1 - (WA a b).slope x1 x2 y1 y2 * x1))
      (δ a b (Point.some x1 y1 h1) + δ a b (Point.some x2 y2 h2) +
        δ a b (-(Point.some x1 y1 h1 + Point.some x2 y2 h2))) := by
  intro α β hv
  have := S.ordAt_line_three (K := C) hn2 a b hpE x1 y1 x2 y2 h1.1 h2.1 hxy α β hv
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [this, Point.add_some hxy, Point.neg_some]
  simp only [δ, Pi.add_apply, Prod.mk.injEq]
  have e : (WA a b).negY ((WA a b).addX x1 x2 ((WA a b).slope x1 x2 y1 y2)) ((WA a b).addY x1 x2 y1 ((WA a b).slope x1 x2 y1 y2)) =
      (WA a b).slope x1 x2 y1 y2 * (WA a b).addX x1 x2 ((WA a b).slope x1 x2 y1 y2) + (y1 - (WA a b).slope x1 x2 y1 y2 * x1) := by
    rw [addY, negY_negY]; simp only [negAddY]; ring
  rw [e]

omit hn2 hpE in
lemma δ_nonneg (P : (WA a b).Point) (z : C × C) : 0 ≤ δ a b P z := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [δ]
  · simp only [δ]; split_ifs <;> norm_num

omit hn2 hpE in
lemma δ_self (x y : C) (h : (WA a b).Nonsingular x y) : δ a b (Point.some x y h) (x, y) = 1 := by
  simp [δ]

omit hn2 hpE in
lemma ne_zero_of_divIs {f : C⟮S.x⟯⟮S.y⟯} {D : C × C → ℤ} (h : S.DivIs f D) (α β : C)
    (hv : β ^ S.n = (S.p.map (algebraMap C C)).eval α) (hD : D (α, β) ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply hD
  rw [← h α β hv]
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C C)).eval α = 0 := by rw [← hv, zero_pow S.hn.ne']
    obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
    rw [S.ordAt_br _ α γ he hγ hγp, map_zero, HahnSeries.order_zero]
  · rw [S.ordAt_nb _ α β hβ hv, map_zero, HahnSeries.order_zero]

lemma point_on (x y : C) (h : (WA a b).Nonsingular x y) :
    y ^ S.n = (S.p.map (algebraMap C C)).eval x := by
  rw [hn2, eq_of_point hn2 hpE h, hpE]; simp

/-- **For all `P, Q`: a function with divisor `δ P + δ Q − δ (P + Q)`.** -/
lemma exists_g (P Q : (WA a b).Point) :
    ∃ g : C⟮S.x⟯⟮S.y⟯, g ≠ 0 ∧ S.DivIs g (δ a b P + δ a b Q - δ a b (P + Q)) := by
  rcases P with _ | ⟨x1, y1, h1⟩
  · refine ⟨1, one_ne_zero, divIs_congr divIs_one ?_⟩
    have e : (Point.zero : (WA a b).Point) + Q = Q := zero_add Q
    rw [e]; funext z; simp [δ]
  rcases Q with _ | ⟨x2, y2, h2⟩
  · refine ⟨1, one_ne_zero, divIs_congr divIs_one ?_⟩
    have e : Point.some x1 y1 h1 + (Point.zero : (WA a b).Point) = Point.some x1 y1 h1 := add_zero _
    rw [e]; funext z; simp [δ]
  by_cases hxy : x1 = x2 ∧ y1 = (WA a b).negY x2 y2
  · -- `Q = −P`: the vertical at `P`
    have hv := divIs_vert (S := S) hn2 hpE x1 y1 h1
    refine ⟨S.polyX (X - Polynomial.C x1), S.polyX_ne_zero (X_sub_C_ne_zero x1), divIs_congr hv ?_⟩
    rw [Point.add_of_Y_eq hxy.1 hxy.2]
    have hQ : -Point.some x1 y1 h1 = Point.some x2 y2 h2 := by
      rw [Point.neg_some]; simp only [Point.some.injEq]
      refine ⟨hxy.1, ?_⟩
      rw [hxy.2, ← hxy.1, negY_negY]
    rw [hQ]; funext z; simp [δ]
  · -- the line through `P, Q` over the vertical at `P + Q`
    have hl := divIs_line (S := S) hn2 hpE x1 y1 x2 y2 h1 h2 hxy
    set R := Point.some x1 y1 h1 + Point.some x2 y2 h2 with hR
    have hRe : R = Point.some _ _ (nonsingular_add h1 h2 hxy) := Point.add_some hxy
    set x3 := (WA a b).addX x1 x2 ((WA a b).slope x1 x2 y1 y2)
    set y3 := (WA a b).addY x1 x2 y1 ((WA a b).slope x1 x2 y1 y2)
    have h3 : (WA a b).Nonsingular x3 y3 := nonsingular_add h1 h2 hxy
    have hvt := divIs_vert (S := S) hn2 hpE x3 y3 h3
    have hlne : S.lineF ((WA a b).slope x1 x2 y1 y2) (y1 - (WA a b).slope x1 x2 y1 y2 * x1) ≠ 0 :=
      ne_zero_of_divIs hl x1 y1 (point_on hn2 hpE x1 y1 h1) (by
        have e1 := δ_self x1 y1 h1
        have e2 := δ_nonneg (Point.some x2 y2 h2) (x1, y1)
        have e3 := δ_nonneg (-R) (x1, y1)
        simp only [Pi.add_apply]; omega)
    have hvne : S.polyX (X - Polynomial.C x3) ≠ 0 := S.polyX_ne_zero (X_sub_C_ne_zero x3)
    refine ⟨_ * (S.polyX (X - Polynomial.C x3))⁻¹, mul_ne_zero hlne (inv_ne_zero hvne),
      divIs_congr (divIs_mul hlne (inv_ne_zero hvne) hl (divIs_inv hvt)) ?_⟩
    rw [hRe]
    funext z; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring

/-- The divisor `∑ nᵢ δ Pᵢ` and the sum `∑ nᵢ Pᵢ` of a list. -/
noncomputable def divL : List (ℤ × (WA a b).Point) → C × C → ℤ
  | [] => 0
  | e :: l => e.1 • δ a b e.2 + divL l

/-- The group sum `∑ nᵢ Pᵢ`. -/
noncomputable def sumL : List (ℤ × (WA a b).Point) → (WA a b).Point
  | [] => 0
  | e :: l => e.1 • e.2 + sumL l

omit hn2 hpE in
lemma divIs_mul' {f g : C⟮S.x⟯⟮S.y⟯} {D E F : C × C → ℤ} (hf : f ≠ 0) (hg : g ≠ 0)
    (h1 : S.DivIs f D) (h2 : S.DivIs g E) (hF : D + E = F) : S.DivIs (f * g) F :=
  divIs_congr (divIs_mul hf hg h1 h2) hF

/-- **Adding `n` copies of `P`.** -/
lemma step_n (E : C × C → ℤ) (s P : (WA a b).Point) (h : C⟮S.x⟯⟮S.y⟯) (hh : h ≠ 0)
    (hd : S.DivIs h (E - δ a b s)) (n : ℤ) :
    ∃ h' : C⟮S.x⟯⟮S.y⟯, h' ≠ 0 ∧ S.DivIs h' (E + n • δ a b P - δ a b (s + n • P)) := by
  induction n using Int.induction_on with
  | zero => exact ⟨h, hh, divIs_congr hd (by simp)⟩
  | succ k ih =>
    obtain ⟨h', hh', hd'⟩ := ih
    obtain ⟨g, hg, hdg⟩ := exists_g (S := S) hn2 hpE (s + (k : ℤ) • P) P
    refine ⟨h' * g, mul_ne_zero hh' hg, divIs_mul' hh' hg hd' hdg ?_⟩
    have e : s + ((k : ℤ) + 1) • P = s + (k : ℤ) • P + P := by rw [add_smul, one_smul, add_assoc]
    push_cast
    rw [e]
    funext z; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  | pred k ih =>
    obtain ⟨h', hh', hd'⟩ := ih
    obtain ⟨g, hg, hdg⟩ := exists_g (S := S) hn2 hpE (s + (-(k : ℤ) - 1) • P) P
    refine ⟨h' * g⁻¹, mul_ne_zero hh' (inv_ne_zero hg), divIs_mul' hh' (inv_ne_zero hg) hd'
      (divIs_inv hdg) ?_⟩
    have e : s + (-(k : ℤ) - 1) • P + P = s + -(k : ℤ) • P := by
      rw [sub_smul, one_smul]; abel
    rw [e]
    funext z; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring

/-- **A function with divisor `∑ nᵢ δ Pᵢ − δ (∑ nᵢ Pᵢ)`.** -/
lemma exists_h (l : List (ℤ × (WA a b).Point)) :
    ∃ h : C⟮S.x⟯⟮S.y⟯, h ≠ 0 ∧ S.DivIs h (divL l - δ a b (sumL l)) := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, divIs_congr divIs_one (by funext z; simp [divL, sumL, δ])⟩
  | cons e l ih =>
    obtain ⟨h, hh, hd⟩ := ih
    obtain ⟨h', hh', hd'⟩ := step_n (S := S) hn2 hpE (divL l) (sumL l) e.2 h hh hd e.1
    refine ⟨h', hh', divIs_congr hd' ?_⟩
    simp only [divL, sumL]
    rw [add_comm (sumL l)]
    funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring

/-- **Abel's theorem (the direction needed)**: a function with affine divisor `∑ nᵢ (Pᵢ)` forces
`∑ nᵢ Pᵢ = 0` in the group of points. -/
theorem abel_sum (l : List (ℤ × (WA a b).Point)) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hdiv : S.DivIs w (divL l)) : sumL l = 0 := by
  obtain ⟨h, hh, hd⟩ := exists_h (S := S) hn2 hpE l
  have hq := divIs_mul' hw (inv_ne_zero hh) hdiv (divIs_inv hd) (F := δ a b (sumL l))
    (by funext z; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring)
  by_contra hs
  rcases hR : sumL l with _ | ⟨α₀, β₀, h₀⟩
  · exact hs hR
  rw [hR] at hq
  have hd3 : S.p.natDegree = 3 := by rw [hpE]; compute_degree!
  refine S.no_simple_pole (K := C) hn2 hd3 _ (mul_ne_zero hw (inv_ne_zero hh)) α₀ β₀
    (point_on hn2 hpE α₀ β₀ h₀) (fun α β hv ↦ ?_)
  rw [hq α β hv]
  simp only [δ, Prod.mk.injEq]

end SuperData

end Differential
