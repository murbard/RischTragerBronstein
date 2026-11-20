import RischTragerBronstein.Mixed.EllParAux

/-!
# The parallelogram estimate for the naive height on an elliptic curve over `K(X)`

**`hN_par_upper`**: `hN (P + Q) + hN (P − Q) ≤ 2 hN P + 2 hN Q + 2 D` on `y² = x³ + A x + B`.
`x(P ± Q)` are the roots of `W₀ X² − W₁ X + W₂` (`W₀ = (x₁ − x₂)²`, …, `sum_addX`, `prod_addX`);
the Gauss lemma (`gauss_deg`) and the unit-ideal argument (`dvd_of_prim`) bound
`ht x(P+Q) + ht x(P−Q)` by the degrees of the `Wᵢ`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

lemma sum_addX {F : Type*} [Field F] (x1 x2 y1 y2 a b : F) (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) (hx : x1 - x2 ≠ 0) :
    (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) + (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) =
      2 * ((x1 + x2) * (x1 * x2 + a) + 2 * b) / (x1 - x2) ^ 2 := by
  field_simp
  linear_combination 2 * h1 + 2 * h2

lemma prod_addX {F : Type*} [Field F] (x1 x2 y1 y2 a b : F) (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) (hx : x1 - x2 ≠ 0) :
    (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) * (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) =
      ((x1 * x2 - a) ^ 2 - 4 * b * (x1 + x2)) / (x1 - x2) ^ 2 := by
  field_simp
  linear_combination (y1 ^ 2 - y2 ^ 2 + (x1 ^ 3 + a * x1 + b) - (x2 ^ 3 + a * x2 + b) -
    2 * (x1 + x2) * (x1 - x2) ^ 2) * h1 - (y1 ^ 2 - y2 ^ 2 + (x1 ^ 3 + a * x1 + b) -
    (x2 ^ 3 + a * x2 + b) + 2 * (x1 + x2) * (x1 - x2) ^ 2) * h2

omit [CharZero K] in
/-- **Height of the roots of a quadratic**: if `x₃ + x₄ = W₁/W₀` and `x₃ x₄ = W₂/W₀` (`W₀ ≠ 0`)
then `ht x₃ + ht x₄ ≤ max (deg W₀) (max (deg W₁) (deg W₂))`. -/
theorem ht_roots_le (x3 x4 : RatFunc K) (W0 W1 W2 : K[X]) (hW0 : W0 ≠ 0)
    (hs : x3 + x4 = ι W1 / ι W0) (hp : x3 * x4 = ι W2 / ι W0) :
    ht x3 + ht x4 ≤ max W0.natDegree (max W1.natDegree W2.natDegree) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  set p3 := RatFunc.num x3; set q3 := RatFunc.denom x3
  set p4 := RatFunc.num x4; set q4 := RatFunc.denom x4
  have hq3 : q3 ≠ 0 := RatFunc.denom_ne_zero x3
  have hq4 : q4 ≠ 0 := RatFunc.denom_ne_zero x4
  have hx3 : x3 = ι p3 / ι q3 := (RatFunc.num_div_denom x3).symm
  have hx4 : x4 = ι p4 / ι q4 := (RatFunc.num_div_denom x4).symm
  have hι3 : ι q3 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq3
  have hι4 : ι q4 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq4
  have hι0 : ι W0 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hW0
  -- the coefficient relations `W₀ Pᵢ = q₃q₄ Wᵢ`
  have r1 : W0 * (q3 * p4 + p3 * q4) = q3 * q4 * W1 := by
    apply hinj
    simp only [map_mul, map_add]
    rw [hx3, hx4] at hs
    field_simp at hs
    linear_combination hs
  have r0 : W0 * (p3 * p4) = q3 * q4 * W2 := by
    apply hinj
    simp only [map_mul]
    rw [hx3, hx4] at hp
    field_simp at hp
    linear_combination hp
  have hdvd : q3 * q4 ∣ W0 := dvd_of_prim p3 q3 p4 q4 W0 (q3 * q4)
    (RatFunc.isCoprime_num_denom x3).symm (RatFunc.isCoprime_num_denom x4).symm
    ⟨W0, by ring⟩ ⟨W1, r1⟩ ⟨W2, r0⟩
  obtain ⟨c, hc⟩ := hdvd
  have hqq : q3 * q4 ≠ 0 := mul_ne_zero hq3 hq4
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hW0 hc
  have e1 : W1 = c * (q3 * p4 + p3 * q4) := by
    apply mul_left_cancel₀ hqq; rw [← r1, hc]; ring
  have e2 : W2 = c * (p3 * p4) := by
    apply mul_left_cancel₀ hqq; rw [← r0, hc]; ring
  have g := gauss_deg p3 q3 p4 q4 hq3 hq4
  have d0 : (q3 * q4).natDegree ≤ W0.natDegree := by
    rw [hc, natDegree_mul hqq hc0]; omega
  have d1 : (q3 * p4 + p3 * q4).natDegree ≤ W1.natDegree := by
    by_cases hz : q3 * p4 + p3 * q4 = 0
    · rw [hz]; simp
    · rw [e1, natDegree_mul hc0 hz]; omega
  have d2 : (p3 * p4).natDegree ≤ W2.natDegree := by
    by_cases hz : p3 * p4 = 0
    · rw [hz]; simp
    · rw [e2, natDegree_mul hc0 hz]; omega
  unfold ht
  calc max p3.natDegree q3.natDegree + max p4.natDegree q4.natDegree
      ≤ max (q3 * q4).natDegree (max (q3 * p4 + p3 * q4).natDegree (p3 * p4).natDegree) := g
    _ ≤ _ := max_le_max d0 (max_le_max d1 d2)

omit [CharZero K] in
lemma eq_short (A B : K[X]) {x y : RatFunc K} (h : (shortW A B).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + ι A * x + ι B := by
  have := (equation_iff x y).mp h
  simpa [shortW] using this

omit [CharZero K] in
lemma negY_short (A B : K[X]) (x y : RatFunc K) : (shortW A B).toAffine.negY x y = -y := by
  simp [negY, shortW]

omit [CharZero K] in
lemma addX_short (A B : K[X]) (x1 x2 ℓ : RatFunc K) :
    (shortW A B).toAffine.addX x1 x2 ℓ = ℓ ^ 2 - x1 - x2 := by
  simp [addX, shortW]

omit [CharZero K] in
lemma hN_neg (A B : K[X]) (Q : (shortW A B).toAffine.Point) : hN A B (-Q) = hN A B Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · rfl

omit [CharZero K] in
/-- The generic case `x₁ ≠ x₂`. -/
theorem par_generic (A B : K[X]) (x1 y1 x2 y2 : RatFunc K)
    (h1 : (shortW A B).toAffine.Equation x1 y1) (h2 : (shortW A B).toAffine.Equation x2 y2)
    (hx : x1 ≠ x2) :
    ht (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) + ht (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) ≤
      2 * ht x1 + 2 * ht x2 + 2 * max A.natDegree B.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  set u1 := RatFunc.num x1; set v1 := RatFunc.denom x1
  set u2 := RatFunc.num x2; set v2 := RatFunc.denom x2
  have hv1 : v1 ≠ 0 := RatFunc.denom_ne_zero x1
  have hv2 : v2 ≠ 0 := RatFunc.denom_ne_zero x2
  have hx1 : x1 = ι u1 / ι v1 := (RatFunc.num_div_denom x1).symm
  have hx2 : x2 = ι u2 / ι v2 := (RatFunc.num_div_denom x2).symm
  have hι1 : ι v1 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv1
  have hι2 : ι v2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv2
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  set W0 := WE2.ev A B u1 v1 u2 v2 w0E
  set W1 := WE2.ev A B u1 v1 u2 v2 w1E
  set W2 := WE2.ev A B u1 v1 u2 v2 w2E
  have eW0 : ι W0 = (ι v1 * ι v2) ^ 2 * (x1 - x2) ^ 2 := by
    simp only [W0, WE2.ev, w0E, map_pow, map_sub, map_mul]
    rw [hx1, hx2]; field_simp
  have eW1 : ι W1 = (ι v1 * ι v2) ^ 2 * (2 * ((x1 + x2) * (x1 * x2 + ι A) + 2 * ι B)) := by
    simp only [W1, WE2.ev, w1E, map_pow, map_add, map_mul, map_intCast]
    rw [hx1, hx2]; field_simp; push_cast; ring
  have eW2 : ι W2 = (ι v1 * ι v2) ^ 2 * ((x1 * x2 - ι A) ^ 2 - 4 * ι B * (x1 + x2)) := by
    simp only [W2, WE2.ev, w2E, map_pow, map_sub, map_add, map_mul, map_intCast]
    rw [hx1, hx2]; field_simp; push_cast; ring
  have hvv : (ι v1 * ι v2) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hι1 hι2)
  have hW0 : W0 ≠ 0 := by
    intro h0; have := congrArg ι h0; rw [eW0, map_zero] at this
    exact mul_ne_zero hvv (pow_ne_zero 2 hd) this
  have hs := sum_addX x1 x2 y1 y2 (ι A) (ι B) (eq_short A B h1) (eq_short A B h2) hd
  have hp := prod_addX x1 x2 y1 y2 (ι A) (ι B) (eq_short A B h1) (eq_short A B h2) hd
  have hs' : (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) + (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) =
      ι W1 / ι W0 := by
    rw [hs, eW0, eW1, mul_div_mul_left _ _ hvv]
  have hp' : (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) * (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) =
      ι W2 / ι W0 := by
    rw [hp, eW0, eW2, mul_div_mul_left _ _ hvv]
  have hr := ht_roots_le _ _ W0 W1 W2 hW0 hs' hp'
  -- degree bounds
  set D := max A.natDegree B.natDegree
  have S := WE2.est_sound A B u1 v1 u2 v2 D (max u1.natDegree v1.natDegree)
    (max u2.natDegree v2.natDegree) (le_max_left _ _) (le_max_right _ _) (le_max_left _ _)
    (le_max_right _ _) (le_max_left _ _) (le_max_right _ _)
  have b0 : W0.natDegree ≤ _ := S w0E
  have b1 : W1.natDegree ≤ _ := S w1E
  have b2 : W2.natDegree ≤ _ := S w2E
  rw [est_w.1] at b0; rw [est_w.2.1] at b1; rw [est_w.2.2] at b2
  simp only [zero_mul, zero_add, one_mul] at b0 b1 b2
  have hh1 : ht x1 = max u1.natDegree v1.natDegree := by
    rw [hx1]; exact ht_div_coprime u1 v1 hv1 (RatFunc.isCoprime_num_denom x1)
  have hh2 : ht x2 = max u2.natDegree v2.natDegree := by
    rw [hx2]; exact ht_div_coprime u2 v2 hv2 (RatFunc.isCoprime_num_denom x2)
  rw [hh1, hh2]
  have : max W0.natDegree (max W1.natDegree W2.natDegree) ≤
      2 * D + 2 * max u1.natDegree v1.natDegree + 2 * max u2.natDegree v2.natDegree :=
    max_le (by omega) (max_le (by omega) (by omega))
  omega

/-- **The upper parallelogram estimate.** -/
theorem hN_par_upper (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (P Q : (shortW A B).toAffine.Point) :
    hN A B (P + Q) + hN A B (P - Q) ≤ 2 * hN A B P + 2 * hN A B Q + 2 * max A.natDegree B.natDegree := by
  rcases P with _ | ⟨x1, y1, h1⟩
  · have e : (Point.zero : (shortW A B).toAffine.Point) = 0 := rfl
    rw [e, zero_add, zero_sub, hN_neg]
    simp [hN]; omega
  rcases Q with _ | ⟨x2, y2, h2⟩
  · have e : (Point.zero : (shortW A B).toAffine.Point) = 0 := rfl
    rw [e, add_zero, sub_zero]
    simp [hN]; omega
  rw [sub_eq_add_neg, Point.neg_some]
  by_cases hx : x1 = x2
  · subst hx
    have hdbl := (hN_double A B hΔ (Point.some x1 y1 h1)).2
    have hQ : hN A B (Point.some x1 y2 h2) = hN A B (Point.some x1 y1 h1) := rfl
    by_cases hy : y1 = (shortW A B).toAffine.negY x1 y2
    · -- `Q = −P`: `P + Q = 0`, `P − Q = 2P`
      rw [Point.add_of_Y_eq rfl hy]
      have e : (Point.some x1 ((shortW A B).toAffine.negY x1 y2)
          ((nonsingular_neg ..).mpr h2) : (shortW A B).toAffine.Point) = Point.some x1 y1 h1 := by
        simp only [Point.some.injEq]; exact ⟨trivial, hy.symm⟩
      rw [e, hQ]
      have z : hN A B (0 : (shortW A B).toAffine.Point) = 0 := rfl
      rw [z]; omega
    · -- `Q = P`: `P + Q = 2P`, `P − Q = 0`
      have hy2 : y1 = y2 := Y_eq_of_Y_ne h1.1 h2.1 rfl hy
      subst hy2
      have e2 : Point.some x1 y1 h2 = Point.some x1 y1 h1 := rfl
      rw [e2, Point.add_of_Y_eq (h₂ := (nonsingular_neg ..).mpr h1) rfl (negY_negY _ _).symm, hQ]
      have z : hN A B (0 : (shortW A B).toAffine.Point) = 0 := rfl
      rw [z]; omega
  · rw [Point.add_of_X_ne hx, Point.add_of_X_ne hx]
    simp only [hN, addX_short, slope_of_X_ne hx, negY_short, sub_neg_eq_add]
    exact par_generic A B x1 y1 x2 y2 h1.1 h2.1 hx

end FFHeight
