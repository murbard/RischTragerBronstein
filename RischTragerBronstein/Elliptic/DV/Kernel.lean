import RischTragerBronstein.Elliptic.DV.Padic

/-!
# The kernel of reduction over `ℚ_p`

For `y² = f(x) = x³ + ax² + bx + c` (`a, b, c ∈ ℤ`), `p` odd, with good reduction in the form
`GoodRed` (`‖f(t)‖ < 1 → ‖f′(t)‖ = 1` for integral `t`): two distinct integral points with the same
reduction (`‖x₁ − x₂‖ < 1`, `‖y₁ − y₂‖ < 1`) differ by a point with `‖x‖ > 1`, i.e. in the kernel
of reduction (`kernel_big`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllDV

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime] (a b c : ℤ)

/-- Good reduction: the reduced cubic has no repeated root. -/
def GoodRed (p : ℕ) [Fact p.Prime] (a b c : ℤ) : Prop :=
  ∀ t : ℚ_[p], ‖t‖ ≤ 1 → ‖t ^ 3 + a * t ^ 2 + b * t + c‖ < 1 → ‖3 * t ^ 2 + 2 * a * t + b‖ = 1

lemma nint (z : ℤ) : ‖(z : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one z

lemma nadd {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (Padic.nonarchimedean x y).trans (max_le hx hy)

lemma nmul {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

lemma nneg {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) : ‖-x‖ ≤ 1 := by rwa [norm_neg]

lemma nsub {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact nadd hx (nneg hy)

lemma norm_two_odd (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have := (Padic.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
    ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
  exact_mod_cast this

/-- A big `λ` gives a big `x = λ² − a − x₁ − x₂`. -/
lemma big_addX {L x1 x2 : ℚ_[p]} (hL : 1 < ‖L‖) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1) :
    1 < ‖L ^ 2 - a - x1 - x2‖ := by
  have hL2 : ‖L ^ 2‖ = ‖L‖ ^ 2 := norm_pow _ _
  have hrest : ‖-((a : ℚ_[p]) + x1 + x2)‖ ≤ 1 := nneg (nadd (nadd (nint a) hx1) hx2)
  have hbig : 1 < ‖L ^ 2‖ := by rw [hL2]; nlinarith
  have e : L ^ 2 - a - x1 - x2 = L ^ 2 + -((a : ℚ_[p]) + x1 + x2) := by ring
  rw [e, Padic.add_eq_max_of_ne (by linarith), max_eq_left (by linarith)]
  exact hbig

set_option maxHeartbeats 800000 in
/-- **The kernel lemma.** -/
theorem kernel_big (hp2 : p ≠ 2) (hgood : GoodRed p a b c) {x1 y1 x2 y2 : ℚ_[p]}
    (h1 : (W ℚ_[p] a b c).toAffine.Nonsingular x1 y1)
    (h2 : (W ℚ_[p] a b c).toAffine.Nonsingular x2 y2)
    (hx1 : ‖x1‖ ≤ 1) (hy1 : ‖y1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1) (hy2 : ‖y2‖ ≤ 1)
    (hdx : ‖x1 - x2‖ < 1) (hdy : ‖y1 - y2‖ < 1)
    (hne : Point.some x1 y1 h1 ≠ Point.some x2 y2 h2) :
    ∃ x3 y3 h3, Point.some x1 y1 h1 - Point.some x2 y2 h2 = Point.some x3 y3 h3 ∧ 1 < ‖x3‖ := by
  classical
  have e1 := (equation_W a b c).mp h1.1
  have e2 := (equation_W a b c).mp h2.1
  unfold OnCurve at e1 e2
  have h2n := (Point.neg_some h2)
  rw [sub_eq_add_neg, h2n]
  have hn2 : (W ℚ_[p] a b c).toAffine.negY x2 y2 = -y2 := negY_W a b c x2 y2
  have hnn : (W ℚ_[p] a b c).toAffine.negY x2 ((W ℚ_[p] a b c).toAffine.negY x2 y2) = y2 := by
    rw [hn2, negY_W]; ring
  have hxy : ¬(x1 = x2 ∧ y1 = (W ℚ_[p] a b c).toAffine.negY x2
      ((W ℚ_[p] a b c).toAffine.negY x2 y2)) := by
    rintro ⟨rfl, hyy⟩
    rw [hnn] at hyy
    subst hyy
    exact hne rfl
  rw [Point.add_some hxy]
  refine ⟨_, _, _, rfl, ?_⟩
  have h2' : ‖(2 : ℚ_[p])‖ = 1 := norm_two_odd hp2
  have hX : ∀ L : ℚ_[p], (W ℚ_[p] a b c).toAffine.addX x1 x2 L = L ^ 2 - a - x1 - x2 := by
    intro L; simp [addX, W, W0]
  rw [hX]
  refine big_addX a ?_ hx1 hx2
  by_cases hx : x1 = x2
  · -- doubling: `y₂ = −y₁`
    subst hx
    have hy : y1 ≠ (W ℚ_[p] a b c).toAffine.negY x1 ((W ℚ_[p] a b c).toAffine.negY x1 y2) :=
      fun h ↦ hxy ⟨rfl, h⟩
    rw [hnn] at hy
    have hyy : y2 = -y1 := by
      have : (y1 - y2) * (y1 + y2) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hy
      · linear_combination h
    subst hyy
    have hy10 : y1 ≠ 0 := by rintro rfl; exact hy (by ring)
    rw [slope_of_Y_ne rfl (by
      simp only [negY, W, W0, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_zero]
      intro h; apply hy10; linear_combination h / 2)]
    have hsl : (3 * x1 ^ 2 + 2 * (W ℚ_[p] a b c).a₂ * x1 + (W ℚ_[p] a b c).a₄ -
        (W ℚ_[p] a b c).a₁ * y1) / (y1 - (W ℚ_[p] a b c).toAffine.negY x1 y1) =
        (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1) := by
      rw [negY_W]; simp [W, W0]; ring
    rw [hsl]
    -- `‖y₁‖ < 1` and `‖f′(x₁)‖ = 1`
    have hy1s : ‖y1‖ < 1 := by
      have : ‖y1 - -y1‖ = ‖y1‖ := by
        rw [show y1 - -y1 = 2 * y1 by ring, norm_mul, h2', one_mul]
      rwa [this] at hdy
    have hf : ‖x1 ^ 3 + a * x1 ^ 2 + b * x1 + c‖ < 1 := by
      rw [← e1, norm_pow]; nlinarith [norm_nonneg y1]
    have hf' := hgood x1 hx1 hf
    rw [norm_div, hf', norm_mul, h2', one_mul]
    rw [one_lt_div (norm_pos_iff.mpr hy10)]
    exact hy1s
  · rw [slope_of_X_ne hx]
    have hxs : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
    have hxn : 0 < ‖x1 - x2‖ := norm_pos_iff.mpr hxs
    rw [hn2, sub_neg_eq_add]
    by_cases hyu : ‖y1‖ = 1
    · -- `y₁ + y₂ = 2y₁ − (y₁ − y₂)` is a unit
      have hs : ‖y1 + y2‖ = 1 := by
        have e : y1 + y2 = 2 * y1 + -(y1 - y2) := by ring
        rw [e, Padic.add_eq_max_of_ne, norm_mul, h2', one_mul, hyu, norm_neg,
          max_eq_left hdy.le]
        rw [norm_mul, h2', one_mul, hyu, norm_neg]; exact (ne_of_lt hdy).symm
      rw [norm_div, hs, one_lt_div hxn]
      exact hdx
    · have hy1s : ‖y1‖ < 1 := lt_of_le_of_ne hy1 hyu
      have hf : ‖x1 ^ 3 + a * x1 ^ 2 + b * x1 + c‖ < 1 := by
        rw [← e1, norm_pow]; nlinarith [norm_nonneg y1]
      have hf' := hgood x1 hx1 hf
      -- `F = (f(x₁) − f(x₂))/(x₁ − x₂)` is a unit
      set F : ℚ_[p] := x1 ^ 2 + x1 * x2 + x2 ^ 2 + a * (x1 + x2) + b with hF
      have hFd : F - (3 * x1 ^ 2 + 2 * a * x1 + b) = (x2 - x1) * (2 * x1 + x2 + a) := by
        rw [hF]; ring
      have hFs : ‖F - (3 * x1 ^ 2 + 2 * a * x1 + b)‖ < 1 := by
        rw [hFd, norm_mul, ← norm_neg, neg_sub]
        have : ‖2 * x1 + x2 + a‖ ≤ 1 :=
          nadd (nadd (nmul (by rw [h2']) hx1) hx2) (nint a)
        nlinarith [norm_nonneg (x1 - x2), norm_nonneg (2 * x1 + x2 + (a : ℚ_[p]))]
      have hFn : ‖F‖ = 1 := by
        have e : F = (3 * x1 ^ 2 + 2 * a * x1 + b) + (F - (3 * x1 ^ 2 + 2 * a * x1 + b)) := by
          ring
        rw [e, Padic.add_eq_max_of_ne (by rw [hf']; exact (ne_of_lt hFs).symm), hf',
          max_eq_left hFs.le]
      have hyy : (y1 + y2) * (y1 - y2) = F * (x1 - x2) := by
        rw [hF]; linear_combination e1 - e2
      have hyd : y1 - y2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hyy
        rcases mul_eq_zero.mp hyy.symm with h | h
        · rw [h, norm_zero] at hFn; exact zero_ne_one hFn
        · exact hxs h
      have hL : (y1 + y2) / (x1 - x2) = F / (y1 - y2) := by
        rw [div_eq_div_iff hxs hyd]; linear_combination hyy
      rw [hL, norm_div, hFn, one_lt_div (norm_pos_iff.mpr hyd)]
      exact hdy

end EllDV
