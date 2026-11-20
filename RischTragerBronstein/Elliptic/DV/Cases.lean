import RischTragerBronstein.Elliptic.DV.Alg

/-!
# Nagell–Lutz: chord and tangent cases

Points `(x, y)` on `y² = x³ + a x² + b x + c` with `v_p(y) ≤ -3r` (`r ≥ 1`) have
`v_p(x) = -2k`, `v_p(y) = -3k`, `k ≥ r` (`point_val`), so `t = x/y ∈ p^r`, `s = 1/y ∈ p^{3r}`.
`chord` and `tangent`: the sum `(x₃, y₃)` (Mathlib's formulas) satisfies `1/y₃ ∈ p^{3r}` and
`x₃/y₃ ≡ x₁/y₁ + x₂/y₂ (mod p^{3r})`.
-/

namespace EllDV


variable {K : Type*} [Field K] [CharZero K] {p : ℕ} (V : DVal K p)

/-- The curve equation. -/
def OnCurve (a b c : ℤ) (x y : K) : Prop := y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c

/-- The filtration `E(p^r)`: `v_p(y) ≤ -3r`. -/
def InFilt (r : ℕ) (y : K) : Prop := y ≠ 0 ∧ V.v y ≤ -3 * r

lemma point_val (a b c : ℤ) {x y : K} (h : OnCurve a b c x y) (hy : y ≠ 0)
    (hneg : V.v y < 0) :
    x ≠ 0 ∧ ∃ k : ℕ, 1 ≤ k ∧ V.v x = -2 * k ∧ V.v y = -3 * k := by
  -- `x` is not integral
  have hx : x ≠ 0 ∧ V.v x < 0 := by
    by_contra hx
    have hxi : PDvd V 0 x := by
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · right; push_neg at hx; exact hx hx0
    have hr : PDvd V 0 (x ^ 3 + a * x ^ 2 + b * x + c) := by
      have h3 := hxi.pow 3
      have h2 := (pdvd_intCast V a).mul (hxi.pow 2)
      have h1 := (pdvd_intCast V b).mul hxi
      have h0 := pdvd_intCast V c
      simp only [mul_zero, add_zero, Nat.cast_ofNat] at h3 h2 h1
      exact ((h3.add h2).add h1).add h0
    rw [← h] at hr
    have := pdvd_of_ne hr (pow_ne_zero _ hy)
    rw [V.pow y hy] at this
    push_cast at this
    omega
  obtain ⟨hx0, hxn⟩ := hx
  refine ⟨hx0, ?_⟩
  set v := V.v x with hv
  -- the rest is of valuation `≥ 2v > 3v`
  have hrest : PDvd V (2 * v) (a * x ^ 2 + b * x + c) := by
    have h2 : PDvd V (2 * v) ((a : K) * x ^ 2) := by
      have := (pdvd_intCast V a).mul ((show PDvd V v x from Or.inr le_rfl).pow 2)
      simpa using this
    have h1 : PDvd V (2 * v) ((b : K) * x) := by
      have := (pdvd_intCast V b).mul (show PDvd V v x from Or.inr le_rfl)
      exact (by simpa using this : PDvd V v ((b : K) * x)).mono (by omega)
    have h0 : PDvd V (2 * v) (c : K) := (pdvd_intCast V c).mono (by omega)
    exact (h2.add h1).add h0
  have hval : V.v (x ^ 3 + (a * x ^ 2 + b * x + c)) = 3 * v := by
    have hx3 : V.v (x ^ 3) = 3 * v := by rw [V.pow x hx0]; push_cast; ring
    have hsum0 : x ^ 3 + (a * x ^ 2 + b * x + c) ≠ 0 := by
      rw [show x ^ 3 + (a * x ^ 2 + b * x + c) = y ^ 2 by rw [h]; ring]
      exact pow_ne_zero _ hy
    by_cases h0 : (a : K) * x ^ 2 + b * x + c = 0
    · rw [h0, add_zero, hx3]
    · have hrv := pdvd_of_ne hrest h0
      rw [V.add_eq_of_lt hsum0 (pow_ne_zero _ hx0) h0 (by rw [hx3]; omega), hx3]
  have hy2 : V.v (y ^ 2) = 2 * V.v y := by
    rw [V.pow y hy]; push_cast; ring
  rw [show y ^ 2 = x ^ 3 + (a * x ^ 2 + b * x + c) by rw [h]; ring] at hy2
  rw [hval] at hy2
  -- `2 v_p(y) = 3 v`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, v = -2 * k := ⟨(-v / 2).toNat, by omega⟩
  refine ⟨k, by omega, hk, by omega⟩

/-- In the filtration: `t ∈ p^r`, `s ∈ p^{3r}`. -/
lemma filt_ts (a b c : ℤ) (r : ℕ) (hr : 1 ≤ r) {x y : K} (h : OnCurve a b c x y)
    (hF : InFilt V r y) : PDvd V r (x / y) ∧ PDvd V (3 * r) (1 / y) := by
  obtain ⟨hy, hyv⟩ := hF
  obtain ⟨hx0, k, hk, hxk, hyk⟩ := point_val V a b c h hy (by omega)
  refine ⟨Or.inr ?_, Or.inr ?_⟩
  · rw [V.div hx0 hy, hxk, hyk]; omega
  · rw [one_div, V.inv hy, hyk]; omega

/-- The curve in `(t, s)` coordinates: `s = t³ + a t² s + b t s² + c s³`. -/
lemma curve_ts (a b c : ℤ) {x y : K} (h : OnCurve a b c x y) (hy : y ≠ 0) :
    1 / y = (x / y) ^ 3 + a * (x / y) ^ 2 * (1 / y) + b * (x / y) * (1 / y) ^ 2 +
      c * (1 / y) ^ 3 := by
  unfold OnCurve at h
  field_simp
  linear_combination h

lemma filt_of_pdvd {r : ℕ} {y : K} (hy : y ≠ 0) (h : PDvd V (3 * r) (1 / y)) : InFilt V r y := by
  refine ⟨hy, ?_⟩
  have := pdvd_of_ne h (by simpa using hy)
  rw [one_div, V.inv hy] at this
  omega

lemma unit_of_small {u : K} (hu : PDvd V 1 u) : V.v (1 + u) = 0 ∧ 1 + u ≠ 0 :=
  val_one_add hu

/-- **The chord case.** -/
theorem chord (a b c : ℤ) (r : ℕ) (hr : 1 ≤ r) {x1 y1 x2 y2 : K} (h1 : OnCurve a b c x1 y1)
    (h2 : OnCurve a b c x2 y2) (F1 : InFilt V r y1) (F2 : InFilt V r y2) (hx : x1 ≠ x2) :
    let ℓ := (y1 - y2) / (x1 - x2)
    let x3 := ℓ ^ 2 - a - x1 - x2
    let y3 := -(ℓ * (x3 - x1) + y1)
    y3 ≠ 0 ∧ InFilt V r y3 ∧ PDvd V (3 * r) (x3 / y3 - x1 / y1 - x2 / y2) := by
  intro ℓ x3 y3
  have hy1 := F1.1
  have hy2 := F2.1
  obtain ⟨ht1, hs1⟩ := filt_ts V a b c r hr h1 F1
  obtain ⟨ht2, hs2⟩ := filt_ts V a b c r hr h2 F2
  have C1 := curve_ts a b c h1 hy1
  have C2 := curve_ts a b c h2 hy2
  set t1 := x1 / y1 with ht1d
  set t2 := x2 / y2 with ht2d
  set s1 := 1 / y1 with hs1d
  set s2 := 1 / y2 with hs2d
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  -- the unit denominator and the slope `α`
  set u := -((a : K) * t2 ^ 2 + b * t2 * (s1 + s2) + c * (s1 ^ 2 + s1 * s2 + s2 ^ 2)) with hu
  have hu1 : PDvd V 1 u := by
    have e1 : PDvd V 1 ((a : K) * t2 ^ 2) :=
      ((pdvd_intCast V a).mul (ht2.pow 2)).mono (by push_cast; omega)
    have e2 : PDvd V 1 ((b : K) * t2 * (s1 + s2)) :=
      (((pdvd_intCast V b).mul ht2).mul (hs1.add hs2)).mono (by push_cast; omega)
    have q1 : PDvd V 1 (s1 ^ 2) := (hs1.pow 2).mono (by push_cast; omega)
    have q2 : PDvd V 1 (s1 * s2) := (hs1.mul hs2).mono (by omega)
    have q3 : PDvd V 1 (s2 ^ 2) := (hs2.pow 2).mono (by push_cast; omega)
    have e3 : PDvd V 1 ((c : K) * (s1 ^ 2 + s1 * s2 + s2 ^ 2)) :=
      ((pdvd_intCast V c).mul ((q1.add q2).add q3)).mono (by omega)
    exact ((e1.add e2).add e3).neg
  obtain ⟨hU, hU0⟩ := unit_of_small V hu1
  set num := t1 ^ 2 + t1 * t2 + t2 ^ 2 + a * (t1 + t2) * s1 + b * s1 ^ 2 with hnum
  have hnumv : PDvd V (2 * r) num := by
    have e1 := ht1.pow 2
    have e2 := ht1.mul ht2
    have e3 := ht2.pow 2
    have e4 := ((pdvd_intCast V a).mul (ht1.add ht2)).mul hs1
    have e5 := (pdvd_intCast V b).mul (hs1.pow 2)
    refine ((((e1.mono ?_).add (e2.mono ?_)).add (e3.mono ?_)).add (e4.mono ?_)).add (e5.mono ?_)
    all_goals push_cast; omega
  set α := num / (1 + u) with hα
  have hαv : PDvd V (2 * r) α := hnumv.div_unit hU hU0
  have key : (s1 - s2) * (1 + u) = (t1 - t2) * num := by
    rw [hu, hnum]
    linear_combination C1 - C2
  set β := s1 - α * t1 with hβ
  have hβv : PDvd V (3 * r) β := hs1.sub ((hαv.mul ht1).mono (by push_cast; omega))
  have hs2' : s2 = α * t2 + β := by
    have : s1 - s2 = α * (t1 - t2) := by
      rw [hα, div_mul_eq_mul_div, eq_div_iff hU0]; linear_combination key
    rw [hβ]; linear_combination -this
  have hl1 : α * x1 + β * y1 = 1 := by
    rw [hβ, ht1d, hs1d]; field_simp; ring
  have hl2 : α * x2 + β * y2 = 1 := by
    have : s2 * y2 = 1 := by rw [hs2d]; field_simp
    rw [hs2', ht2d] at this
    rw [← this]; field_simp
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_mul, add_zero] at hl1 hl2
    apply hx
    have hα0 : α ≠ 0 := by rintro h; rw [h, zero_mul] at hl1; exact zero_ne_one hl1
    exact mul_left_cancel₀ hα0 (hl1.trans hl2.symm)
  have hxne : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  have hℓ : ℓ = -α / β := by
    show (y1 - y2) / (x1 - x2) = -α / β
    rw [div_eq_div_iff hxne hβ0]
    linear_combination hl1 - hl2
  set m := 1 / β with hm
  have hy1l : y1 = ℓ * x1 + m := by rw [hℓ, hm]; field_simp; linear_combination hl1
  have hy2l : y2 = ℓ * x2 + m := by rw [hℓ, hm]; field_simp; linear_combination hl2
  have g1 : x1 ^ 3 + a * x1 ^ 2 + b * x1 + c = (ℓ * x1 + m) ^ 2 := by rw [← hy1l]; exact h1.symm
  have g2 : x2 ^ 3 + a * x2 ^ 2 + b * x2 + c = (ℓ * x2 + m) ^ 2 := by rw [← hy2l]; exact h2.symm
  have V1 : x1 + x2 + x3 = ℓ ^ 2 - a := by simp only [x3]; ring
  have V2 : x1 * x2 + x1 * x3 + x2 * x3 = b - 2 * ℓ * m := by
    have : (x1 - x2) * (x1 * x2 + x1 * x3 + x2 * x3 - (b - 2 * ℓ * m)) = 0 := by
      simp only [x3]; linear_combination g2 - g1
    have := (mul_eq_zero.mp this).resolve_left hxne
    linear_combination this
  have V3 : x1 * x2 * x3 = m ^ 2 - c := by
    have hx3 : x3 = ℓ ^ 2 - a - x1 - x2 := rfl
    linear_combination g1 + x1 * V2 - x1 ^ 2 * V1
  obtain ⟨hl3, hK, hs3, -⟩ := third V a b c r hr x1 x2 x3 y1 y2 ℓ m α β hβ0 hℓ hm hy1l hy2l
    hy1 hy2 V1 V2 V3 hαv hβv ht1 ht2
  have hy3 : y3 = -(ℓ * x3 + m) := by simp only [y3]; rw [hy1l]; ring
  rw [hy3]
  refine ⟨neg_ne_zero.mpr hl3, filt_of_pdvd V (neg_ne_zero.mpr hl3) hs3, hK⟩

/-- The tangent slope in `(t, s)` coordinates. -/
lemma tangent_slope (a b c t s : K) (hs : s ≠ 0)
    (C : s = t ^ 3 + a * t ^ 2 * s + b * t * s ^ 2 + c * s ^ 3)
    (hden : 1 - a * t ^ 2 - 2 * b * t * s - 3 * c * s ^ 2 ≠ 0) :
    (3 * t ^ 2 + 2 * a * t * s + b * s ^ 2) / (2 * s) *
      (s - (3 * t ^ 2 + 2 * a * t * s + b * s ^ 2) / (1 - a * t ^ 2 - 2 * b * t * s -
        3 * c * s ^ 2) * t) =
    -((3 * t ^ 2 + 2 * a * t * s + b * s ^ 2) / (1 - a * t ^ 2 - 2 * b * t * s -
        3 * c * s ^ 2)) := by
  generalize hD : 1 - a * t ^ 2 - 2 * b * t * s - 3 * c * s ^ 2 = D at hden ⊢
  generalize hN : 3 * t ^ 2 + 2 * a * t * s + b * s ^ 2 = N
  field_simp
  linear_combination (3 * N) * C - (N * s) * hD + (N * t) * hN

/-- **The tangent case.** -/
theorem tangent (a b c : ℤ) (r : ℕ) (hr : 1 ≤ r) {x1 y1 : K} (h1 : OnCurve a b c x1 y1)
    (F1 : InFilt V r y1) :
    let ℓ := (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1)
    let x3 := ℓ ^ 2 - a - x1 - x1
    let y3 := -(ℓ * (x3 - x1) + y1)
    y3 ≠ 0 ∧ InFilt V r y3 ∧ PDvd V (3 * r) (x3 / y3 - x1 / y1 - x1 / y1) := by
  intro ℓ x3 y3
  have hℓdef : ℓ = (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1) := rfl
  have hx3def : x3 = ℓ ^ 2 - a - x1 - x1 := rfl
  have hy3def : y3 = -(ℓ * (x3 - x1) + y1) := rfl
  clear_value ℓ x3 y3
  have hy1 := F1.1
  obtain ⟨ht1, hs1⟩ := filt_ts V a b c r hr h1 F1
  have C1 := curve_ts a b c h1 hy1
  set t := x1 / y1 with htd
  set s := 1 / y1 with hsd
  set u := -((a : K) * t ^ 2 + 2 * b * t * s + 3 * c * s ^ 2) with hu
  have hu1 : PDvd V 1 u := by
    have e1 : PDvd V 1 ((a : K) * t ^ 2) :=
      ((pdvd_intCast V a).mul (ht1.pow 2)).mono (by push_cast; omega)
    have e2 : PDvd V 1 (2 * (b : K) * t * s) := by
      have := (((pdvd_intCast V 2).mul (pdvd_intCast V b)).mul ht1).mul hs1
      push_cast at this
      exact this.mono (by omega)
    have e3 : PDvd V 1 (3 * (c : K) * s ^ 2) := by
      have := ((pdvd_intCast V 3).mul (pdvd_intCast V c)).mul (hs1.pow 2)
      push_cast at this
      exact this.mono (by omega)
    exact ((e1.add e2).add e3).neg
  obtain ⟨hU, hU0⟩ := unit_of_small V hu1
  set num := 3 * t ^ 2 + 2 * a * t * s + b * s ^ 2 with hnum
  have hnumv : PDvd V (2 * r) num := by
    have e1 : PDvd V (2 * r) (3 * t ^ 2) := by
      have := (pdvd_intCast V 3).mul (ht1.pow 2)
      push_cast at this; exact this.mono (by omega)
    have e2 : PDvd V (2 * r) (2 * (a : K) * t * s) := by
      have := (((pdvd_intCast V 2).mul (pdvd_intCast V a)).mul ht1).mul hs1
      push_cast at this; exact this.mono (by omega)
    have e3 : PDvd V (2 * r) ((b : K) * s ^ 2) := by
      have := (pdvd_intCast V b).mul (hs1.pow 2)
      push_cast at this; exact this.mono (by omega)
    exact (e1.add e2).add e3
  set α := num / (1 + u) with hα
  have hαv : PDvd V (2 * r) α := hnumv.div_unit hU hU0
  set β := s - α * t with hβ
  have hβv : PDvd V (3 * r) β := hs1.sub ((hαv.mul ht1).mono (by push_cast; omega))
  have hl1 : α * x1 + β * y1 = 1 := by rw [hβ, htd, hsd]; field_simp; ring
  -- `ℓ β = -α`, from the curve equation
  have hℓβ : ℓ * β = -α := by
    have hℓ' : ℓ = num / (2 * s) := by
      rw [hℓdef, hnum, htd, hsd]; field_simp
    have hs0 : s ≠ 0 := by rw [hsd]; simpa using hy1
    have hden : 1 - (a : K) * t ^ 2 - 2 * b * t * s - 3 * c * s ^ 2 = 1 + u := by rw [hu]; ring
    rw [hℓ', hβ, hα, hnum, ← hden]
    exact tangent_slope (a : K) (b : K) (c : K) t s hs0 C1 (by rw [hden]; exact hU0)
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_eq_neg] at hℓβ
    rw [hℓβ, zero_mul, zero_add] at hl1
    rw [hβ, hℓβ, zero_mul, sub_zero, hsd] at h0
    simp at h0; exact hy1 h0
  have hℓ : ℓ = -α / β := by rw [eq_div_iff hβ0]; exact hℓβ
  set m := 1 / β with hm
  have hy1l : y1 = ℓ * x1 + m := by rw [hℓ, hm]; field_simp; linear_combination hl1
  have htan : 2 * ℓ * y1 = 3 * x1 ^ 2 + 2 * a * x1 + b := by
    rw [hℓdef]; field_simp
  have V1 : x1 + x1 + x3 = ℓ ^ 2 - a := by rw [hx3def]; ring
  have V2 : x1 * x1 + x1 * x3 + x1 * x3 = b - 2 * ℓ * m := by
    have hmd : m = y1 - ℓ * x1 := by rw [hy1l]; ring
    rw [hx3def, hmd]
    linear_combination htan
  have V3 : x1 * x1 * x3 = m ^ 2 - c := by
    have hmd : m = y1 - ℓ * x1 := by rw [hy1l]; ring
    unfold OnCurve at h1
    rw [hx3def, hmd]
    linear_combination -h1 + x1 * htan
  obtain ⟨hl3, hK, hs3, -⟩ := third V a b c r hr x1 x1 x3 y1 y1 ℓ m α β hβ0 hℓ hm hy1l hy1l
    hy1 hy1 V1 V2 V3 hαv hβv ht1 ht1
  have hy3 : y3 = -(ℓ * x3 + m) := by rw [hy3def, hy1l]; ring
  rw [hy3]
  exact ⟨neg_ne_zero.mpr hl3, filt_of_pdvd V (neg_ne_zero.mpr hl3) hs3, hK⟩

end EllDV
