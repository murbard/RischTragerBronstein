import RischTragerBronstein.Elliptic.NLAlg

/-!
# Nagell–Lutz: chord and tangent cases

Points `(x, y)` on `y² = x³ + a x² + b x + c` with `v_p(y) ≤ -3r` (`r ≥ 1`) have
`v_p(x) = -2k`, `v_p(y) = -3k`, `k ≥ r` (`point_val`), so `t = x/y ∈ p^r`, `s = 1/y ∈ p^{3r}`.
`chord` and `tangent`: the sum `(x₃, y₃)` (Mathlib's formulas) satisfies `1/y₃ ∈ p^{3r}` and
`x₃/y₃ ≡ x₁/y₁ + x₂/y₂ (mod p^{3r})`.
-/

namespace EllNL

open PVal

variable {p : ℕ} [hp : Fact p.Prime]

/-- The curve equation. -/
def OnCurve (a b c : ℤ) (x y : ℚ) : Prop := y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c

/-- The filtration `E(p^r)`: `v_p(y) ≤ -3r`. -/
def InFilt (p : ℕ) (r : ℕ) (y : ℚ) : Prop := y ≠ 0 ∧ padicValRat p y ≤ -3 * r

lemma point_val (a b c : ℤ) {x y : ℚ} (h : OnCurve a b c x y) (hy : y ≠ 0)
    (hneg : padicValRat p y < 0) :
    x ≠ 0 ∧ ∃ k : ℕ, 1 ≤ k ∧ padicValRat p x = -2 * k ∧ padicValRat p y = -3 * k := by
  -- `x` is not integral
  have hx : x ≠ 0 ∧ padicValRat p x < 0 := by
    by_contra hx
    have hxi : PDvd p 0 x := by
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · right; push_neg at hx; exact hx hx0
    have hr : PDvd p 0 (x ^ 3 + a * x ^ 2 + b * x + c) := by
      have h3 := hxi.pow 3
      have h2 := (pdvd_intCast (p := p) a).mul (hxi.pow 2)
      have h1 := (pdvd_intCast (p := p) b).mul hxi
      have h0 := pdvd_intCast (p := p) c
      simp only [mul_zero, add_zero, Nat.cast_ofNat] at h3 h2 h1
      exact ((h3.add h2).add h1).add h0
    rw [← h] at hr
    have := pdvd_of_ne hr (pow_ne_zero _ hy)
    rw [padicValRat.pow y] at this
    push_cast at this
    omega
  obtain ⟨hx0, hxn⟩ := hx
  refine ⟨hx0, ?_⟩
  set v := padicValRat p x with hv
  -- the rest is of valuation `≥ 2v > 3v`
  have hrest : PDvd p (2 * v) (a * x ^ 2 + b * x + c) := by
    have h2 : PDvd p (2 * v) ((a : ℚ) * x ^ 2) := by
      have := (pdvd_intCast (p := p) a).mul ((show PDvd p v x from Or.inr le_rfl).pow 2)
      simpa using this
    have h1 : PDvd p (2 * v) ((b : ℚ) * x) := by
      have := (pdvd_intCast (p := p) b).mul (show PDvd p v x from Or.inr le_rfl)
      exact (by simpa using this : PDvd p v ((b : ℚ) * x)).mono (by omega)
    have h0 : PDvd p (2 * v) (c : ℚ) := (pdvd_intCast (p := p) c).mono (by omega)
    exact (h2.add h1).add h0
  have hval : padicValRat p (x ^ 3 + (a * x ^ 2 + b * x + c)) = 3 * v := by
    have hx3 : padicValRat p (x ^ 3) = 3 * v := by rw [padicValRat.pow x]; push_cast; ring
    have hsum0 : x ^ 3 + (a * x ^ 2 + b * x + c) ≠ 0 := by
      rw [show x ^ 3 + (a * x ^ 2 + b * x + c) = y ^ 2 by rw [h]; ring]
      exact pow_ne_zero _ hy
    by_cases h0 : (a : ℚ) * x ^ 2 + b * x + c = 0
    · rw [h0, add_zero, hx3]
    · have hrv := pdvd_of_ne hrest h0
      rw [padicValRat.add_eq_of_lt hsum0 (pow_ne_zero _ hx0) h0 (by rw [hx3]; omega), hx3]
  have hy2 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by
    rw [padicValRat.pow y]; push_cast; ring
  rw [show y ^ 2 = x ^ 3 + (a * x ^ 2 + b * x + c) by rw [h]; ring] at hy2
  rw [hval] at hy2
  -- `2 v_p(y) = 3 v`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, v = -2 * k := ⟨(-v / 2).toNat, by omega⟩
  refine ⟨k, by omega, hk, by omega⟩

/-- In the filtration: `t ∈ p^r`, `s ∈ p^{3r}`. -/
lemma filt_ts (a b c : ℤ) (r : ℕ) (hr : 1 ≤ r) {x y : ℚ} (h : OnCurve a b c x y)
    (hF : InFilt p r y) : PDvd p r (x / y) ∧ PDvd p (3 * r) (1 / y) := by
  obtain ⟨hy, hyv⟩ := hF
  obtain ⟨hx0, k, hk, hxk, hyk⟩ := point_val (p := p) a b c h hy (by omega)
  refine ⟨Or.inr ?_, Or.inr ?_⟩
  · rw [padicValRat.div hx0 hy, hxk, hyk]; omega
  · rw [one_div, padicValRat.inv, hyk]; omega

/-- The curve in `(t, s)` coordinates: `s = t³ + a t² s + b t s² + c s³`. -/
lemma curve_ts (a b c : ℤ) {x y : ℚ} (h : OnCurve a b c x y) (hy : y ≠ 0) :
    1 / y = (x / y) ^ 3 + a * (x / y) ^ 2 * (1 / y) + b * (x / y) * (1 / y) ^ 2 +
      c * (1 / y) ^ 3 := by
  unfold OnCurve at h
  field_simp
  linear_combination h

lemma filt_of_pdvd {r : ℕ} {y : ℚ} (hy : y ≠ 0) (h : PDvd p (3 * r) (1 / y)) : InFilt p r y := by
  refine ⟨hy, ?_⟩
  have := pdvd_of_ne h (by simpa using hy)
  rw [one_div, padicValRat.inv] at this
  omega

lemma unit_of_small {u : ℚ} (hu : PDvd p 1 u) : padicValRat p (1 + u) = 0 ∧ 1 + u ≠ 0 :=
  val_one_add hu

/-- **The chord case.** -/
theorem chord (a b c : ℤ) (r : ℕ) (hr : 1 ≤ r) {x1 y1 x2 y2 : ℚ} (h1 : OnCurve a b c x1 y1)
    (h2 : OnCurve a b c x2 y2) (F1 : InFilt p r y1) (F2 : InFilt p r y2) (hx : x1 ≠ x2) :
    let ℓ := (y1 - y2) / (x1 - x2)
    let x3 := ℓ ^ 2 - a - x1 - x2
    let y3 := -(ℓ * (x3 - x1) + y1)
    y3 ≠ 0 ∧ InFilt p r y3 ∧ PDvd p (3 * r) (x3 / y3 - x1 / y1 - x2 / y2) := by
  intro ℓ x3 y3
  have hy1 := F1.1
  have hy2 := F2.1
  obtain ⟨ht1, hs1⟩ := filt_ts (p := p) a b c r hr h1 F1
  obtain ⟨ht2, hs2⟩ := filt_ts (p := p) a b c r hr h2 F2
  have C1 := curve_ts a b c h1 hy1
  have C2 := curve_ts a b c h2 hy2
  set t1 := x1 / y1 with ht1d
  set t2 := x2 / y2 with ht2d
  set s1 := 1 / y1 with hs1d
  set s2 := 1 / y2 with hs2d
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  -- the unit denominator and the slope `α`
  set u := -((a : ℚ) * t2 ^ 2 + b * t2 * (s1 + s2) + c * (s1 ^ 2 + s1 * s2 + s2 ^ 2)) with hu
  have hu1 : PDvd p 1 u := by
    have e1 : PDvd p 1 ((a : ℚ) * t2 ^ 2) :=
      ((pdvd_intCast (p := p) a).mul (ht2.pow 2)).mono (by push_cast; omega)
    have e2 : PDvd p 1 ((b : ℚ) * t2 * (s1 + s2)) :=
      (((pdvd_intCast (p := p) b).mul ht2).mul (hs1.add hs2)).mono (by push_cast; omega)
    have q1 : PDvd p 1 (s1 ^ 2) := (hs1.pow 2).mono (by push_cast; omega)
    have q2 : PDvd p 1 (s1 * s2) := (hs1.mul hs2).mono (by omega)
    have q3 : PDvd p 1 (s2 ^ 2) := (hs2.pow 2).mono (by push_cast; omega)
    have e3 : PDvd p 1 ((c : ℚ) * (s1 ^ 2 + s1 * s2 + s2 ^ 2)) :=
      ((pdvd_intCast (p := p) c).mul ((q1.add q2).add q3)).mono (by omega)
    exact ((e1.add e2).add e3).neg
  obtain ⟨hU, hU0⟩ := unit_of_small hu1
  set num := t1 ^ 2 + t1 * t2 + t2 ^ 2 + a * (t1 + t2) * s1 + b * s1 ^ 2 with hnum
  have hnumv : PDvd p (2 * r) num := by
    have e1 := ht1.pow 2
    have e2 := ht1.mul ht2
    have e3 := ht2.pow 2
    have e4 := ((pdvd_intCast (p := p) a).mul (ht1.add ht2)).mul hs1
    have e5 := (pdvd_intCast (p := p) b).mul (hs1.pow 2)
    refine ((((e1.mono ?_).add (e2.mono ?_)).add (e3.mono ?_)).add (e4.mono ?_)).add (e5.mono ?_)
    all_goals push_cast; omega
  set α := num / (1 + u) with hα
  have hαv : PDvd p (2 * r) α := hnumv.div_unit hU hU0
  have key : (s1 - s2) * (1 + u) = (t1 - t2) * num := by
    rw [hu, hnum]
    linear_combination C1 - C2
  set β := s1 - α * t1 with hβ
  have hβv : PDvd p (3 * r) β := hs1.sub ((hαv.mul ht1).mono (by push_cast; omega))
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
  obtain ⟨hl3, hK, hs3, -⟩ := third (p := p) a b c r hr x1 x2 x3 y1 y2 ℓ m α β hβ0 hℓ hm hy1l hy2l
    hy1 hy2 V1 V2 V3 hαv hβv ht1 ht2
  have hy3 : y3 = -(ℓ * x3 + m) := by simp only [y3]; rw [hy1l]; ring
  rw [hy3]
  refine ⟨neg_ne_zero.mpr hl3, filt_of_pdvd (neg_ne_zero.mpr hl3) hs3, hK⟩

/-- The tangent slope in `(t, s)` coordinates. -/
lemma tangent_slope (a b c t s : ℚ) (hs : s ≠ 0)
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
theorem tangent (a b c : ℤ) (r : ℕ) (hr : 1 ≤ r) {x1 y1 : ℚ} (h1 : OnCurve a b c x1 y1)
    (F1 : InFilt p r y1) :
    let ℓ := (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1)
    let x3 := ℓ ^ 2 - a - x1 - x1
    let y3 := -(ℓ * (x3 - x1) + y1)
    y3 ≠ 0 ∧ InFilt p r y3 ∧ PDvd p (3 * r) (x3 / y3 - x1 / y1 - x1 / y1) := by
  intro ℓ x3 y3
  have hℓdef : ℓ = (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1) := rfl
  have hx3def : x3 = ℓ ^ 2 - a - x1 - x1 := rfl
  have hy3def : y3 = -(ℓ * (x3 - x1) + y1) := rfl
  clear_value ℓ x3 y3
  have hy1 := F1.1
  obtain ⟨ht1, hs1⟩ := filt_ts (p := p) a b c r hr h1 F1
  have C1 := curve_ts a b c h1 hy1
  set t := x1 / y1 with htd
  set s := 1 / y1 with hsd
  set u := -((a : ℚ) * t ^ 2 + 2 * b * t * s + 3 * c * s ^ 2) with hu
  have hu1 : PDvd p 1 u := by
    have e1 : PDvd p 1 ((a : ℚ) * t ^ 2) :=
      ((pdvd_intCast (p := p) a).mul (ht1.pow 2)).mono (by push_cast; omega)
    have e2 : PDvd p 1 (2 * (b : ℚ) * t * s) := by
      have := (((pdvd_intCast (p := p) 2).mul (pdvd_intCast (p := p) b)).mul ht1).mul hs1
      push_cast at this
      exact this.mono (by omega)
    have e3 : PDvd p 1 (3 * (c : ℚ) * s ^ 2) := by
      have := ((pdvd_intCast (p := p) 3).mul (pdvd_intCast (p := p) c)).mul (hs1.pow 2)
      push_cast at this
      exact this.mono (by omega)
    exact ((e1.add e2).add e3).neg
  obtain ⟨hU, hU0⟩ := unit_of_small hu1
  set num := 3 * t ^ 2 + 2 * a * t * s + b * s ^ 2 with hnum
  have hnumv : PDvd p (2 * r) num := by
    have e1 : PDvd p (2 * r) (3 * t ^ 2) := by
      have := (pdvd_intCast (p := p) 3).mul (ht1.pow 2)
      push_cast at this; exact this.mono (by omega)
    have e2 : PDvd p (2 * r) (2 * (a : ℚ) * t * s) := by
      have := (((pdvd_intCast (p := p) 2).mul (pdvd_intCast (p := p) a)).mul ht1).mul hs1
      push_cast at this; exact this.mono (by omega)
    have e3 : PDvd p (2 * r) ((b : ℚ) * s ^ 2) := by
      have := (pdvd_intCast (p := p) b).mul (hs1.pow 2)
      push_cast at this; exact this.mono (by omega)
    exact (e1.add e2).add e3
  set α := num / (1 + u) with hα
  have hαv : PDvd p (2 * r) α := hnumv.div_unit hU hU0
  set β := s - α * t with hβ
  have hβv : PDvd p (3 * r) β := hs1.sub ((hαv.mul ht1).mono (by push_cast; omega))
  have hl1 : α * x1 + β * y1 = 1 := by rw [hβ, htd, hsd]; field_simp; ring
  -- `ℓ β = -α`, from the curve equation
  have hℓβ : ℓ * β = -α := by
    have hℓ' : ℓ = num / (2 * s) := by
      rw [hℓdef, hnum, htd, hsd]; field_simp
    have hs0 : s ≠ 0 := by rw [hsd]; simpa using hy1
    have hden : 1 - (a : ℚ) * t ^ 2 - 2 * b * t * s - 3 * c * s ^ 2 = 1 + u := by rw [hu]; ring
    rw [hℓ', hβ, hα, hnum, ← hden]
    exact tangent_slope a b c t s hs0 C1 (by rw [hden]; exact hU0)
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
  obtain ⟨hl3, hK, hs3, -⟩ := third (p := p) a b c r hr x1 x1 x3 y1 y1 ℓ m α β hβ0 hℓ hm hy1l hy1l
    hy1 hy1 V1 V2 V3 hαv hβv ht1 ht1
  have hy3 : y3 = -(ℓ * x3 + m) := by rw [hy3def, hy1l]; ring
  rw [hy3]
  exact ⟨neg_ne_zero.mpr hl3, filt_of_pdvd (neg_ne_zero.mpr hl3) hs3, hK⟩

end EllNL
