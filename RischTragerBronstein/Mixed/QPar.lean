import RischTragerBronstein.Mixed.QHeight
import RischTragerBronstein.Mixed.EllPar

/-!
# The parallelogram bound for the logarithmic height over `ℚ`

On `y² = x³ + a x + b` (`a, b ∈ ℤ`): `|h(P+Q) + h(P−Q) − 2h(P) − 2h(Q)| ≤ log C'` (`hP_par`). For
`x₁ ≠ x₂`, `x(P±Q)` are the roots of `W₀X² − W₁X + W₂` (`EllPar.sum_addX/prod_addX`, `W` homogeneous
of bidegree `(2, 2)` in `(u₁, w₁), (u₂, w₂)`), and `H(x₃)H(x₄) ≤ 2 max|Wᵢ|` (Gauss's lemma,
`dvd_of_primZ`, and `max(|q₃q₄|, |q₃p₄+p₃q₄|, |p₃p₄|) ≥ H₃H₄/2`); the lower bound follows from the
upper one applied to `P ± Q` and the duplication bound.
-/

open FFHeight WeierstrassCurve WeierstrassCurve.Affine

namespace QHeight

/-! ### Two-point expressions over `ℤ` -/

/-- Evaluation of `WE2` over `ℤ`. -/
def evZ2 (a b u1 w1 u2 w2 : ℤ) : WE2 → ℤ
  | .a => a
  | .b => b
  | .u1 => u1
  | .v1 => w1
  | .u2 => u2
  | .v2 => w2
  | .cst c => c
  | .add e f => evZ2 a b u1 w1 u2 w2 e + evZ2 a b u1 w1 u2 w2 f
  | .sub e f => evZ2 a b u1 w1 u2 w2 e - evZ2 a b u1 w1 u2 w2 f
  | .mul e f => evZ2 a b u1 w1 u2 w2 e * evZ2 a b u1 w1 u2 w2 f
  | .pow e n => evZ2 a b u1 w1 u2 w2 e ^ n

/-- The coefficient bound. -/
def bZ2 (Aa Bb : ℤ) : WE2 → ℤ
  | .a => Aa
  | .b => Bb
  | .u1 => 1
  | .v1 => 1
  | .u2 => 1
  | .v2 => 1
  | .cst c => |c|
  | .add e f => bZ2 Aa Bb e + bZ2 Aa Bb f
  | .sub e f => bZ2 Aa Bb e + bZ2 Aa Bb f
  | .mul e f => bZ2 Aa Bb e * bZ2 Aa Bb f
  | .pow e n => bZ2 Aa Bb e ^ n

lemma bZ2_nonneg (Aa Bb : ℤ) (hA : 0 ≤ Aa) (hB : 0 ≤ Bb) : ∀ e, 0 ≤ bZ2 Aa Bb e
  | .a => hA
  | .b => hB
  | .u1 => zero_le_one
  | .v1 => zero_le_one
  | .u2 => zero_le_one
  | .v2 => zero_le_one
  | .cst c => abs_nonneg c
  | .add e f => add_nonneg (bZ2_nonneg Aa Bb hA hB e) (bZ2_nonneg Aa Bb hA hB f)
  | .sub e f => add_nonneg (bZ2_nonneg Aa Bb hA hB e) (bZ2_nonneg Aa Bb hA hB f)
  | .mul e f => mul_nonneg (bZ2_nonneg Aa Bb hA hB e) (bZ2_nonneg Aa Bb hA hB f)
  | .pow e n => pow_nonneg (bZ2_nonneg Aa Bb hA hB e) n

lemma pow_mono_aux (H : ℤ) (hH : 1 ≤ H) {m n : ℕ} (h : m ≤ n) : H ^ m ≤ H ^ n :=
  pow_le_pow_right₀ hH h

/-- **The bound** `|e| ≤ bZ2 e · H₁^{k₁} H₂^{k₂}`. -/
theorem abs_evZ2_le (a b u1 w1 u2 w2 H1 H2 : ℤ) (h1 : 1 ≤ H1) (h2 : 1 ≤ H2) (hu1 : |u1| ≤ H1)
    (hw1 : |w1| ≤ H1) (hu2 : |u2| ≤ H2) (hw2 : |w2| ≤ H2) :
    ∀ e : WE2, |evZ2 a b u1 w1 u2 w2 e| ≤
      bZ2 |a| |b| e * (H1 ^ (WE2.est e).2.1 * H2 ^ (WE2.est e).2.2)
  | .a => by simp [evZ2, bZ2, WE2.est]
  | .b => by simp [evZ2, bZ2, WE2.est]
  | .u1 => by simpa [evZ2, bZ2, WE2.est] using hu1
  | .v1 => by simpa [evZ2, bZ2, WE2.est] using hw1
  | .u2 => by simpa [evZ2, bZ2, WE2.est] using hu2
  | .v2 => by simpa [evZ2, bZ2, WE2.est] using hw2
  | .cst c => by simp [evZ2, bZ2, WE2.est]
  | .add e f => by
    have he := abs_evZ2_le a b u1 w1 u2 w2 H1 H2 h1 h2 hu1 hw1 hu2 hw2 e
    have hf := abs_evZ2_le a b u1 w1 u2 w2 H1 H2 h1 h2 hu1 hw1 hu2 hw2 f
    have n1 := bZ2_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) e
    have n2 := bZ2_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) f
    have m1 : H1 ^ (WE2.est e).2.1 * H2 ^ (WE2.est e).2.2 ≤
        H1 ^ max (WE2.est e).2.1 (WE2.est f).2.1 * H2 ^ max (WE2.est e).2.2 (WE2.est f).2.2 :=
      mul_le_mul (pow_mono_aux H1 h1 (le_max_left _ _)) (pow_mono_aux H2 h2 (le_max_left _ _))
        (by positivity) (by positivity)
    have m2 : H1 ^ (WE2.est f).2.1 * H2 ^ (WE2.est f).2.2 ≤
        H1 ^ max (WE2.est e).2.1 (WE2.est f).2.1 * H2 ^ max (WE2.est e).2.2 (WE2.est f).2.2 :=
      mul_le_mul (pow_mono_aux H1 h1 (le_max_right _ _)) (pow_mono_aux H2 h2 (le_max_right _ _))
        (by positivity) (by positivity)
    simp only [evZ2, bZ2, WE2.est]
    calc _ ≤ |evZ2 a b u1 w1 u2 w2 e| + |evZ2 a b u1 w1 u2 w2 f| := abs_add_le _ _
      _ ≤ _ := add_le_add he hf
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left m1 n1, mul_le_mul_of_nonneg_left m2 n2]
  | .sub e f => by
    have he := abs_evZ2_le a b u1 w1 u2 w2 H1 H2 h1 h2 hu1 hw1 hu2 hw2 e
    have hf := abs_evZ2_le a b u1 w1 u2 w2 H1 H2 h1 h2 hu1 hw1 hu2 hw2 f
    have n1 := bZ2_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) e
    have n2 := bZ2_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) f
    have m1 : H1 ^ (WE2.est e).2.1 * H2 ^ (WE2.est e).2.2 ≤
        H1 ^ max (WE2.est e).2.1 (WE2.est f).2.1 * H2 ^ max (WE2.est e).2.2 (WE2.est f).2.2 :=
      mul_le_mul (pow_mono_aux H1 h1 (le_max_left _ _)) (pow_mono_aux H2 h2 (le_max_left _ _))
        (by positivity) (by positivity)
    have m2 : H1 ^ (WE2.est f).2.1 * H2 ^ (WE2.est f).2.2 ≤
        H1 ^ max (WE2.est e).2.1 (WE2.est f).2.1 * H2 ^ max (WE2.est e).2.2 (WE2.est f).2.2 :=
      mul_le_mul (pow_mono_aux H1 h1 (le_max_right _ _)) (pow_mono_aux H2 h2 (le_max_right _ _))
        (by positivity) (by positivity)
    simp only [evZ2, bZ2, WE2.est]
    calc _ ≤ |evZ2 a b u1 w1 u2 w2 e| + |evZ2 a b u1 w1 u2 w2 f| := abs_sub _ _
      _ ≤ _ := add_le_add he hf
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left m1 n1, mul_le_mul_of_nonneg_left m2 n2]
  | .mul e f => by
    have he := abs_evZ2_le a b u1 w1 u2 w2 H1 H2 h1 h2 hu1 hw1 hu2 hw2 e
    have hf := abs_evZ2_le a b u1 w1 u2 w2 H1 H2 h1 h2 hu1 hw1 hu2 hw2 f
    simp only [evZ2, bZ2, WE2.est, abs_mul, pow_add]
    calc |evZ2 a b u1 w1 u2 w2 e| * |evZ2 a b u1 w1 u2 w2 f| ≤
        (bZ2 |a| |b| e * (H1 ^ (WE2.est e).2.1 * H2 ^ (WE2.est e).2.2)) *
          (bZ2 |a| |b| f * (H1 ^ (WE2.est f).2.1 * H2 ^ (WE2.est f).2.2)) :=
          mul_le_mul he hf (abs_nonneg _) (mul_nonneg
            (bZ2_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) e) (by positivity))
      _ = _ := by ring
  | .pow e n => by
    have he := abs_evZ2_le a b u1 w1 u2 w2 H1 H2 h1 h2 hu1 hw1 hu2 hw2 e
    simp only [evZ2, bZ2, WE2.est, abs_pow]
    calc |evZ2 a b u1 w1 u2 w2 e| ^ n ≤
        (bZ2 |a| |b| e * (H1 ^ (WE2.est e).2.1 * H2 ^ (WE2.est e).2.2)) ^ n :=
          pow_le_pow_left₀ (abs_nonneg _) he n
      _ = _ := by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (WE2.est e).2.1 n,
          mul_comm (WE2.est e).2.2 n]

/-! ### Gauss's lemma over `ℤ` and heights of the roots of a quadratic -/

theorem dvd_of_primZ (p3 q3 p4 q4 W0 Z : ℤ) (hc3 : IsCoprime q3 p3) (hc4 : IsCoprime q4 p4)
    (h2 : Z ∣ W0 * (q3 * q4)) (h1 : Z ∣ W0 * (q3 * p4 + p3 * q4)) (h0 : Z ∣ W0 * (p3 * p4)) :
    Z ∣ W0 := by
  have hA : Z ∣ W0 * (q3 * p4) ^ 2 := by
    have : W0 * (q3 * p4) ^ 2 = W0 * (q3 * p4 + p3 * q4) * (q3 * p4) - W0 * (q3 * q4) * (p3 * p4) := by
      ring
    rw [this]; exact dvd_sub (h1.mul_right _) (h2.mul_right _)
  have hB : Z ∣ W0 * (p3 * q4) ^ 2 := by
    have : W0 * (p3 * q4) ^ 2 = W0 * (q3 * p4 + p3 * q4) * (p3 * q4) - W0 * (q3 * q4) * (p3 * p4) := by
      ring
    rw [this]; exact dvd_sub (h1.mul_right _) (h2.mul_right _)
  obtain ⟨a, b, hab⟩ := hc4.pow (m := 2) (n := 2)
  obtain ⟨c, d, hcd⟩ := hc3.pow (m := 2) (n := 2)
  have hq3 : Z ∣ W0 * q3 ^ 2 := by
    have : W0 * q3 ^ 2 = a * (W0 * (q3 * q4) * (q3 * q4)) + b * (W0 * (q3 * p4) ^ 2) := by
      linear_combination (-(W0 * q3 ^ 2)) * hab
    rw [this]; exact dvd_add ((h2.mul_right _).mul_left _) (hA.mul_left _)
  have hp3 : Z ∣ W0 * p3 ^ 2 := by
    have : W0 * p3 ^ 2 = a * (W0 * (p3 * q4) ^ 2) + b * (W0 * (p3 * p4) * (p3 * p4)) := by
      linear_combination (-(W0 * p3 ^ 2)) * hab
    rw [this]; exact dvd_add (hB.mul_left _) ((h0.mul_right _).mul_left _)
  have : W0 = c * (W0 * q3 ^ 2) + d * (W0 * p3 ^ 2) := by linear_combination (-W0) * hcd
  rw [this]; exact dvd_add (hq3.mul_left _) (hp3.mul_left _)

/-- **Gauss-type inequality** for the product of two linear forms. -/
theorem gaussZ (p3 q3 p4 q4 : ℤ) :
    max |p3| |q3| * max |p4| |q4| ≤
      2 * max |q3 * q4| (max |q3 * p4 + p3 * q4| |p3 * p4|) := by
  set M := max |q3 * q4| (max |q3 * p4 + p3 * q4| |p3 * p4|)
  have m0 : |q3 * q4| ≤ M := le_max_left _ _
  have m1 : |q3 * p4 + p3 * q4| ≤ M := le_max_of_le_right (le_max_left _ _)
  have m2 : |p3 * p4| ≤ M := le_max_of_le_right (le_max_right _ _)
  have hM : 0 ≤ M := (abs_nonneg _).trans m0
  rw [abs_mul] at m0 m2
  have t1 : |q3 * p4| ≤ |q3 * p4 + p3 * q4| + |p3 * q4| := by
    have := abs_sub (q3 * p4 + p3 * q4) (p3 * q4); simpa using this
  have t2 : |p3 * q4| ≤ |q3 * p4 + p3 * q4| + |q3 * p4| := by
    have := abs_sub (q3 * p4 + p3 * q4) (q3 * p4); simpa using this
  simp only [abs_mul] at t1 t2
  rcases le_total |p3| |q3| with h3 | h3 <;> rcases le_total |p4| |q4| with h4 | h4
  · rw [max_eq_right h3, max_eq_right h4]; linarith [abs_nonneg q3, abs_nonneg q4]
  · -- `q₃`, `p₄` dominate
    rw [max_eq_right h3, max_eq_left h4]
    have k : |p3| * |q4| ≤ |p3| * |p4| := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    generalize |q3| * |p4| = X at *
    generalize |p3| * |q4| = Y at *
    generalize |q3 * p4 + p3 * q4| = Z at *
    generalize |p3| * |p4| = V at *
    linarith
  · rw [max_eq_left h3, max_eq_right h4]
    have k : |q3| * |p4| ≤ |p3| * |p4| := mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
    generalize |q3| * |p4| = X at *
    generalize |p3| * |q4| = Y at *
    generalize |q3 * p4 + p3 * q4| = Z at *
    generalize |p3| * |p4| = V at *
    linarith
  · rw [max_eq_left h3, max_eq_left h4]; linarith [abs_nonneg p3, abs_nonneg p4]

/-- **Heights of the roots of a quadratic over `ℚ`.** -/
theorem Hq_roots_le (x3 x4 : ℚ) (W0 W1 W2 : ℤ) (hW0 : W0 ≠ 0)
    (hs : x3 + x4 = (W1 : ℚ) / W0) (hp : x3 * x4 = (W2 : ℚ) / W0) :
    ((Hq x3 : ℤ)) * Hq x4 ≤ 2 * max |W0| (max |W1| |W2|) := by
  set p3 := x3.num
  set q3 : ℤ := (x3.den : ℤ)
  set p4 := x4.num
  set q4 : ℤ := (x4.den : ℤ)
  have hq3 : (0 : ℤ) < q3 := by simp [q3, x3.den_pos]
  have hq4 : (0 : ℤ) < q4 := by simp [q4, x4.den_pos]
  have hx3 : (p3 : ℚ) = x3 * q3 := by simp [p3, q3, Rat.mul_den_eq_num]
  have hx4 : (p4 : ℚ) = x4 * q4 := by simp [p4, q4, Rat.mul_den_eq_num]
  have hW0q : (W0 : ℚ) ≠ 0 := by exact_mod_cast hW0
  have r1 : W0 * (q3 * p4 + p3 * q4) = q3 * q4 * W1 := by
    have : ((W0 * (q3 * p4 + p3 * q4) : ℤ) : ℚ) = ((q3 * q4 * W1 : ℤ) : ℚ) := by
      push_cast; rw [hx3, hx4]
      have : (W1 : ℚ) = W0 * (x3 + x4) := by rw [hs]; field_simp
      rw [this]; ring
    exact_mod_cast this
  have r0 : W0 * (p3 * p4) = q3 * q4 * W2 := by
    have : ((W0 * (p3 * p4) : ℤ) : ℚ) = ((q3 * q4 * W2 : ℤ) : ℚ) := by
      push_cast; rw [hx3, hx4]
      have : (W2 : ℚ) = W0 * (x3 * x4) := by rw [hp]; field_simp
      rw [this]; ring
    exact_mod_cast this
  have hc3 : IsCoprime q3 p3 := (coprime_num_den x3).symm
  have hc4 : IsCoprime q4 p4 := (coprime_num_den x4).symm
  obtain ⟨c, hc⟩ := dvd_of_primZ p3 q3 p4 q4 W0 (q3 * q4) hc3 hc4 ⟨W0, by ring⟩ ⟨W1, r1⟩ ⟨W2, r0⟩
  have hqq : q3 * q4 ≠ 0 := by positivity
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hW0 hc
  have e1 : W1 = c * (q3 * p4 + p3 * q4) := by
    apply mul_left_cancel₀ hqq; rw [← r1, hc]; ring
  have e2 : W2 = c * (p3 * p4) := by
    apply mul_left_cancel₀ hqq; rw [← r0, hc]; ring
  have hH3 : (Hq x3 : ℤ) = max |p3| |q3| := by simp [Hq, p3, q3]
  have hH4 : (Hq x4 : ℤ) = max |p4| |q4| := by simp [Hq, p4, q4]
  rw [hH3, hH4]
  have g := gaussZ p3 q3 p4 q4
  have hc1 : 1 ≤ |c| := Int.one_le_abs hc0
  have k0 : |q3 * q4| ≤ |W0| := by
    rw [hc, abs_mul (q3 * q4) c]; exact le_mul_of_one_le_right (abs_nonneg _) hc1
  have k1 : |q3 * p4 + p3 * q4| ≤ |W1| := by
    rw [e1, abs_mul c]; exact le_mul_of_one_le_left (abs_nonneg _) hc1
  have k2 : |p3 * p4| ≤ |W2| := by
    rw [e2, abs_mul c]; exact le_mul_of_one_le_left (abs_nonneg _) hc1
  have hmax : max |q3 * q4| (max |q3 * p4 + p3 * q4| |p3 * p4|) ≤ max |W0| (max |W1| |W2|) :=
    max_le_max k0 (max_le_max k1 k2)
  linarith

/-! ### The parallelogram bound on the curve -/

/-- `max |Wᵢ| ≤ Cw H₁² H₂²`. -/
def Cw (a b : ℤ) : ℤ := max (bZ2 |a| |b| w0E) (max (bZ2 |a| |b| w1E) (bZ2 |a| |b| w2E))

/-- The upper parallelogram constant. -/
def Cpu (a b : ℤ) : ℤ := max (2 * Cw a b) (Cq a b)

lemma one_le_Cpu (a b : ℤ) : 1 ≤ Cpu a b := le_max_of_le_right (one_le_Cq a b)

lemma eq_qW (a b : ℤ) {x y : ℚ} (h : (qW a b).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a * x + b := by
  have := (equation_iff x y).mp h
  simpa [qW] using this

lemma negY_qW (a b : ℤ) (x y : ℚ) : (qW a b).toAffine.negY x y = -y := by simp [negY, qW]

lemma addX_qW (a b : ℤ) (x1 x2 ℓ : ℚ) : (qW a b).toAffine.addX x1 x2 ℓ = ℓ ^ 2 - x1 - x2 := by
  simp [addX, qW]

lemma hP_neg (a b : ℤ) (Q : (qW a b).toAffine.Point) : hP a b (-Q) = hP a b Q := by
  rcases Q with _ | ⟨x, y, h⟩ <;> rfl

/-- The generic case `x₁ ≠ x₂`. -/
theorem Hq_par_generic (a b : ℤ) (x1 y1 x2 y2 : ℚ) (h1 : (qW a b).toAffine.Equation x1 y1)
    (h2 : (qW a b).toAffine.Equation x2 y2) (hx : x1 ≠ x2) :
    ((Hq (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) : ℤ)) * Hq (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) ≤
      2 * Cw a b * ((Hq x1 : ℤ) ^ 2 * (Hq x2 : ℤ) ^ 2) := by
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  have hw1 : (0 : ℤ) < (x1.den : ℤ) := by exact_mod_cast x1.den_pos
  have hw2 : (0 : ℤ) < (x2.den : ℤ) := by exact_mod_cast x2.den_pos
  have hH1 : (Hq x1 : ℤ) = max |x1.num| |(x1.den : ℤ)| := by simp [Hq, abs_of_pos hw1]
  have hH2 : (Hq x2 : ℤ) = max |x2.num| |(x2.den : ℤ)| := by simp [Hq, abs_of_pos hw2]
  have hn1 : (x1.num : ℚ) = x1 * ((x1.den : ℤ) : ℚ) := by
    rw [Int.cast_natCast]; exact (Rat.mul_den_eq_num x1).symm
  have hn2 : (x2.num : ℚ) = x2 * ((x2.den : ℤ) : ℚ) := by
    rw [Int.cast_natCast]; exact (Rat.mul_den_eq_num x2).symm
  set u1 := x1.num; set w1 : ℤ := (x1.den : ℤ)
  set u2 := x2.num; set w2 : ℤ := (x2.den : ℤ)
  set W0 := evZ2 a b u1 w1 u2 w2 w0E
  set W1 := evZ2 a b u1 w1 u2 w2 w1E
  set W2 := evZ2 a b u1 w1 u2 w2 w2E
  have hww : ((w1 : ℚ) * w2) ^ 2 ≠ 0 := by positivity
  have eW0 : (W0 : ℚ) = ((w1 : ℚ) * w2) ^ 2 * (x1 - x2) ^ 2 := by
    simp only [W0, evZ2, w0E]; push_cast; rw [hn1, hn2]; ring
  have eW1 : (W1 : ℚ) = ((w1 : ℚ) * w2) ^ 2 * (2 * ((x1 + x2) * (x1 * x2 + a) + 2 * b)) := by
    simp only [W1, evZ2, w1E]; push_cast; rw [hn1, hn2]; ring
  have eW2 : (W2 : ℚ) = ((w1 : ℚ) * w2) ^ 2 * ((x1 * x2 - a) ^ 2 - 4 * b * (x1 + x2)) := by
    simp only [W2, evZ2, w2E]; push_cast; rw [hn1, hn2]; ring
  have hW0 : W0 ≠ 0 := by
    intro h0
    have : (W0 : ℚ) = 0 := by exact_mod_cast h0
    rw [eW0] at this
    exact mul_ne_zero hww (pow_ne_zero 2 hd) this
  have hs := sum_addX x1 x2 y1 y2 (a : ℚ) b (eq_qW a b h1) (eq_qW a b h2) hd
  have hp := prod_addX x1 x2 y1 y2 (a : ℚ) b (eq_qW a b h1) (eq_qW a b h2) hd
  have hs' : (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) + (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) =
      (W1 : ℚ) / W0 := by
    rw [hs, eW0, eW1, mul_div_mul_left _ _ hww]
  have hp' : (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) * (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2) =
      (W2 : ℚ) / W0 := by
    rw [hp, eW0, eW2, mul_div_mul_left _ _ hww]
  have hr := Hq_roots_le _ _ W0 W1 W2 hW0 hs' hp'
  have hb1 : 1 ≤ (Hq x1 : ℤ) := by exact_mod_cast one_le_Hq x1
  have hb2 : 1 ≤ (Hq x2 : ℤ) := by exact_mod_cast one_le_Hq x2
  have B := abs_evZ2_le a b u1 w1 u2 w2 (Hq x1) (Hq x2) hb1 hb2 (hH1 ▸ le_max_left _ _)
    (hH1 ▸ le_max_right _ _) (hH2 ▸ le_max_left _ _) (hH2 ▸ le_max_right _ _)
  have b0 := B w0E
  have b1 := B w1E
  have b2 := B w2E
  rw [est_w.1] at b0; rw [est_w.2.1] at b1; rw [est_w.2.2] at b2
  simp only at b0 b1 b2
  have hpos : (0 : ℤ) ≤ (Hq x1 : ℤ) ^ 2 * (Hq x2 : ℤ) ^ 2 := by positivity
  have c0 : bZ2 |a| |b| w0E ≤ Cw a b := le_max_left _ _
  have c1 : bZ2 |a| |b| w1E ≤ Cw a b := le_max_of_le_right (le_max_left _ _)
  have c2 : bZ2 |a| |b| w2E ≤ Cw a b := le_max_of_le_right (le_max_right _ _)
  have hm : max |W0| (max |W1| |W2|) ≤ Cw a b * ((Hq x1 : ℤ) ^ 2 * (Hq x2 : ℤ) ^ 2) :=
    max_le (b0.trans (mul_le_mul_of_nonneg_right c0 hpos))
      (max_le (b1.trans (mul_le_mul_of_nonneg_right c1 hpos))
        (b2.trans (mul_le_mul_of_nonneg_right c2 hpos)))
  linarith

/-- **The upper parallelogram bound.** -/
theorem hP_par_upper (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (P Q : (qW a b).toAffine.Point) :
    hP a b (P + Q) + hP a b (P - Q) ≤ 2 * hP a b P + 2 * hP a b Q + Real.log (Cpu a b) := by
  have hCu : (1 : ℝ) ≤ Cpu a b := by exact_mod_cast one_le_Cpu a b
  have hlog : 0 ≤ Real.log (Cpu a b) := Real.log_nonneg hCu
  have hCqu : Real.log (Cq a b) ≤ Real.log (Cpu a b) := by
    have : (Cq a b : ℝ) ≤ Cpu a b := by exact_mod_cast le_max_right _ _
    exact Real.log_le_log (by exact_mod_cast (one_le_Cq a b).trans_lt' (by norm_num)) this
  have hnn : ∀ R : (qW a b).toAffine.Point, 0 ≤ hP a b R := fun R ↦ by
    rcases R with _ | ⟨x, y, h⟩
    · exact le_refl _
    · exact Real.log_nonneg (by exact_mod_cast one_le_Hq x)
  rcases P with _ | ⟨x1, y1, h1⟩
  · have e : (Point.zero : (qW a b).toAffine.Point) = 0 := rfl
    rw [e, zero_add, zero_sub, hP_neg]
    have := hnn Q
    simp only [hP] at *; linarith
  rcases Q with _ | ⟨x2, y2, h2⟩
  · have e : (Point.zero : (qW a b).toAffine.Point) = 0 := rfl
    rw [e, add_zero, sub_zero]
    have := hnn (Point.some x1 y1 h1)
    simp only [hP] at *; linarith
  rw [sub_eq_add_neg, Point.neg_some]
  have hdbl := hP_double a b hΔ (Point.some x1 y1 h1)
  rw [abs_le] at hdbl
  by_cases hx : x1 = x2
  · subst hx
    have hQ : hP a b (Point.some x1 y2 h2) = hP a b (Point.some x1 y1 h1) := rfl
    by_cases hy : y1 = (qW a b).toAffine.negY x1 y2
    · rw [Point.add_of_Y_eq rfl hy]
      have e : (Point.some x1 ((qW a b).toAffine.negY x1 y2)
          ((nonsingular_neg ..).mpr h2) : (qW a b).toAffine.Point) = Point.some x1 y1 h1 := by
        simp only [Point.some.injEq]; exact ⟨trivial, hy.symm⟩
      rw [e, hQ]
      have z : hP a b (0 : (qW a b).toAffine.Point) = 0 := rfl
      rw [z]; linarith
    · have hy2 : y1 = y2 := Y_eq_of_Y_ne h1.1 h2.1 rfl hy
      subst hy2
      have e2 : Point.some x1 y1 h2 = Point.some x1 y1 h1 := rfl
      rw [e2, Point.add_of_Y_eq (h₂ := (nonsingular_neg ..).mpr h1) rfl (negY_negY _ _).symm, hQ]
      have z : hP a b (0 : (qW a b).toAffine.Point) = 0 := rfl
      rw [z]; linarith
  · rw [Point.add_of_X_ne hx, Point.add_of_X_ne hx]
    simp only [hP, addX_qW, slope_of_X_ne hx, negY_qW, sub_neg_eq_add]
    have g := Hq_par_generic a b x1 y1 x2 y2 h1.1 h2.1 hx
    set H3 := Hq (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2)
    set H4 := Hq (((y1 + y2) / (x1 - x2)) ^ 2 - x1 - x2)
    have h3 : (1 : ℝ) ≤ H3 := by exact_mod_cast one_le_Hq _
    have h4 : (1 : ℝ) ≤ H4 := by exact_mod_cast one_le_Hq _
    have g1 : (1 : ℝ) ≤ Hq x1 := by exact_mod_cast one_le_Hq _
    have g2 : (1 : ℝ) ≤ Hq x2 := by exact_mod_cast one_le_Hq _
    have g' : (H3 : ℝ) * H4 ≤ (Cpu a b : ℝ) * ((Hq x1 : ℝ) ^ 2 * (Hq x2 : ℝ) ^ 2) := by
      have : (H3 : ℝ) * H4 ≤ 2 * Cw a b * ((Hq x1 : ℝ) ^ 2 * (Hq x2 : ℝ) ^ 2) := by exact_mod_cast g
      refine this.trans ?_
      have hc : ((2 * Cw a b : ℤ) : ℝ) ≤ Cpu a b := by exact_mod_cast le_max_left _ _
      push_cast at hc
      gcongr
    have hCpos : (0 : ℝ) < Cpu a b := by linarith
    have := Real.log_le_log (by positivity) g'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hCpos.ne' (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith

/-- **The parallelogram bound** `|h(P+Q) + h(P−Q) − 2h(P) − 2h(Q)| ≤ log C_u + log C`. -/
theorem hP_par (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (P Q : (qW a b).toAffine.Point) :
    |hP a b (P + Q) + hP a b (P - Q) - 2 * hP a b P - 2 * hP a b Q| ≤
      Real.log (Cpu a b) + Real.log (Cq a b) := by
  have up := hP_par_upper a b hΔ
  have lo : ∀ R, 4 * hP a b R ≤ hP a b (R + R) + Real.log (Cq a b) := fun R ↦ by
    have := hP_double a b hΔ R; rw [abs_le] at this; linarith
  have hCq : 0 ≤ Real.log (Cq a b) := Real.log_nonneg (by exact_mod_cast one_le_Cq a b)
  have hCu : 0 ≤ Real.log (Cpu a b) := Real.log_nonneg (by exact_mod_cast one_le_Cpu a b)
  have u2 := up (P + Q) (P - Q)
  have e1 : P + Q + (P - Q) = P + P := by abel
  have e2 : P + Q - (P - Q) = Q + Q := by abel
  rw [e1, e2] at u2
  have lP := lo P
  have lQ := lo Q
  have u1 := up P Q
  rw [abs_le]; constructor <;> linarith

/-! ### The two-point certificate over `ℚ` -/

/-- **Independence from approximations** (generic). -/
theorem indep_of_bounds {G : Type*} [AddCommGroup G] {h : G → ℝ} {C C' : ℝ}
    (hC : ∀ P, |h (MWPair.dbl P) - 4 * h P| ≤ C)
    (hC' : ∀ P Q, |h (P + Q) + h (P - Q) - 2 * h P - 2 * h Q| ≤ C') (P Q : G) (a b c e : ℝ)
    (ha : |MWTate.canon MWPair.dbl h P - a| ≤ e) (hb : |MWTate.canon MWPair.dbl h Q - b| ≤ e)
    (hc : |MWTate.canon MWPair.dbl h (P + Q) - c| ≤ e)
    (hgap : e * (|a| + |b| + e) + 3 * e / 2 * (|c - a - b| + 3 * e / 2) <
      |a * b - ((c - a - b) / 2) ^ 2|)
    (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 := by
  refine MWPair.indep_of_gram hC hC' P Q ?_ m n hrel
  rw [MWPair.gram_pairing]
  intro h0
  have := MWPair.gram_perturb _ _ _ _ _ _ _ ha hb hc
  rw [h0, zero_sub, abs_neg] at this
  linarith

/-- The bit length `⌊log₂ n⌋ + 1`. -/
def bitLen (n : ℕ) : ℕ := Nat.log2 n + 1

lemma log_bounds (n : ℕ) (hn : 1 ≤ n) :
    ((bitLen n : ℝ) - 1) * Real.log 2 ≤ Real.log n ∧ Real.log n ≤ (bitLen n : ℝ) * Real.log 2 := by
  have h1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
  have h2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have : ((2 : ℝ) ^ Nat.log2 n) ≤ n := by exact_mod_cast h1
    have := Real.log_le_log (by positivity) this
    rw [Real.log_pow] at this
    simp only [bitLen]; push_cast; linarith
  · have : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log2 n + 1) := by exact_mod_cast h2.le
    have := Real.log_le_log hn' this
    rw [Real.log_pow] at this
    simp only [bitLen]; push_cast at this ⊢; linarith

/-- The rational gap check (units of `log 2`). -/
def gapQ (LP LQ LR LC k : ℕ) : Bool :=
  let α : ℚ := ((LP : ℚ) - 1 / 2) / 4 ^ k
  let β : ℚ := ((LQ : ℚ) - 1 / 2) / 4 ^ k
  let γ : ℚ := ((LR : ℚ) - 1 / 2) / 4 ^ k
  let ε : ℚ := ((LC : ℚ) / 3 + 1 / 2) / 4 ^ k
  decide (ε * (|α| + |β| + ε) + 3 * ε / 2 * (|γ - α - β| + 3 * ε / 2) <
    |α * β - ((γ - α - β) / 2) ^ 2|)

/-- **The two-point certificate** for `P = (x₁, y₁)`, `Q = (x₂, y₂)`. -/
def certG (a b : ℤ) (k : ℕ) (x1 y1 x2 y2 : ℚ) : Bool :=
  x1 != x2 &&
  match xIter a b k x1, xIter a b k x2, xIter a b k (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) with
  | some p, some q, some r => gapQ (bitLen (Hq p)) (bitLen (Hq q)) (bitLen (Hq r))
      (bitLen (Cq a b).toNat) k
  | _, _, _ => false

/-- An approximation of `ĥ` from the bit length of `H(x(2ᵏP))`. -/
lemma canon_approx_bits (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (k : ℕ) (x y : ℚ)
    (h : (qW a b).toAffine.Nonsingular x y) (x' : ℚ) (hx : xIter a b k x = some x') :
    |MWTate.canon MWPair.dbl (hP a b) (Point.some x y h) -
        ((bitLen (Hq x') : ℝ) - 1 / 2) / 4 ^ k * Real.log 2| ≤
      ((bitLen (Cq a b).toNat : ℝ) / 3 + 1 / 2) / 4 ^ k * Real.log 2 := by
  obtain ⟨y', h', e'⟩ := xIter_spec a b k x x' y h hx
  have happ := MWPair.canon_approx (h := hP a b) (hP_double a b hΔ) k (Point.some x y h)
  rw [e'] at happ
  simp only [hP] at happ
  obtain ⟨l1, l2⟩ := log_bounds (Hq x') (one_le_Hq x')
  have hCq1 : 1 ≤ (Cq a b).toNat := by have := one_le_Cq a b; omega
  obtain ⟨-, c2⟩ := log_bounds (Cq a b).toNat hCq1
  have hcast : ((Cq a b).toNat : ℝ) = (Cq a b : ℝ) := by
    have := one_le_Cq a b
    exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [hcast] at c2
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_le] at happ ⊢
  constructor
  · have : ((bitLen (Hq x') : ℝ) - 1 / 2) / 4 ^ k * Real.log 2 - Real.log (Hq x') / 4 ^ k ≤
        Real.log 2 / 2 / 4 ^ k := by
      rw [div_mul_eq_mul_div, ← sub_div, div_le_div_iff_of_pos_right h4]; nlinarith
    have : Real.log (Cq a b) / 3 / 4 ^ k ≤ (bitLen (Cq a b).toNat : ℝ) / 3 / 4 ^ k * Real.log 2 := by
      rw [div_div, div_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      linarith
    have e1 : ((bitLen (Cq a b).toNat : ℝ) / 3 + 1 / 2) / 4 ^ k * Real.log 2 =
        (bitLen (Cq a b).toNat : ℝ) / 3 / 4 ^ k * Real.log 2 + Real.log 2 / 2 / 4 ^ k := by ring
    linarith [happ.1]
  · have : Real.log (Hq x') / 4 ^ k - ((bitLen (Hq x') : ℝ) - 1 / 2) / 4 ^ k * Real.log 2 ≤
        Real.log 2 / 2 / 4 ^ k := by
      rw [div_mul_eq_mul_div, ← sub_div, div_le_div_iff_of_pos_right h4]; nlinarith
    have : Real.log (Cq a b) / 3 / 4 ^ k ≤ (bitLen (Cq a b).toNat : ℝ) / 3 / 4 ^ k * Real.log 2 := by
      rw [div_div, div_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      linarith
    have e1 : ((bitLen (Cq a b).toNat : ℝ) / 3 + 1 / 2) / 4 ^ k * Real.log 2 =
        (bitLen (Cq a b).toNat : ℝ) / 3 / 4 ^ k * Real.log 2 + Real.log 2 / 2 / 4 ^ k := by ring
    linarith [happ.2]

/-- **A passing two-point certificate proves independence over `ℚ`.** -/
theorem indepQ_of_certG (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (k : ℕ) (x1 y1 x2 y2 : ℚ)
    (h1 : (qW a b).toAffine.Nonsingular x1 y1) (h2 : (qW a b).toAffine.Nonsingular x2 y2)
    (hc : certG a b k x1 y1 x2 y2 = true) (m n : ℤ)
    (hrel : m • Point.some x1 y1 h1 = n • Point.some x2 y2 h2) : m = 0 ∧ n = 0 := by
  simp only [certG, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨hx, hc⟩ := hc
  split at hc
  · rename_i p q r hp hq hr
    have hx3e : (qW a b).toAffine.addX x1 x2 ((qW a b).toAffine.slope x1 x2 y1 y2) =
        ((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2 := by rw [addX_qW, slope_of_X_ne hx]
    have h3 : (qW a b).toAffine.Nonsingular (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2)
        ((qW a b).toAffine.addY x1 x2 y1 ((qW a b).toAffine.slope x1 x2 y1 y2)) := by
      rw [← hx3e]; exact nonsingular_add h1 h2 (fun hxy ↦ hx hxy.1)
    have hsum : Point.some x1 y1 h1 + Point.some x2 y2 h2 =
        Point.some (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) _ h3 := by
      rw [Point.add_of_X_ne hx]
      simp only [Point.some.injEq, hx3e, and_self]
    set ℓ := Real.log 2
    have hℓ : 0 < ℓ := Real.log_pos (by norm_num)
    have aP := canon_approx_bits a b hΔ k x1 y1 h1 p hp
    have aQ := canon_approx_bits a b hΔ k x2 y2 h2 q hq
    have aR := canon_approx_bits a b hΔ k _ _ h3 r hr
    rw [← hsum] at aR
    simp only [gapQ, decide_eq_true_eq] at hc
    set α : ℚ := ((bitLen (Hq p) : ℚ) - 1 / 2) / 4 ^ k
    set β : ℚ := ((bitLen (Hq q) : ℚ) - 1 / 2) / 4 ^ k
    set γ : ℚ := ((bitLen (Hq r) : ℚ) - 1 / 2) / 4 ^ k
    set ε : ℚ := ((bitLen (Cq a b).toNat : ℚ) / 3 + 1 / 2) / 4 ^ k
    have eα : ((bitLen (Hq p) : ℝ) - 1 / 2) / 4 ^ k * ℓ = (α : ℝ) * ℓ := by simp [α]
    have eβ : ((bitLen (Hq q) : ℝ) - 1 / 2) / 4 ^ k * ℓ = (β : ℝ) * ℓ := by simp [β]
    have eγ : ((bitLen (Hq r) : ℝ) - 1 / 2) / 4 ^ k * ℓ = (γ : ℝ) * ℓ := by simp [γ]
    have eε : ((bitLen (Cq a b).toNat : ℝ) / 3 + 1 / 2) / 4 ^ k * ℓ = (ε : ℝ) * ℓ := by simp [ε]
    rw [eα, eε] at aP; rw [eβ, eε] at aQ; rw [eγ, eε] at aR
    refine indep_of_bounds (hP_double a b hΔ) (hP_par a b hΔ) _ _ _ _ _ _ aP aQ aR ?_ m n hrel
    have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
    push_cast [Rat.cast_abs] at hc'
    have hℓ2 : 0 < ℓ * ℓ := mul_pos hℓ hℓ
    have key : ∀ u v w e : ℝ, e * ℓ * (|u * ℓ| + |v * ℓ| + e * ℓ) +
        3 * (e * ℓ) / 2 * (|w * ℓ - u * ℓ - v * ℓ| + 3 * (e * ℓ) / 2) =
        (ℓ * ℓ) * (e * (|u| + |v| + e) + 3 * e / 2 * (|w - u - v| + 3 * e / 2)) := by
      intro u v w e
      rw [abs_mul u, abs_mul v, show w * ℓ - u * ℓ - v * ℓ = (w - u - v) * ℓ by ring, abs_mul,
        abs_of_pos hℓ]; ring
    have key2 : ∀ u v w : ℝ, |u * ℓ * (v * ℓ) - ((w * ℓ - u * ℓ - v * ℓ) / 2) ^ 2| =
        (ℓ * ℓ) * |u * v - ((w - u - v) / 2) ^ 2| := by
      intro u v w
      rw [show u * ℓ * (v * ℓ) - ((w * ℓ - u * ℓ - v * ℓ) / 2) ^ 2 =
        (ℓ * ℓ) * (u * v - ((w - u - v) / 2) ^ 2) by ring, abs_mul, abs_of_pos hℓ2]
    rw [key, key2]
    exact mul_lt_mul_of_pos_left hc' hℓ2
  · exact absurd hc (by decide)

end QHeight
