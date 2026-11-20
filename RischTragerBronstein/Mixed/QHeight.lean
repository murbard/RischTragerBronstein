import RischTragerBronstein.Mixed.EllHeight
import RischTragerBronstein.Mixed.MWTate
import RischTragerBronstein.Mixed.MWPair
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithmic height on `y² = x³ + a x + b` over `ℚ` (integer `a, b`)

The naive height `h(x) = log max(|num x|, den x)` satisfies the duplication bound
`|h(2P) − 4 h(P)| ≤ log C(a, b)` (`hP_double`): with `x = u / w` in lowest terms,
`x(2P) = φ(u, w) / ψ(u, w)` (homogeneous quartics), `max(|φ|, |ψ|) ≤ C₁ H⁴` and, by the resultant
identities `f₁φ − g₁ψ = 4Δ w⁷`, `f₂φ + g₂ψ = 4Δ u⁷` (`EllDup.res1/res2`, here over `ℤ`), the common
factor of `φ, ψ` divides `4Δ` and `4|Δ| H⁷ ≤ C₂ H³ max(|φ|, |ψ|)`.
-/

open FFHeight WeierstrassCurve WeierstrassCurve.Affine

namespace QHeight

/-! ### Integer evaluation and absolute bounds of the expression trees -/

/-- Evaluation of `WE` over `ℤ`. -/
def evZ (a b u w : ℤ) : WE → ℤ
  | .a => a
  | .b => b
  | .u => u
  | .v => w
  | .cst c => c
  | .add e f => evZ a b u w e + evZ a b u w f
  | .sub e f => evZ a b u w e - evZ a b u w f
  | .mul e f => evZ a b u w e * evZ a b u w f
  | .pow e n => evZ a b u w e ^ n

/-- The bound on `|e|` in terms of `|a|, |b|` (coefficient of `H^{deg}`). -/
def bZ (Aa Bb : ℤ) : WE → ℤ
  | .a => Aa
  | .b => Bb
  | .u => 1
  | .v => 1
  | .cst c => |c|
  | .add e f => bZ Aa Bb e + bZ Aa Bb f
  | .sub e f => bZ Aa Bb e + bZ Aa Bb f
  | .mul e f => bZ Aa Bb e * bZ Aa Bb f
  | .pow e n => bZ Aa Bb e ^ n

lemma bZ_nonneg (Aa Bb : ℤ) (hA : 0 ≤ Aa) (hB : 0 ≤ Bb) : ∀ e, 0 ≤ bZ Aa Bb e
  | .a => hA
  | .b => hB
  | .u => zero_le_one
  | .v => zero_le_one
  | .cst c => abs_nonneg c
  | .add e f => add_nonneg (bZ_nonneg Aa Bb hA hB e) (bZ_nonneg Aa Bb hA hB f)
  | .sub e f => add_nonneg (bZ_nonneg Aa Bb hA hB e) (bZ_nonneg Aa Bb hA hB f)
  | .mul e f => mul_nonneg (bZ_nonneg Aa Bb hA hB e) (bZ_nonneg Aa Bb hA hB f)
  | .pow e n => pow_nonneg (bZ_nonneg Aa Bb hA hB e) n

/-- **The bound**: `|e(u, w)| ≤ bZ e · H^{k e}` for `|u|, |w| ≤ H`, `H ≥ 1`. -/
theorem abs_evZ_le (a b u w H : ℤ) (hH : 1 ≤ H) (hu : |u| ≤ H) (hw : |w| ≤ H) :
    ∀ e : WE, |evZ a b u w e| ≤ bZ |a| |b| e * H ^ (WE.est e).2
  | .a => by simp [evZ, bZ, WE.est]
  | .b => by simp [evZ, bZ, WE.est]
  | .u => by simpa [evZ, bZ, WE.est] using hu
  | .v => by simpa [evZ, bZ, WE.est] using hw
  | .cst c => by simp [evZ, bZ, WE.est]
  | .add e f => by
    have he := abs_evZ_le a b u w H hH hu hw e
    have hf := abs_evZ_le a b u w H hH hu hw f
    have h1 : H ^ (WE.est e).2 ≤ H ^ max (WE.est e).2 (WE.est f).2 :=
      pow_le_pow_right₀ hH (le_max_left _ _)
    have h2 : H ^ (WE.est f).2 ≤ H ^ max (WE.est e).2 (WE.est f).2 :=
      pow_le_pow_right₀ hH (le_max_right _ _)
    have n1 := bZ_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) e
    have n2 := bZ_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) f
    simp only [evZ, bZ, WE.est]
    calc |evZ a b u w e + evZ a b u w f| ≤ |evZ a b u w e| + |evZ a b u w f| := abs_add_le _ _
      _ ≤ bZ |a| |b| e * H ^ (WE.est e).2 + bZ |a| |b| f * H ^ (WE.est f).2 := add_le_add he hf
      _ ≤ (bZ |a| |b| e + bZ |a| |b| f) * H ^ max (WE.est e).2 (WE.est f).2 := by
        nlinarith [mul_le_mul_of_nonneg_left h1 n1, mul_le_mul_of_nonneg_left h2 n2]
  | .sub e f => by
    have he := abs_evZ_le a b u w H hH hu hw e
    have hf := abs_evZ_le a b u w H hH hu hw f
    have h1 : H ^ (WE.est e).2 ≤ H ^ max (WE.est e).2 (WE.est f).2 :=
      pow_le_pow_right₀ hH (le_max_left _ _)
    have h2 : H ^ (WE.est f).2 ≤ H ^ max (WE.est e).2 (WE.est f).2 :=
      pow_le_pow_right₀ hH (le_max_right _ _)
    have n1 := bZ_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) e
    have n2 := bZ_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) f
    simp only [evZ, bZ, WE.est]
    calc |evZ a b u w e - evZ a b u w f| ≤ |evZ a b u w e| + |evZ a b u w f| := abs_sub _ _
      _ ≤ bZ |a| |b| e * H ^ (WE.est e).2 + bZ |a| |b| f * H ^ (WE.est f).2 := add_le_add he hf
      _ ≤ (bZ |a| |b| e + bZ |a| |b| f) * H ^ max (WE.est e).2 (WE.est f).2 := by
        nlinarith [mul_le_mul_of_nonneg_left h1 n1, mul_le_mul_of_nonneg_left h2 n2]
  | .mul e f => by
    have he := abs_evZ_le a b u w H hH hu hw e
    have hf := abs_evZ_le a b u w H hH hu hw f
    simp only [evZ, bZ, WE.est, abs_mul, pow_add]
    calc |evZ a b u w e| * |evZ a b u w f| ≤
        (bZ |a| |b| e * H ^ (WE.est e).2) * (bZ |a| |b| f * H ^ (WE.est f).2) :=
          mul_le_mul he hf (abs_nonneg _) (mul_nonneg
            (bZ_nonneg |a| |b| (abs_nonneg _) (abs_nonneg _) e) (pow_nonneg (by omega) _))
      _ = _ := by ring
  | .pow e n => by
    have he := abs_evZ_le a b u w H hH hu hw e
    simp only [evZ, bZ, WE.est, abs_pow, pow_mul]
    calc |evZ a b u w e| ^ n ≤ (bZ |a| |b| e * H ^ (WE.est e).2) ^ n :=
          pow_le_pow_left₀ (abs_nonneg _) he n
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (WE.est e).2 n]

lemma res1Z (a b u w : ℤ) :
    evZ a b u w f1E * evZ a b u w phiE + (-evZ a b u w g1E) * evZ a b u w psiE =
      (4 * evZ a b u w deltaE) * w ^ 7 := by
  simp only [evZ, f1E, g1E, phiE, psiE, deltaE]; ring

lemma res2Z (a b u w : ℤ) :
    evZ a b u w f2E * evZ a b u w phiE + evZ a b u w g2E * evZ a b u w psiE =
      (4 * evZ a b u w deltaE) * u ^ 7 := by
  simp only [evZ, f2E, g2E, phiE, psiE, deltaE]; ring

/-! ### Heights of fractions -/

/-- The height `max(|num|, den)` of a rational. -/
def Hq (x : ℚ) : ℕ := max x.num.natAbs x.den

lemma one_le_Hq (x : ℚ) : 1 ≤ Hq x := le_max_of_le_right x.den_pos

/-- **Fractions**: `F/G = num/den` with `F = num · t`, `G = den · t`. -/
lemma frac_cofactor (F G : ℤ) (hG : G ≠ 0) :
    ∃ t : ℤ, t ≠ 0 ∧ F = ((F : ℚ) / G).num * t ∧ G = (((F : ℚ) / G).den : ℤ) * t := by
  set r : ℚ := (F : ℚ) / G with hr
  have hd : (r.den : ℤ) ∣ G := by
    rw [hr, ← Rat.divInt_eq_div]; exact Rat.den_dvd F G
  obtain ⟨t, ht⟩ := hd
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht; exact hG ht
  refine ⟨t, ht0, ?_, ht⟩
  have hrq : r * G = F := by rw [hr]; field_simp
  have : (r.num : ℚ) / r.den * ((r.den : ℤ) * t : ℤ) = F := by
    rw [Rat.num_div_den, ← ht, hrq]
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have e : (F : ℚ) = (r.num * t : ℤ) := by
    rw [← this]; push_cast; field_simp
  exact_mod_cast e

/-- The cofactor divides every integer combination. -/
lemma cofactor_dvd (F G : ℤ) (t n d : ℤ) (hF : F = n * t) (hG : G = d * t) (R s w : ℤ)
    (h1 : ∃ p q, p * F + q * G = R * s) (h2 : ∃ p q, p * F + q * G = R * w) (hsw : IsCoprime s w) :
    t ∣ R := by
  obtain ⟨p1, q1, e1⟩ := h1
  obtain ⟨p2, q2, e2⟩ := h2
  obtain ⟨α, β, hab⟩ := hsw
  have : R = α * (p1 * F + q1 * G) + β * (p2 * F + q2 * G) := by
    rw [e1, e2]; linear_combination (-R) * hab
  rw [this, hF, hG]
  exact ⟨α * (p1 * n + q1 * d) + β * (p2 * n + q2 * d), by ring⟩

/-! ### The curve over `ℚ` and the duplication bound -/

/-- `y² = x³ + a x + b` over `ℚ`. -/
def qW (a b : ℤ) : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

/-- The logarithmic height of a point (`0` at `O`). -/
noncomputable def hP (a b : ℤ) : (qW a b).toAffine.Point → ℝ
  | .zero => 0
  | .some x _ _ => Real.log (Hq x)

/-- The constant `C₁` (`max(|φ|, |ψ|) ≤ C₁ H⁴`). -/
def C1 (a b : ℤ) : ℤ := max (bZ |a| |b| phiE) (bZ |a| |b| psiE)
/-- The constant `C₂` (`4|Δ| H⁷ ≤ C₂ H³ max(|φ|, |ψ|)`). -/
def C2 (a b : ℤ) : ℤ := max (bZ |a| |b| f1E + bZ |a| |b| g1E) (bZ |a| |b| f2E + bZ |a| |b| g2E)
/-- `max(1, |a|, |b|)`. -/
def M0 (a b : ℤ) : ℤ := max 1 (max |a| |b|)
/-- **The duplication constant.** -/
def Cq (a b : ℤ) : ℤ := max (C1 a b) (max (C2 a b) (M0 a b ^ 4))

lemma one_le_M0 (a b : ℤ) : 1 ≤ M0 a b := le_max_left _ _
lemma one_le_Cq (a b : ℤ) : 1 ≤ Cq a b :=
  le_max_of_le_right (le_max_of_le_right (one_le_pow₀ (one_le_M0 a b)))

lemma coprime_num_den (x : ℚ) : IsCoprime x.num (x.den : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact x.reduced

/-- The `2`-torsion case: `x` is an integer root of the cubic, so `H ≤ M₀`. -/
lemma Hq_le_M0_of_root (a b : ℤ) (x : ℚ) (h : x ^ 3 + a * x + b = 0) : (Hq x : ℤ) ≤ M0 a b := by
  have hdq : (x.den : ℚ) ≠ 0 := by positivity
  have hpoly : x.num ^ 3 + a * x.num * (x.den : ℤ) ^ 2 + b * (x.den : ℤ) ^ 3 = 0 := by
    have hq : ((x.num ^ 3 + a * x.num * (x.den : ℤ) ^ 2 + b * (x.den : ℤ) ^ 3 : ℤ) : ℚ) = 0 := by
      have e : ((x.num ^ 3 + a * x.num * (x.den : ℤ) ^ 2 + b * (x.den : ℤ) ^ 3 : ℤ) : ℚ) =
          (x.den : ℚ) ^ 3 * (x ^ 3 + a * x + b) := by
        have hx : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
        push_cast
        rw [hx]; ring
      rw [e, h, mul_zero]
    exact_mod_cast hq
  have hc := coprime_num_den x
  have hwu : (x.den : ℤ) ∣ x.num ^ 3 :=
    ⟨-(a * x.num * (x.den : ℤ) + b * (x.den : ℤ) ^ 2), by linear_combination hpoly⟩
  have hden : x.den = 1 := by
    have hu : IsUnit (x.den : ℤ) := (hc.pow_left (m := 3)).symm.isUnit_of_dvd' (dvd_refl _) hwu
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact_mod_cast h1
    · have := x.den_pos; omega
  rw [hden] at hpoly
  push_cast at hpoly
  have hH : (Hq x : ℤ) = max |x.num| 1 := by
    simp [Hq, hden]
  rw [hH]
  set u := x.num
  have key : |u| ≤ max |a| |b| ∨ u = 0 := by
    by_cases hb : b = 0
    · subst hb
      by_cases hu : u = 0
      · exact Or.inr hu
      · left
        have hsq : u ^ 2 = -a := by
          have : u * (u ^ 2 + a) = 0 := by linear_combination hpoly
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hu
          · linarith
        have h1 : 1 ≤ |u| := Int.one_le_abs hu
        have hua : |u| ≤ |a| := by
          calc |u| ≤ |u| ^ 2 := by nlinarith
            _ = |u ^ 2| := (abs_pow u 2).symm
            _ = |a| := by rw [hsq, abs_neg]
        exact le_max_of_le_left hua
    · by_cases hu : u = 0
      · exact Or.inr hu
      left
      have hub : u ∣ b := ⟨-(u ^ 2 + a), by linear_combination hpoly⟩
      exact le_max_of_le_right (Int.le_of_dvd (abs_pos.mpr hb) ((abs_dvd_abs _ _).mpr hub))
  rcases key with h | h
  · exact max_le (h.trans (le_max_right _ _)) (le_max_left _ _)
  · rw [h]; simp [M0]

theorem C1_bound (a b u w : ℤ) (H : ℤ) (hH : 1 ≤ H) (hu : |u| ≤ H) (hw : |w| ≤ H) :
    |evZ a b u w phiE| ≤ C1 a b * H ^ 4 ∧ |evZ a b u w psiE| ≤ C1 a b * H ^ 4 := by
  have h1 := abs_evZ_le a b u w H hH hu hw phiE
  have h2 := abs_evZ_le a b u w H hH hu hw psiE
  have e1 : (WE.est phiE).2 = 4 := by decide
  have e2 : (WE.est psiE).2 = 4 := by decide
  rw [e1] at h1; rw [e2] at h2
  have hp : 0 ≤ H ^ 4 := by positivity
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp),
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)⟩

theorem C2_bound (a b u w : ℤ) (H : ℤ) (hH : 1 ≤ H) (hu : |u| ≤ H) (hw : |w| ≤ H)
    (hmax : H = |u| ∨ H = |w|) :
    |4 * evZ a b u w deltaE| * H ^ 7 ≤
      C2 a b * H ^ 3 * max |evZ a b u w phiE| |evZ a b u w psiE| := by
  set F := evZ a b u w phiE
  set G := evZ a b u w psiE
  set M := max |F| |G|
  have hM : 0 ≤ M := le_max_of_le_left (abs_nonneg _)
  have hF : |F| ≤ M := le_max_left _ _
  have hG : |G| ≤ M := le_max_right _ _
  have bf1 := abs_evZ_le a b u w H hH hu hw f1E
  have bg1 := abs_evZ_le a b u w H hH hu hw g1E
  have bf2 := abs_evZ_le a b u w H hH hu hw f2E
  have bg2 := abs_evZ_le a b u w H hH hu hw g2E
  have e1 : (WE.est f1E).2 = 3 := by decide
  have e2 : (WE.est g1E).2 = 3 := by decide
  have e3 : (WE.est f2E).2 = 3 := by decide
  have e4 : (WE.est g2E).2 = 3 := by decide
  rw [e1] at bf1; rw [e2] at bg1; rw [e3] at bf2; rw [e4] at bg2
  have hH3 : 0 ≤ H ^ 3 := by positivity
  -- `|4Δ| |w|⁷ ≤ (b f₁ + b g₁) H³ M`
  have hw7 : |4 * evZ a b u w deltaE| * |w| ^ 7 ≤
      (bZ |a| |b| f1E + bZ |a| |b| g1E) * H ^ 3 * M := by
    have := res1Z a b u w
    rw [← abs_pow, ← abs_mul, ← this]
    calc |evZ a b u w f1E * F + -evZ a b u w g1E * G|
        ≤ |evZ a b u w f1E| * |F| + |evZ a b u w g1E| * |G| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_neg]
      _ ≤ (bZ |a| |b| f1E * H ^ 3) * M + (bZ |a| |b| g1E * H ^ 3) * M :=
          add_le_add (mul_le_mul bf1 hF (abs_nonneg _) (mul_nonneg (bZ_nonneg _ _ (abs_nonneg _)
            (abs_nonneg _) _) hH3)) (mul_le_mul bg1 hG (abs_nonneg _) (mul_nonneg (bZ_nonneg _ _
            (abs_nonneg _) (abs_nonneg _) _) hH3))
      _ = _ := by ring
  have hu7 : |4 * evZ a b u w deltaE| * |u| ^ 7 ≤
      (bZ |a| |b| f2E + bZ |a| |b| g2E) * H ^ 3 * M := by
    have := res2Z a b u w
    rw [← abs_pow, ← abs_mul, ← this]
    calc |evZ a b u w f2E * F + evZ a b u w g2E * G|
        ≤ |evZ a b u w f2E| * |F| + |evZ a b u w g2E| * |G| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ (bZ |a| |b| f2E * H ^ 3) * M + (bZ |a| |b| g2E * H ^ 3) * M :=
          add_le_add (mul_le_mul bf2 hF (abs_nonneg _) (mul_nonneg (bZ_nonneg _ _ (abs_nonneg _)
            (abs_nonneg _) _) hH3)) (mul_le_mul bg2 hG (abs_nonneg _) (mul_nonneg (bZ_nonneg _ _
            (abs_nonneg _) (abs_nonneg _) _) hH3))
      _ = _ := by ring
  have hC2a : bZ |a| |b| f1E + bZ |a| |b| g1E ≤ C2 a b := le_max_left _ _
  have hC2b : bZ |a| |b| f2E + bZ |a| |b| g2E ≤ C2 a b := le_max_right _ _
  have hH3M : 0 ≤ H ^ 3 * M := mul_nonneg hH3 hM
  rcases hmax with h | h
  · rw [h]
    calc |4 * evZ a b u w deltaE| * |u| ^ 7 ≤ (bZ |a| |b| f2E + bZ |a| |b| g2E) * H ^ 3 * M := hu7
      _ ≤ C2 a b * H ^ 3 * M := by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hC2b hH3M
      _ = C2 a b * |u| ^ 3 * M := by rw [h]
  · rw [h]
    calc |4 * evZ a b u w deltaE| * |w| ^ 7 ≤ (bZ |a| |b| f1E + bZ |a| |b| g1E) * H ^ 3 * M := hw7
      _ ≤ C2 a b * H ^ 3 * M := by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hC2a hH3M
      _ = C2 a b * |w| ^ 3 * M := by rw [h]

/-- **The duplication bound on heights of fractions.** For `x = u/w` (lowest terms) with
`ψ(u, w) ≠ 0`, `r = φ(u,w)/ψ(u,w)` satisfies `H(r) ≤ C₁ H(x)⁴` and `H(x)⁴ ≤ C₂ H(r)`. -/
theorem Hq_dup (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (x : ℚ)
    (hψ : evZ a b x.num x.den psiE ≠ 0) :
    (Hq ((evZ a b x.num x.den phiE : ℚ) / evZ a b x.num x.den psiE) : ℤ) ≤ C1 a b * (Hq x) ^ 4 ∧
      ((Hq x : ℤ)) ^ 4 ≤ C2 a b * Hq ((evZ a b x.num x.den phiE : ℚ) / evZ a b x.num x.den psiE) := by
  have hw0 : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  have hH1 : (1 : ℤ) ≤ (Hq x : ℤ) := by exact_mod_cast one_le_Hq x
  have hHx : (Hq x : ℤ) = max |x.num| |(x.den : ℤ)| := by
    simp [Hq, abs_of_pos hw0]
  set u := x.num
  set w : ℤ := (x.den : ℤ)
  set F := evZ a b u w phiE
  set G := evZ a b u w psiE
  set H := (Hq x : ℤ)
  have hu : |u| ≤ H := hHx ▸ le_max_left _ _
  have hw : |w| ≤ H := hHx ▸ le_max_right _ _
  have hmax : H = |u| ∨ H = |w| := by
    rw [hHx]; rcases le_total |u| |w| with h | h
    · right; exact max_eq_right h
    · left; exact max_eq_left h
  obtain ⟨t, ht0, hF, hG⟩ := frac_cofactor F G hψ
  generalize hr : ((F : ℚ) / G) = r at hF hG ⊢
  have hrd : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have hHr : (Hq r : ℤ) = max |r.num| (r.den : ℤ) := by simp [Hq]
  have hM : max |F| |G| = |t| * Hq r := by
    rw [hHr, hF, hG, abs_mul, abs_mul, abs_of_pos hrd, mul_comm |r.num|, mul_comm (r.den : ℤ),
      ← mul_max_of_nonneg _ _ (abs_nonneg t)]
  have ht1 : 1 ≤ |t| := Int.one_le_abs ht0
  have hr0 : (0 : ℤ) ≤ Hq r := by positivity
  obtain ⟨b1, b2⟩ := C1_bound a b u w H hH1 hu hw
  refine ⟨?_, ?_⟩
  · calc (Hq r : ℤ) ≤ |t| * Hq r := le_mul_of_one_le_left hr0 ht1
      _ = max |F| |G| := hM.symm
      _ ≤ C1 a b * H ^ 4 := max_le b1 b2
  · have hΔ' : evZ a b u w deltaE ≠ 0 := by simp only [evZ, deltaE]; exact hΔ
    have h4Δ : 4 * evZ a b u w deltaE ≠ 0 := mul_ne_zero (by norm_num) hΔ'
    have htd : t ∣ 4 * evZ a b u w deltaE :=
      cofactor_dvd F G t r.num r.den hF hG (4 * evZ a b u w deltaE) (w ^ 7) (u ^ 7)
        ⟨_, _, res1Z a b u w⟩ ⟨_, _, res2Z a b u w⟩
        ((coprime_num_den x).symm.pow_left.pow_right)
    have htle : |t| ≤ |4 * evZ a b u w deltaE| :=
      Int.le_of_dvd (abs_pos.mpr h4Δ) ((abs_dvd_abs _ _).mpr htd)
    have hc2 := C2_bound a b u w H hH1 hu hw hmax
    rw [hM] at hc2
    have hpos : 0 < |4 * evZ a b u w deltaE| * H ^ 3 := by positivity
    have hC2 : 0 ≤ C2 a b := le_max_of_le_left (add_nonneg (bZ_nonneg _ _ (abs_nonneg _)
      (abs_nonneg _) _) (bZ_nonneg _ _ (abs_nonneg _) (abs_nonneg _) _))
    have : |4 * evZ a b u w deltaE| * H ^ 3 * H ^ 4 ≤
        |4 * evZ a b u w deltaE| * H ^ 3 * (C2 a b * Hq r) := by
      calc |4 * evZ a b u w deltaE| * H ^ 3 * H ^ 4 = |4 * evZ a b u w deltaE| * H ^ 7 := by ring
        _ ≤ C2 a b * H ^ 3 * (|t| * Hq r) := hc2
        _ ≤ C2 a b * H ^ 3 * (|4 * evZ a b u w deltaE| * Hq r) := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos

/-- **The duplication bound** `|h(2P) − 4 h(P)| ≤ log C(a, b)`. -/
theorem hP_double (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (P : (qW a b).toAffine.Point) :
    |hP a b (P + P) - 4 * hP a b P| ≤ Real.log (Cq a b) := by
  have hCq : (1 : ℝ) ≤ Cq a b := by exact_mod_cast one_le_Cq a b
  have hlogC : 0 ≤ Real.log (Cq a b) := Real.log_nonneg hCq
  rcases P with _ | ⟨x, y, h⟩
  · have e : (Point.zero : (qW a b).toAffine.Point) + Point.zero = Point.zero := rfl
    simp [e, hP, hlogC]
  have hb2 : (qW a b).b₂ = 0 := by simp [WeierstrassCurve.b₂, qW]
  have hb4 : (qW a b).b₄ = 2 * a := by simp [WeierstrassCurve.b₄, qW]
  have hb6 : (qW a b).b₆ = 4 * b := by simp [WeierstrassCurve.b₆, qW]
  have hb8 : (qW a b).b₈ = -(a : ℚ) ^ 2 := by simp [WeierstrassCurve.b₈, qW]
  have hH1 : (1 : ℝ) ≤ Hq x := by exact_mod_cast one_le_Hq x
  have hHpos : (0 : ℝ) < Hq x := by linarith
  by_cases hy : y = (qW a b).toAffine.negY x y
  · rw [Point.add_self_of_Y_eq hy]
    have hden := (den_duplication_eq_zero_iff h.1).mpr hy
    rw [hb2, hb4, hb6] at hden
    have hroot : x ^ 3 + a * x + b = 0 := by linear_combination hden / 4
    have hle := Hq_le_M0_of_root a b x hroot
    simp only [hP]
    have h4 : ((Hq x : ℤ)) ^ 4 ≤ Cq a b :=
      (pow_le_pow_left₀ (by positivity) hle 4).trans (le_max_of_le_right (le_max_right _ _))
    have h4' : (Hq x : ℝ) ^ 4 ≤ Cq a b := by exact_mod_cast h4
    have : 4 * Real.log (Hq x) ≤ Real.log (Cq a b) := by
      rw [show (4 : ℝ) * Real.log (Hq x) = Real.log ((Hq x : ℝ) ^ 4) by
        rw [Real.log_pow]; norm_num]
      exact Real.log_le_log (by positivity) h4'
    have h0 : 0 ≤ Real.log (Hq x) := Real.log_nonneg hH1
    rw [abs_le]; constructor <;> linarith
  · rw [Point.add_self_of_Y_ne hy]
    have hden := (den_duplication_eq_zero_iff h.1).not.mpr hy
    have hx2 := addX_self_of_Y_ne h.1 hy
    rw [hb2, hb4, hb6, hb8] at hx2
    rw [hb2, hb4, hb6] at hden
    set u := x.num
    set w : ℤ := (x.den : ℤ)
    have hwq : (w : ℚ) ≠ 0 := by simp [w]
    have hxuw : x = (u : ℚ) / w := by simp [u, w, Rat.num_div_den]
    have hphi : ((evZ a b u w phiE : ℤ) : ℚ) = (w : ℚ) ^ 4 *
        (x ^ 4 - 2 * a * x ^ 2 - 2 * (4 * b) * x - -(a : ℚ) ^ 2) := by
      rw [hxuw]; simp only [evZ, phiE]; push_cast; field_simp; ring
    have hpsi : ((evZ a b u w psiE : ℤ) : ℚ) = (w : ℚ) ^ 4 *
        (4 * x ^ 3 + 0 * x ^ 2 + 2 * (2 * a) * x + 4 * b) := by
      rw [hxuw]; simp only [evZ, psiE]; push_cast; field_simp; ring
    have hψ : evZ a b u w psiE ≠ 0 := by
      intro h0
      have := congrArg (fun z : ℤ ↦ (z : ℚ)) h0
      simp only [hpsi, Int.cast_zero] at this
      exact mul_ne_zero (pow_ne_zero 4 hwq) hden this
    have hx2' : (qW a b).toAffine.addX x x ((qW a b).toAffine.slope x x y y) =
        (evZ a b u w phiE : ℚ) / evZ a b u w psiE := by
      rw [hphi, hpsi, mul_div_mul_left _ _ (pow_ne_zero 4 hwq)]
      exact hx2
    obtain ⟨d1, d2⟩ := Hq_dup a b hΔ x hψ
    simp only [hP]
    rw [hx2']
    set r : ℚ := (evZ a b u w phiE : ℚ) / evZ a b u w psiE
    have hr1 : (1 : ℝ) ≤ Hq r := by exact_mod_cast one_le_Hq r
    have hC1 : (C1 a b : ℝ) ≤ Cq a b := by exact_mod_cast le_max_left _ _
    have hC2 : (C2 a b : ℝ) ≤ Cq a b := by exact_mod_cast le_max_of_le_right (le_max_left _ _)
    have d1' : (Hq r : ℝ) ≤ Cq a b * (Hq x : ℝ) ^ 4 := by
      have : (Hq r : ℝ) ≤ C1 a b * (Hq x : ℝ) ^ 4 := by exact_mod_cast d1
      exact this.trans (by gcongr)
    have d2' : (Hq x : ℝ) ^ 4 ≤ Cq a b * Hq r := by
      have : (Hq x : ℝ) ^ 4 ≤ C2 a b * Hq r := by exact_mod_cast d2
      exact this.trans (by gcongr)
    have hCpos : (0 : ℝ) < Cq a b := by linarith
    have e4 : (4 : ℝ) * Real.log (Hq x) = Real.log ((Hq x : ℝ) ^ 4) := by
      rw [Real.log_pow]; norm_num
    have l1 : Real.log (Hq r) ≤ Real.log (Cq a b) + 4 * Real.log (Hq x) := by
      rw [e4, ← Real.log_mul hCpos.ne' (by positivity)]
      exact Real.log_le_log (by linarith) d1'
    have l2 : 4 * Real.log (Hq x) ≤ Real.log (Cq a b) + Real.log (Hq r) := by
      rw [e4, ← Real.log_mul hCpos.ne' (by positivity)]
      exact Real.log_le_log (by positivity) d2'
    rw [abs_le]; constructor <;> linarith

/-! ### Torsion points have canonical height `0`; the executable certificate -/

/-- **Torsion ⇒ `ĥ = 0`** (generic: bounded orbit of the doubling). -/
theorem canon_torsion {G : Type*} [AddCommGroup G] {h : G → ℝ} {C : ℝ}
    (hC : ∀ P, |h (MWPair.dbl P) - 4 * h P| ≤ C) (P : G) (n : ℕ) (hn : 0 < n) (h0 : n • P = 0) :
    MWTate.canon MWPair.dbl h P = 0 := by
  set B := ∑ j ∈ Finset.range n, |h (j • P)|
  have hmod : ∀ m : ℕ, m • P = (m % n) • P := fun m ↦ by
    conv_lhs => rw [← Nat.mod_add_div m n]
    rw [add_nsmul, mul_nsmul, h0, nsmul_zero, add_zero]
  have hb : ∀ k : ℕ, |h (MWPair.dbl^[k] P)| ≤ B := fun k ↦ by
    rw [MWPair.dbl_iter, hmod]
    exact Finset.single_le_sum (f := fun j ↦ |h (j • P)|) (fun j _ ↦ abs_nonneg _)
      (Finset.mem_range.mpr (Nat.mod_lt _ hn))
  have ht : Filter.Tendsto (MWTate.seq MWPair.dbl h P) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun k : ℕ ↦ B * (1 / 4 : ℝ) ^ k) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      simpa using this.const_mul B
    refine squeeze_zero_norm (fun k ↦ ?_) hg
    simp only [MWTate.seq, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k),
      one_div_pow]
    rw [div_le_iff₀ (by positivity)]
    calc |h (MWPair.dbl^[k] P)| ≤ B := hb k
      _ = B * (1 / 4 ^ k) * 4 ^ k := by field_simp
  exact tendsto_nhds_unique (MWTate.tendsto_canon hC P) ht

/-- One executable doubling of `x` (`none` at `2P = O`). -/
def xDbl (a b : ℤ) (x : ℚ) : Option ℚ :=
  if evZ a b x.num x.den psiE = 0 then none
  else some ((evZ a b x.num x.den phiE : ℚ) / evZ a b x.num x.den psiE)

/-- `k` doublings. -/
def xIter (a b : ℤ) : ℕ → ℚ → Option ℚ
  | 0, x => some x
  | k + 1, x => (xDbl a b x).bind (xIter a b k)

/-- **The certificate**: `H(x(2ᵏP))³ > C(a, b)`. -/
def certH (a b : ℤ) (k : ℕ) (x : ℚ) : Bool :=
  match xIter a b k x with
  | some x' => decide (Cq a b < (Hq x' : ℤ) ^ 3)
  | none => false

/-- The doubling of an affine point with `ψ(x) ≠ 0`. -/
lemma dbl_some (a b : ℤ) (x y : ℚ) (h : (qW a b).toAffine.Nonsingular x y)
    (hψ : evZ a b x.num x.den psiE ≠ 0) :
    ∃ y' h', Point.some x y h + Point.some x y h =
      Point.some ((evZ a b x.num x.den phiE : ℚ) / evZ a b x.num x.den psiE) y' h' := by
  have hb2 : (qW a b).b₂ = 0 := by simp [WeierstrassCurve.b₂, qW]
  have hb4 : (qW a b).b₄ = 2 * a := by simp [WeierstrassCurve.b₄, qW]
  have hb6 : (qW a b).b₆ = 4 * b := by simp [WeierstrassCurve.b₆, qW]
  have hb8 : (qW a b).b₈ = -(a : ℚ) ^ 2 := by simp [WeierstrassCurve.b₈, qW]
  have hwq : ((x.den : ℤ) : ℚ) ≠ 0 := by simp
  have hnum : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
  have hpsi : ((evZ a b x.num x.den psiE : ℤ) : ℚ) = ((x.den : ℤ) : ℚ) ^ 4 *
      (4 * x ^ 3 + 0 * x ^ 2 + 2 * (2 * a) * x + 4 * b) := by
    simp only [evZ, psiE]; push_cast; rw [hnum]; ring
  have hphi : ((evZ a b x.num x.den phiE : ℤ) : ℚ) = ((x.den : ℤ) : ℚ) ^ 4 *
      (x ^ 4 - 2 * a * x ^ 2 - 2 * (4 * b) * x - -(a : ℚ) ^ 2) := by
    simp only [evZ, phiE]; push_cast; rw [hnum]; ring
  have hden : 4 * x ^ 3 + (qW a b).b₂ * x ^ 2 + 2 * (qW a b).b₄ * x + (qW a b).b₆ ≠ 0 := by
    rw [hb2, hb4, hb6]
    intro h0
    apply hψ
    have : ((evZ a b x.num x.den psiE : ℤ) : ℚ) = 0 := by rw [hpsi, h0, mul_zero]
    exact_mod_cast this
  have hy : y ≠ (qW a b).toAffine.negY x y := fun hy ↦ hden ((den_duplication_eq_zero_iff h.1).mpr hy)
  rw [Point.add_self_of_Y_ne hy]
  have hx2 := addX_self_of_Y_ne h.1 hy
  rw [hb2, hb4, hb6, hb8] at hx2
  have e : (qW a b).toAffine.addX x x ((qW a b).toAffine.slope x x y y) =
      (evZ a b x.num x.den phiE : ℚ) / evZ a b x.num x.den psiE := by
    rw [hphi, hpsi, mul_div_mul_left _ _ (pow_ne_zero 4 hwq)]; exact hx2
  generalize_proofs hP2
  exact ⟨_, by rw [← e]; exact hP2, by simp only [Point.some.injEq, e, and_self]⟩

lemma xIter_spec (a b : ℤ) : ∀ (k : ℕ) (x x' : ℚ) (y : ℚ) (h : (qW a b).toAffine.Nonsingular x y),
    xIter a b k x = some x' → ∃ y' h', MWPair.dbl^[k] (Point.some x y h) = Point.some x' y' h'
  | 0, x, x', y, h, hx => by
    simp only [xIter, Option.some.injEq] at hx
    subst hx; exact ⟨y, h, rfl⟩
  | k + 1, x, x', y, h, hx => by
    simp only [xIter, xDbl] at hx
    split_ifs at hx with hψ
    · simp at hx
    simp only [Option.bind] at hx
    obtain ⟨y1, h1, e1⟩ := dbl_some a b x y h hψ
    obtain ⟨y', h', e'⟩ := xIter_spec a b k _ x' y1 h1 hx
    refine ⟨y', h', ?_⟩
    rw [Function.iterate_succ_apply, MWPair.dbl, e1, e']

/-- **A passing certificate proves infinite order.** -/
theorem nontors_of_certH (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (k : ℕ) (x y : ℚ)
    (h : (qW a b).toAffine.Nonsingular x y) (hc : certH a b k x = true) (n : ℤ)
    (hn : n • Point.some x y h = 0) : n = 0 := by
  unfold certH at hc
  split at hc
  · rename_i x' hx'
    simp only [decide_eq_true_eq] at hc
    obtain ⟨y', h', e'⟩ := xIter_spec a b k x x' y h hx'
    have hC := hP_double a b hΔ
    have happ := MWPair.canon_approx (h := hP a b) hC k (Point.some x y h)
    rw [e'] at happ
    simp only [hP] at happ
    have hCpos : (0 : ℝ) < Cq a b := by exact_mod_cast (one_le_Cq a b).trans_lt' (by norm_num)
    have hc' : (Cq a b : ℝ) < (Hq x' : ℝ) ^ 3 := by exact_mod_cast hc
    have hlog : Real.log (Cq a b) < 3 * Real.log (Hq x') := by
      rw [show (3 : ℝ) * Real.log (Hq x') = Real.log ((Hq x' : ℝ) ^ 3) by rw [Real.log_pow]; norm_num]
      exact Real.log_lt_log hCpos hc'
    have hpos : 0 < MWTate.canon MWPair.dbl (hP a b) (Point.some x y h) := by
      rw [abs_le] at happ
      have h4 : (0 : ℝ) < 4 ^ k := by positivity
      have : Real.log (Cq a b) / 3 / 4 ^ k < Real.log (Hq x') / 4 ^ k := by
        apply div_lt_div_of_pos_right _ h4; linarith
      linarith [happ.1]
    by_contra hn0
    have h0 : (n.natAbs : ℕ) • Point.some x y h = 0 := by
      rcases Int.natAbs_eq n with e | e
      · rw [← natCast_zsmul, ← e, hn]
      · rw [← natCast_zsmul, show ((n.natAbs : ℕ) : ℤ) = -n by omega, neg_zsmul, hn, neg_zero]
    have := canon_torsion hC _ n.natAbs (Int.natAbs_pos.mpr hn0) h0
    linarith
  · exact absurd hc (by decide)

end QHeight
