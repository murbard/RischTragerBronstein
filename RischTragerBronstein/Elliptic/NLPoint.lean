import RischTragerBronstein.Elliptic.NLCases
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Nagell–Lutz on Mathlib's point group

`W a b c = ⟨0, a, 0, b, c⟩ : WeierstrassCurve ℚ` (`y² = x³ + ax² + bx + c`). `InF p r P`: the
filtration (`v_p(y) ≤ -3r`); `tv P = x/y`. `add_filt`: the filtration is closed under addition and
`t(P + Q) ≡ t(P) + t(Q) (mod p^{3r})`; `nsmul_filt`: `t(nP) ≡ n t(P)`.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllNL

open PVal

/-- `y² = x³ + a x² + b x + c`. -/
def W (a b c : ℤ) : WeierstrassCurve ℚ := ⟨0, a, 0, b, c⟩

variable {p : ℕ} [hp : Fact p.Prime] (a b c : ℤ)

lemma equation_W {x y : ℚ} : (W a b c).toAffine.Equation x y ↔ OnCurve a b c x y := by
  rw [equation_iff]; simp [W, OnCurve]

lemma negY_W (x y : ℚ) : (W a b c).toAffine.negY x y = -y := by simp [negY, W]

/-- `t = x / y` (`0` at the origin). -/
def tv : (W a b c).toAffine.Point → ℚ
  | .zero => 0
  | .some x y _ => x / y

/-- The filtration `E(p^r)`. -/
def InF (p : ℕ) (r : ℕ) : (W a b c).toAffine.Point → Prop
  | .zero => True
  | .some _ y _ => InFilt p r y

lemma inFilt_neg {r : ℕ} {y : ℚ} (h : InFilt p r y) : InFilt p r (-y) :=
  ⟨neg_ne_zero.mpr h.1, by rw [padicValRat.neg]; exact h.2⟩

/-- **The filtration is closed under addition, and `t` is additive modulo `p^{3r}`.** -/
theorem add_filt (r : ℕ) (hr : 1 ≤ r) (P Q : (W a b c).toAffine.Point) (hP : InF a b c p r P)
    (hQ : InF a b c p r Q) :
    InF a b c p r (P + Q) ∧ PDvd p (3 * r) (tv a b c (P + Q) - tv a b c P - tv a b c Q) := by
  rcases P with _ | ⟨x1, y1, h1⟩
  · have e : (Point.zero : (W a b c).toAffine.Point) + Q = Q := zero_add Q
    rw [e]
    refine ⟨hQ, ?_⟩
    have : tv a b c Q - tv a b c Point.zero - tv a b c Q = 0 := by simp [tv]
    rw [this]; exact pdvd_zero _
  rcases Q with _ | ⟨x2, y2, h2⟩
  · have e : (Point.some x1 y1 h1 : (W a b c).toAffine.Point) + Point.zero =
        Point.some x1 y1 h1 := add_zero _
    rw [e]
    refine ⟨hP, ?_⟩
    have : tv a b c (Point.some x1 y1 h1) - tv a b c (Point.some x1 y1 h1) -
        tv a b c Point.zero = 0 := by simp [tv]
    rw [this]; exact pdvd_zero _
  have e1 := (equation_W a b c).mp h1.1
  have e2 := (equation_W a b c).mp h2.1
  by_cases hxy : x1 = x2 ∧ y1 = (W a b c).toAffine.negY x2 y2
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    refine ⟨trivial, ?_⟩
    obtain ⟨rfl, hy⟩ := hxy
    rw [negY_W] at hy
    subst hy
    simp only [tv]
    have : (0 : ℚ) - x1 / -y2 - x1 / y2 = 0 := by ring
    rw [this]; exact pdvd_zero _
  · rw [Point.add_some hxy]
    simp only [InF, tv] at hP hQ ⊢
    by_cases hx : x1 = x2
    · subst hx
      have hy : y1 ≠ (W a b c).toAffine.negY x1 y2 := fun h ↦ hxy ⟨rfl, h⟩
      have hyy := Y_eq_of_Y_ne h1.1 h2.1 rfl hy
      subst hyy
      rw [slope_of_Y_ne rfl hy]
      have hsl : (3 * x1 ^ 2 + 2 * (W a b c).a₂ * x1 + (W a b c).a₄ - (W a b c).a₁ * y1) /
          (y1 - (W a b c).toAffine.negY x1 y1) = (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1) := by
        rw [negY_W]; simp [W]; ring
      rw [hsl]
      obtain ⟨h3, h4, h5⟩ := tangent (p := p) a b c r hr e1 hP
      set ℓ := (3 * x1 ^ 2 + 2 * (a : ℚ) * x1 + b) / (2 * y1)
      have hX : (W a b c).toAffine.addX x1 x1 ℓ = ℓ ^ 2 - a - x1 - x1 := by simp [addX, W]
      have hY : (W a b c).toAffine.addY x1 x1 y1 ℓ =
          -(ℓ * ((ℓ ^ 2 - a - x1 - x1) - x1) + y1) := by
        simp only [addY, negY_W, negAddY, hX]
      rw [hY, hX]
      exact ⟨h4, h5⟩
    · rw [slope_of_X_ne hx]
      obtain ⟨h3, h4, h5⟩ := chord (p := p) a b c r hr e1 e2 hP hQ hx
      set ℓ := (y1 - y2) / (x1 - x2)
      have hX : (W a b c).toAffine.addX x1 x2 ℓ = ℓ ^ 2 - a - x1 - x2 := by simp [addX, W]
      have hY : (W a b c).toAffine.addY x1 x2 y1 ℓ =
          -(ℓ * ((ℓ ^ 2 - a - x1 - x2) - x1) + y1) := by
        simp only [addY, negY_W, negAddY, hX]
      rw [hY, hX]
      exact ⟨h4, h5⟩

lemma neg_filt (r : ℕ) (P : (W a b c).toAffine.Point) (hP : InF a b c p r P) :
    InF a b c p r (-P) ∧ tv a b c (-P) = -tv a b c P := by
  rcases P with _ | ⟨x, y, h1⟩
  · exact ⟨trivial, by simp [tv]; rfl⟩
  · simp only [Point.neg_some, InF, tv, negY_W] at hP ⊢
    exact ⟨inFilt_neg hP, by ring⟩

/-- **`t(nP) ≡ n t(P) (mod p^{3r})`.** -/
theorem nsmul_filt (r : ℕ) (hr : 1 ≤ r) (P : (W a b c).toAffine.Point) (hP : InF a b c p r P) :
    ∀ n : ℕ, InF a b c p r (n • P) ∧ PDvd p (3 * r) (tv a b c (n • P) - n * tv a b c P)
  | 0 => by simp [InF, tv, pdvd_zero]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := nsmul_filt r hr P hP n
    obtain ⟨h1, h2⟩ := add_filt a b c r hr (n • P) P ih1 hP
    rw [succ_nsmul]
    refine ⟨h1, ?_⟩
    have := h2.add ih2
    convert this using 1
    push_cast; ring

end EllNL
