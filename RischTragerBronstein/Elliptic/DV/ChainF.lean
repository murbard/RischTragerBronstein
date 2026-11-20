import RischTragerBronstein.Elliptic.DV.Chain

/-!
# Verified point arithmetic over a computable field

For a computable field `F` of characteristic zero (e.g. `QuadraticAlgebra ℚ d 0 = ℚ(√d)`),
`addPtF`/`mulPtF` compute the chord–tangent law on `y² = x³ + ax² + bx + c` directly in `F`;
`addPtF_spec`/`mulPtF_spec` identify them with Mathlib's group law. With an embedding
`F →ₐ[ℚ] ℚ_p`, `torsionTestF_spec` decides whether a point of `E(F)` has finite order.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace EllDV

open scoped Classical

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-- The chord–tangent sum over `F`. -/
def addPtF (a b _c : ℤ) : Option (F × F) → Option (F × F) → Option (F × F)
  | none, Q => Q
  | P, none => P
  | some (x1, y1), some (x2, y2) =>
    if x1 = x2 then
      if y1 = -y2 then none
      else
        let lam := (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1)
        let x3 := lam ^ 2 - a - x1 - x2
        some (x3, -(lam * (x3 - x1) + y1))
    else
      let lam := (y1 - y2) / (x1 - x2)
      let x3 := lam ^ 2 - a - x1 - x2
      some (x3, -(lam * (x3 - x1) + y1))

/-- `k • P`. -/
def mulPtF (a b c : ℤ) (P : Option (F × F)) : ℕ → Option (F × F)
  | 0 => none
  | k + 1 => addPtF a b c (mulPtF a b c P k) P

variable (a b c : ℤ)

/-- The representation relation. -/
def RepF (o : Option (F × F)) (P : (W F a b c).toAffine.Point) : Prop :=
  match o with
  | none => P = 0
  | some (x, y) => ∃ h, P = Point.some x y h

lemma some_congrF {x y x' y' : F} {h : (W F a b c).toAffine.Nonsingular x y}
    {h' : (W F a b c).toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx; subst hy; rfl

set_option maxHeartbeats 800000 in
theorem addPtF_spec {o₁ o₂ : Option (F × F)} {P₁ P₂ : (W F a b c).toAffine.Point}
    (h₁ : RepF a b c o₁ P₁) (h₂ : RepF a b c o₂ P₂) : RepF a b c (addPtF a b c o₁ o₂) (P₁ + P₂) := by
  rcases o₁ with _ | ⟨x1, y1⟩ <;> rcases o₂ with _ | ⟨x2, y2⟩
  · simp only [RepF, addPtF] at h₁ h₂ ⊢; subst h₁; subst h₂; rfl
  · simp only [RepF, addPtF] at h₁ h₂ ⊢
    subst h₁; obtain ⟨h, rfl⟩ := h₂; exact ⟨h, rfl⟩
  · simp only [RepF, addPtF] at h₁ h₂ ⊢
    subst h₂; obtain ⟨h, rfl⟩ := h₁; exact ⟨h, rfl⟩
  obtain ⟨hn1, rfl⟩ := h₁
  obtain ⟨hn2, rfl⟩ := h₂
  have e1 := (equation_W a b c).mp hn1.1
  have e2 := (equation_W a b c).mp hn2.1
  unfold OnCurve at e1 e2
  have hnegY : ∀ u v : F, (W F a b c).toAffine.negY u v = -v := fun u v ↦ negY_W a b c u v
  have hX : ∀ u v L : F, (W F a b c).toAffine.addX u v L = L ^ 2 - a - u - v := by
    intro u v L; simp [addX, W, W0]
  have hY : ∀ u v w L : F, (W F a b c).toAffine.addY u v w L =
      -(L * ((L ^ 2 - a - u - v) - u) + w) := by
    intro u v w L; simp only [addY, negAddY, hX, hnegY]
  have ha₁ : (W F a b c).toAffine.a₁ = 0 := by simp [W, W0, WeierstrassCurve.baseChange,
    WeierstrassCurve.map]
  have ha₂ : (W F a b c).toAffine.a₂ = (a : F) := by simp [W, W0, WeierstrassCurve.baseChange,
    WeierstrassCurve.map]
  have ha₄ : (W F a b c).toAffine.a₄ = (b : F) := by simp [W, W0, WeierstrassCurve.baseChange,
    WeierstrassCurve.map]
  simp only [addPtF]
  by_cases hx : x1 = x2
  · rw [if_pos hx]
    by_cases hy : y1 = -y2
    · rw [if_pos hy]
      simp only [RepF]
      exact Point.add_of_Y_eq hx (by rw [hy, hnegY])
    · rw [if_neg hy]
      have hyy : y1 = y2 := by
        have : (y1 - y2) * (y1 + y2) = 0 := by rw [← hx] at e2; linear_combination e1 - e2
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd (by linear_combination h) hy
      have h2y : (2 : F) * y1 ≠ 0 := by
        intro h0
        have : y1 = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · norm_num at h
          · exact h
        apply hy; rw [← hyy, this, neg_zero]
      have hxy : ¬(x1 = x2 ∧ y1 = (W F a b c).toAffine.negY x2 y2) := by
        rintro ⟨-, h⟩; rw [hnegY] at h; exact hy h
      have hsl : (W F a b c).toAffine.slope x1 x2 y1 y2 = (3 * x1 ^ 2 + 2 * a * x1 + b) / (2 * y1) := by
        rw [slope_of_Y_ne hx (by rw [hnegY]; exact hy), ha₁, ha₂, ha₄, hnegY]
        congr 1 <;> ring
      refine ⟨by rw [← hY, ← hX, ← hsl]; exact nonsingular_add hn1 hn2 hxy, ?_⟩
      rw [Point.add_some hxy]
      exact some_congrF a b c (by rw [hX, hsl]) (by rw [hY, hsl])
  · rw [if_neg hx]
    have hxy : ¬(x1 = x2 ∧ y1 = (W F a b c).toAffine.negY x2 y2) := fun h ↦ hx h.1
    have hsl : (W F a b c).toAffine.slope x1 x2 y1 y2 = (y1 - y2) / (x1 - x2) := slope_of_X_ne hx
    refine ⟨by rw [← hY, ← hX, ← hsl]; exact nonsingular_add hn1 hn2 hxy, ?_⟩
    rw [Point.add_some hxy]
    exact some_congrF a b c (by rw [hX, hsl]) (by rw [hY, hsl])

theorem mulPtF_spec {o : Option (F × F)} {P : (W F a b c).toAffine.Point} (h : RepF a b c o P) :
    ∀ k : ℕ, RepF a b c (mulPtF a b c o k) (k • P)
  | 0 => by simp only [mulPtF, RepF]; exact zero_nsmul P
  | k + 1 => by rw [succ_nsmul]; exact addPtF_spec a b c (mulPtF_spec h k) h

/-- The torsion test over `F`. -/
def torsionTestF (a b c : ℤ) (o : Option (F × F)) (N : ℕ) : Bool :=
  (List.range N).any fun k ↦ (mulPtF a b c o (k + 1)).isNone

/-- **The torsion test over a field embedded in `ℚ_p` decides.** -/
theorem torsionTestF_spec {p : ℕ} [Fact p.Prime] (φ : F →ₐ[ℚ] ℚ_[p]) (hp2 : p ≠ 2)
    (hgood : goodRedMod p a b c) {o : Option (F × F)} {P : (W F a b c).toAffine.Point}
    (h : RepF a b c o P) (N : ℕ) (hN : Fintype.card (Option (RedPts p a b c)) ≤ N) :
    torsionTestF a b c o N = true ↔ IsOfFinAddOrder P := by
  constructor
  · intro ht
    simp only [torsionTestF, List.any_eq_true, List.mem_range] at ht
    obtain ⟨k, -, hk⟩ := ht
    have hr := mulPtF_spec a b c h (k + 1)
    rcases hm : mulPtF a b c o (k + 1) with _ | ⟨x, y⟩
    · rw [hm] at hr
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k + 1, k.succ_pos, hr⟩
    · rw [hm] at hk; simp at hk
  · intro ht
    have hb := torsion_order_le_field a b c φ hp2 hgood P ht
    have hpos := ht.addOrderOf_pos
    simp only [torsionTestF, List.any_eq_true, List.mem_range]
    refine ⟨addOrderOf P - 1, by omega, ?_⟩
    have hr := mulPtF_spec a b c h (addOrderOf P - 1 + 1)
    rw [Nat.sub_add_cancel hpos, addOrderOf_nsmul_eq_zero] at hr
    rw [Nat.sub_add_cancel hpos]
    rcases hm : mulPtF a b c o (addOrderOf P) with _ | ⟨x, y⟩
    · rfl
    · rw [hm] at hr
      obtain ⟨h', hh⟩ := hr
      exact absurd hh.symm (by simp)

end EllDV
