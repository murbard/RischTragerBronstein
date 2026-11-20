import RischTragerBronstein.Elliptic.DV.Kernel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# A torsion bound over `ℚ_p` by reduction

For `y² = x³ + ax² + bx + c` over `ℚ_p`, `p` odd with good reduction: torsion points are integral
(`torsion_integral`), reduction is injective on torsion points (`red_inj`: the kernel lemma
`kernel_big` and the torsion-freeness of the kernel `torsion_integral_y`), hence
`addOrderOf P ≤ #(Option Ẽ(𝔽_p))` (`torsion_order_le`). For a number field `K ↪ ℚ_p` this bounds
the order of every torsion point of `E(K)`.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllDV

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime] (a b c : ℤ)

/-- The affine points of the reduced curve. -/
def RedPts (p : ℕ) (a b c : ℤ) : Type :=
  {st : ZMod p × ZMod p // st.2 ^ 2 = st.1 ^ 3 + a * st.1 ^ 2 + b * st.1 + c}

noncomputable instance : Fintype (RedPts p a b c) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold RedPts; infer_instance

lemma norm_cubic_big {x : ℚ_[p]} (hx : 1 < ‖x‖) :
    ‖x ^ 3 + a * x ^ 2 + b * x + c‖ = ‖x‖ ^ 3 := by
  have hr : ‖(a : ℚ_[p]) * x ^ 2 + b * x + c‖ ≤ ‖x‖ ^ 2 := by
    refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans
      (max_le ?_ ?_)) ?_)
    · rw [norm_mul, norm_pow]; nlinarith [nint (p := p) a, norm_nonneg x]
    · rw [norm_mul]; nlinarith [nint (p := p) b, norm_nonneg x]
    · nlinarith [nint (p := p) c]
  have h3 : ‖x ^ 3‖ = ‖x‖ ^ 3 := norm_pow _ _
  have hlt : ‖(a : ℚ_[p]) * x ^ 2 + b * x + c‖ < ‖x ^ 3‖ := by
    rw [h3]
    have : ‖x‖ ^ 2 < ‖x‖ ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
    linarith
  rw [show x ^ 3 + a * x ^ 2 + b * x + c = x ^ 3 + (a * x ^ 2 + b * x + c) by ring,
    Padic.add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le, h3]

/-- **Torsion points are integral.** -/
theorem torsion_integral {x y : ℚ_[p]} (h : (W ℚ_[p] a b c).toAffine.Nonsingular x y)
    (ht : IsOfFinAddOrder (Point.some x y h)) : ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 := by
  have e := (equation_W a b c).mp h.1
  unfold OnCurve at e
  have hy : ‖y‖ ≤ 1 := by
    by_cases hy0 : y = 0
    · rw [hy0, norm_zero]; exact zero_le_one
    have hv := torsion_integral_y (padicDVal p) a b c hp.out h ht hy0
    rw [Padic.norm_eq_zpow_neg_valuation hy0]
    exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le)
      (by simp only [padicDVal] at hv; omega)
  refine ⟨?_, hy⟩
  by_contra hx
  push_neg at hx
  have := norm_cubic_big a b c hx
  rw [← e, norm_pow] at this
  have h1 : 1 < ‖x‖ ^ 3 := one_lt_pow₀ hx (by norm_num)
  have h2 : ‖y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg y) hy
  linarith

/-- The reduction of a point (junk `none` for non-integral points). -/
noncomputable def red : (W ℚ_[p] a b c).toAffine.Point → Option (ZMod p × ZMod p)
  | .zero => none
  | .some x y _ =>
    if hx : ‖x‖ ≤ 1 then if hy : ‖y‖ ≤ 1 then
      some (PadicInt.toZMod ⟨x, hx⟩, PadicInt.toZMod ⟨y, hy⟩) else none else none

lemma small_of_toZMod_eq {x₁ x₂ : ℚ_[p]} (h₁ : ‖x₁‖ ≤ 1) (h₂ : ‖x₂‖ ≤ 1)
    (h : PadicInt.toZMod (⟨x₁, h₁⟩ : ℤ_[p]) = PadicInt.toZMod ⟨x₂, h₂⟩) : ‖x₁ - x₂‖ < 1 := by
  let A : ℤ_[p] := ⟨x₁, h₁⟩
  let B : ℤ_[p] := ⟨x₂, h₂⟩
  have hk : A - B ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
    rw [RingHom.mem_ker, map_sub]; exact sub_eq_zero.mpr h
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hk
  exact hk

/-- **Reduction is injective on torsion points.** -/
theorem red_inj (hp2 : p ≠ 2) (hgood : GoodRed p a b c) {P Q : (W ℚ_[p] a b c).toAffine.Point}
    (hP : IsOfFinAddOrder P) (hQ : IsOfFinAddOrder Q) (h : red a b c P = red a b c Q) : P = Q := by
  rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
  · rfl
  · obtain ⟨hx2, hy2⟩ := torsion_integral a b c h2 hQ
    simp [red, hx2, hy2] at h
  · obtain ⟨hx1, hy1⟩ := torsion_integral a b c h1 hP
    simp [red, hx1, hy1] at h
  · obtain ⟨hx1, hy1⟩ := torsion_integral a b c h1 hP
    obtain ⟨hx2, hy2⟩ := torsion_integral a b c h2 hQ
    simp only [red, hx1, hy1, hx2, hy2, dif_pos, Option.some.injEq, Prod.mk.injEq] at h
    by_contra hne
    obtain ⟨x3, y3, h3, hsub, hbig⟩ := kernel_big a b c hp2 hgood h1 h2 hx1 hy1 hx2 hy2
      (small_of_toZMod_eq hx1 hx2 h.1) (small_of_toZMod_eq hy1 hy2 h.2) hne
    have ht : IsOfFinAddOrder (Point.some x3 y3 h3) := by
      rw [← hsub, sub_eq_add_neg]; exact hP.add hQ.neg
    have := (torsion_integral a b c h3 ht).1
    linarith

lemma toZMod_curve {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (e : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) :
    (PadicInt.toZMod (⟨y, hy⟩ : ℤ_[p])) ^ 2 = (PadicInt.toZMod (⟨x, hx⟩ : ℤ_[p])) ^ 3 +
      a * (PadicInt.toZMod (⟨x, hx⟩ : ℤ_[p])) ^ 2 + b * PadicInt.toZMod (⟨x, hx⟩ : ℤ_[p]) + c := by
  set X : ℤ_[p] := ⟨x, hx⟩
  set Y : ℤ_[p] := ⟨y, hy⟩
  have e' : Y ^ 2 = X ^ 3 + (a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * X + (c : ℤ_[p]) := by
    apply Subtype.ext
    simp only [X, Y, PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_intCast]
    exact e
  have := congrArg PadicInt.toZMod e'
  simpa only [map_pow, map_add, map_mul, map_intCast] using this

/-- The reduction of a torsion point lies on the reduced curve. -/
noncomputable def redPt (P : (W ℚ_[p] a b c).toAffine.Point) : Option (RedPts p a b c) :=
  match P with
  | .zero => none
  | .some x y h =>
    if hxy : ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 then
      some ⟨(PadicInt.toZMod ⟨x, hxy.1⟩, PadicInt.toZMod ⟨y, hxy.2⟩),
        toZMod_curve a b c hxy.1 hxy.2 ((equation_W a b c).mp h.1)⟩
    else none

lemma redPt_eq {P Q : (W ℚ_[p] a b c).toAffine.Point} (hP : IsOfFinAddOrder P)
    (hQ : IsOfFinAddOrder Q) (h : redPt a b c P = redPt a b c Q) : red a b c P = red a b c Q := by
  rcases P with _ | ⟨x1, y1, h1⟩ <;> rcases Q with _ | ⟨x2, y2, h2⟩
  · rfl
  · obtain ⟨hx2, hy2⟩ := torsion_integral a b c h2 hQ
    simp [redPt, hx2, hy2] at h
  · obtain ⟨hx1, hy1⟩ := torsion_integral a b c h1 hP
    simp [redPt, hx1, hy1] at h
  · obtain ⟨hx1, hy1⟩ := torsion_integral a b c h1 hP
    obtain ⟨hx2, hy2⟩ := torsion_integral a b c h2 hQ
    simp only [redPt, hx1, hy1, hx2, hy2, and_self, dif_pos, Option.some.injEq,
      Subtype.mk.injEq] at h
    simp only [red, hx1, hy1, hx2, hy2, dif_pos]
    have h' := congrArg Subtype.val (Option.some.inj h)
    exact congrArg some h'

/-- **The torsion bound**: the order of a torsion point is at most `#Ẽ(𝔽_p) + 1`. -/
theorem torsion_order_le (hp2 : p ≠ 2) (hgood : GoodRed p a b c)
    (P : (W ℚ_[p] a b c).toAffine.Point) (ht : IsOfFinAddOrder P) :
    addOrderOf P ≤ Fintype.card (Option (RedPts p a b c)) := by
  set n := addOrderOf P
  let g : Fin n → Option (RedPts p a b c) := fun k ↦ redPt a b c ((k : ℕ) • P)
  have hg : Function.Injective g := by
    intro k j hkj
    have hk : IsOfFinAddOrder ((k : ℕ) • P) := ht.nsmul
    have hj : IsOfFinAddOrder ((j : ℕ) • P) := ht.nsmul
    have := red_inj a b c hp2 hgood hk hj (redPt_eq a b c hk hj hkj)
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf k.2 j.2 this)
  simpa using Fintype.card_le_of_injective g hg

end EllDV
