import RischTragerBronstein.Mixed.KXCertBridgeC
import RischTragerBronstein.Mixed.QHeight
import RischTragerBronstein.Mixed.QPar

/-!
# Constant curves: the conjugation case with heights over `ℚ`

When the curve of the exception has constant coefficients (`θ² = A(t)`, `A ∈ ℚ[t]`), the points are
constant and their function-field heights vanish. On the twist, `D′` is a point of `E(ℚ)`
(`y² = x³ + a x + b`, `a, b ∈ ℤ`) embedded in `E(ℚ(x))` (`ιQ`); its infinite order is certified by
the logarithmic height over `ℚ` (`QHeight.certH`). With the conjugation argument
(`grp_of_chkC0`) this decides the exception when `D` and `P₊` lie in different square classes:
`kxChkCK`, `grp_of_chkCK`.
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

/-- `p` is the constant `p.headD 0`. -/
def isConstB (p : CPoly ℚ) : Bool := p.tail.all (· == 0)

lemma toPoly_of_isConstB {p : CPoly ℚ} (h : isConstB p = true) :
    CPoly.toPoly p = Polynomial.C (p.headD 0) := by
  rcases p with _ | ⟨c, t⟩
  · simp [CPoly.toPoly]
  · have ht : CPoly.toPoly t = 0 := by
      rw [← CPoly.isZero_iff]
      simp only [isConstB, List.tail_cons, List.all_eq_true, beq_iff_eq] at h
      simpa [CPoly.isZero, List.all_eq_true] using h
    simp [CPoly.toPoly_cons, ht]

/-- The curve over `ℚ(x)` is the base change of the curve over `ℚ`. -/
lemma qW_baseChange (a b : ℤ) :
    ((QHeight.qW a b).toAffine⁄(RatFunc ℚ)) =
      (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine := by
  simp [QHeight.qW, shortW, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    RatFunc.algebraMap_C]

/-- **The embedding** `E(ℚ) → E(ℚ(x))`. -/
noncomputable def ιQ (a b : ℤ) :
    (QHeight.qW a b).toAffine.Point →+
      (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine.Point :=
  have hself : (QHeight.qW a b).toAffine = ((QHeight.qW a b).toAffine⁄ℚ) := by
    simp [QHeight.qW, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  (castHom (qW_baseChange a b)).comp
    ((Point.map (W' := (QHeight.qW a b).toAffine) (Algebra.ofId ℚ (RatFunc ℚ))).comp
      (castHom hself))

lemma ιQ_injective (a b : ℤ) : Function.Injective (ιQ a b) :=
  (castHom_injective _).comp ((Point.map_injective _).comp (castHom_injective _))

lemma ιQ_some (a b : ℤ) (x y : ℚ) (h : (QHeight.qW a b).toAffine.Nonsingular x y) :
    ∃ h', ιQ a b (Point.some x y h) =
      Point.some (algebraMap ℚ (RatFunc ℚ) x) (algebraMap ℚ (RatFunc ℚ) y) h' := by
  unfold ιQ
  simp only [AddMonoidHom.comp_apply]
  erw [castHom_some]
  refine ⟨?w, ?e⟩
  case e => rfl
  case w =>
    have hW : (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine =
        (QHeight.qW a b).toAffine.map (algebraMap ℚ (RatFunc ℚ)) := by rw [← qW_baseChange]; rfl
    rw [hW]
    exact (Affine.map_nonsingular (W := (QHeight.qW a b).toAffine)
      (algebraMap ℚ (RatFunc ℚ)).injective x y).mpr h

/-- **Constant points of infinite order.** A point of `E(ℚ(x))` with constant coordinates
`(x₀, y₀)` whose `ℚ`-height certificate passes has infinite order. -/
theorem nontors_const (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (k : ℕ) (fx fy : Fr ℚ)
    (hx1 : isConstB fx.1 = true) (hx2 : isConstB fx.2 = true) (hy1 : isConstB fy.1 = true)
    (hy2 : isConstB fy.2 = true)
    (hc : QHeight.certH a b k (fx.1.headD 0 / fx.2.headD 0) = true)
    (A B : ℚ[X]) (hA : A = Polynomial.C (a : ℚ)) (hB : B = Polynomial.C (b : ℚ))
    (PD : (shortW A B).toAffine.Point)
    (hR : Rel _ _ (some (fx, fy)) PD) (n : ℤ) (hn : n • PD = 0) : n = 0 := by
  subst hA hB
  rcases PD with _ | ⟨X, Y, hXY⟩
  · exact absurd hR (by simp [Rel])
  obtain ⟨ox, oy, hX, hY⟩ := hR
  set x0 := fx.1.headD 0 / fx.2.headD 0
  set y0 := fy.1.headD 0 / fy.2.headD 0
  have hval : ∀ f : Fr ℚ, isConstB f.1 = true → isConstB f.2 = true →
      Fr.val f = algebraMap ℚ (RatFunc ℚ) (f.1.headD 0 / f.2.headD 0) := by
    intro f h1 h2
    simp only [Fr.val, toPoly_of_isConstB h1, toPoly_of_isConstB h2, RatFunc.algebraMap_C,
      map_div₀]
    simp only [eq_ratCast]
  have eX : X = algebraMap ℚ (RatFunc ℚ) x0 := by rw [← hX]; exact hval fx hx1 hx2
  have eY : Y = algebraMap ℚ (RatFunc ℚ) y0 := by rw [← hY]; exact hval fy hy1 hy2
  subst eX eY
  have hW : (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine =
      (QHeight.qW a b).toAffine.map (algebraMap ℚ (RatFunc ℚ)) := by
    rw [← qW_baseChange]; rfl
  have h0 : (QHeight.qW a b).toAffine.Nonsingular x0 y0 := by
    have := hXY
    rw [hW] at this
    exact (Affine.map_nonsingular (W := (QHeight.qW a b).toAffine)
      (algebraMap ℚ (RatFunc ℚ)).injective x0 y0).mp this
  obtain ⟨h1, e1⟩ := ιQ_some a b x0 y0 h0
  have hP : Point.some (algebraMap ℚ (RatFunc ℚ) x0) (algebraMap ℚ (RatFunc ℚ) y0) hXY =
      ιQ a b (Point.some x0 y0 h0) := by rw [e1]
  rw [hP, ← map_zsmul] at hn
  have := ιQ_injective a b (hn.trans (map_zero _).symm)
  exact QHeight.nontors_of_certH a b hΔ k x0 y0 h0 hc n this

/-- **Constant points come from `E(ℚ)`.** -/
theorem const_point (a b : ℤ) (fx fy : Fr ℚ)
    (hx1 : isConstB fx.1 = true) (hx2 : isConstB fx.2 = true) (hy1 : isConstB fy.1 = true)
    (hy2 : isConstB fy.2 = true)
    (A B : ℚ[X]) (hA : A = Polynomial.C (a : ℚ)) (hB : B = Polynomial.C (b : ℚ))
    (PD : (shortW A B).toAffine.Point) (hR : Rel _ _ (some (fx, fy)) PD) :
    ∃ h0 : (QHeight.qW a b).toAffine.Nonsingular (fx.1.headD 0 / fx.2.headD 0)
      (fy.1.headD 0 / fy.2.headD 0),
      castHom (by rw [hA, hB]) PD = ιQ a b (Point.some _ _ h0) := by
  subst hA hB
  rcases PD with _ | ⟨X, Y, hXY⟩
  · exact absurd hR (by simp [Rel])
  obtain ⟨ox, oy, hX, hY⟩ := hR
  have hval : ∀ f : Fr ℚ, isConstB f.1 = true → isConstB f.2 = true →
      Fr.val f = algebraMap ℚ (RatFunc ℚ) (f.1.headD 0 / f.2.headD 0) := by
    intro f h1 h2
    simp only [Fr.val, toPoly_of_isConstB h1, toPoly_of_isConstB h2, RatFunc.algebraMap_C,
      map_div₀]
    simp only [eq_ratCast]
  have eX : X = algebraMap ℚ (RatFunc ℚ) (fx.1.headD 0 / fx.2.headD 0) := by
    rw [← hX]; exact hval fx hx1 hx2
  have eY : Y = algebraMap ℚ (RatFunc ℚ) (fy.1.headD 0 / fy.2.headD 0) := by
    rw [← hY]; exact hval fy hy1 hy2
  subst eX eY
  have hW : (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine =
      (QHeight.qW a b).toAffine.map (algebraMap ℚ (RatFunc ℚ)) := by
    rw [← qW_baseChange]; rfl
  have h0 : (QHeight.qW a b).toAffine.Nonsingular (fx.1.headD 0 / fx.2.headD 0)
      (fy.1.headD 0 / fy.2.headD 0) := by
    have := hXY
    rw [hW] at this
    exact (Affine.map_nonsingular (W := (QHeight.qW a b).toAffine)
      (algebraMap ℚ (RatFunc ℚ)).injective _ _).mp this
  obtain ⟨h1, e1⟩ := ιQ_some a b _ _ h0
  refine ⟨h0, ?_⟩
  rw [e1]
  rfl

/-- **Two constant points with a passing `ℚ`-certificate are independent.** -/
theorem indep_const (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (k : ℕ) (fx fy gx gy : Fr ℚ)
    (hx1 : isConstB fx.1 = true) (hx2 : isConstB fx.2 = true) (hy1 : isConstB fy.1 = true)
    (hy2 : isConstB fy.2 = true) (gx1 : isConstB gx.1 = true) (gx2 : isConstB gx.2 = true)
    (gy1 : isConstB gy.1 = true) (gy2 : isConstB gy.2 = true)
    (hc : QHeight.certG a b k (fx.1.headD 0 / fx.2.headD 0) (fy.1.headD 0 / fy.2.headD 0)
      (gx.1.headD 0 / gx.2.headD 0) (gy.1.headD 0 / gy.2.headD 0) = true)
    (A B : ℚ[X]) (hA : A = Polynomial.C (a : ℚ)) (hB : B = Polynomial.C (b : ℚ))
    (PD PZ : (shortW A B).toAffine.Point) (hRD : Rel _ _ (some (fx, fy)) PD)
    (hRZ : Rel _ _ (some (gx, gy)) PZ) (m n : ℤ) (hrel : m • PD = n • PZ) : m = 0 ∧ n = 0 := by
  obtain ⟨h1, e1⟩ := const_point a b fx fy hx1 hx2 hy1 hy2 A B hA hB PD hRD
  obtain ⟨h2, e2⟩ := const_point a b gx gy gx1 gx2 gy1 gy2 A B hA hB PZ hRZ
  have := congrArg (castHom (by rw [hA, hB] : (shortW A B).toAffine =
    (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine)) hrel
  rw [map_zsmul, map_zsmul, e1, e2, ← map_zsmul, ← map_zsmul] at this
  exact QHeight.indepQ_of_certG a b hΔ k _ _ _ _ h1 h2 hc m n (ιQ_injective a b this)

end FFHeight

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight NFEmbed

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- Normalized coordinates (`Fr.norm`). -/
def normPt : PtC ℚ → PtC ℚ
  | none => none
  | some (fx, fy) => some (Fr.norm fx, Fr.norm fy)

lemma rel_normPt {A B : ℚ[X]} {p : PtC ℚ} {P : (shortW A B).toAffine.Point} (h : Rel A B p P) :
    Rel A B (normPt p) P := by
  rcases p with _ | ⟨fx, fy⟩ <;> rcases P with _ | ⟨x, y, hxy⟩
  · exact h
  · exact absurd h (by simp [FFHeight.Rel])
  · exact absurd h (by simp [FFHeight.Rel])
  · obtain ⟨ox, oy, hX, hY⟩ := h
    exact ⟨Fr.ok_norm ox, Fr.ok_norm oy, by rw [Fr.val_norm ox, hX], by rw [Fr.val_norm oy, hY]⟩

section ChkCK

variable (Fc ks) [Fact (Irreducible (toPoly (fKc Fc)))]
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (κ : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk kc : ℕ) (a b : ℤ)

/-- **The check for constant curves, different classes**: `kxChkC0`, the integer constant model
`y² = x³ + a x + b`, a constant `D′`, and its height certificate over `ℚ`. -/
def kxChkCK : Bool :=
  kxChkC0 Fc ks c0f g A B kt l cs z κ uF Ac Bc kc && Ac == [(a : ℚ)] && Bc == [(b : ℚ)] &&
  4 * a ^ 3 + 27 * b ^ 2 != 0 &&
  match normPt (ptDT Fc ks c0f g A B kt l cs uF Ac kc) with
  | some (fx, fy) => isConstB fx.1 && isConstB fx.2 && isConstB fy.1 && isConstB fy.2 &&
      QHeight.certH a b kk (fx.1.headD 0 / fx.2.headD 0)
  | none => false

/-- **The check for constant curves, same class**: `kxChkT0`, the integer constant model, constant
`D′`, `P₊′` on the twist and their two-point height certificate over `ℚ`. -/
def kxChkTK (c : ℚ) : Bool :=
  kxChkT0 Fc ks c0f g A B kt l cs z c uF Ac Bc kc && Ac == [(a : ℚ)] && Bc == [(b : ℚ)] &&
  4 * a ^ 3 + 27 * b ^ 2 != 0 &&
  match normPt (ptDT Fc ks c0f g A B kt l cs uF Ac kc),
    normPt (ptZT Fc ks c0f g A B kt l cs z c uF kc) with
  | some (fx, fy), some (gx, gy) => isConstB fx.1 && isConstB fx.2 && isConstB fy.1 &&
      isConstB fy.2 && isConstB gx.1 && isConstB gx.2 && isConstB gy.1 && isConstB gy.2 &&
      QHeight.certG a b kk (fx.1.headD 0 / fx.2.headD 0) (fy.1.headD 0 / fy.2.headD 0)
        (gx.1.headD 0 / gx.2.headD 0) (gy.1.headD 0 / gy.2.headD 0)
  | _, _ => false

end ChkCK

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (κ : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk : ℕ) (a b : ℤ)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The group condition for constant curves, different classes.** -/
theorem grp_of_chkCK (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    [Fact (¬ IsSquare (sT Fc ks g A B kt l cs k * κ))]
    (hchk : kxChkCK Fc ks c0f g A B kt l cs z κ uF Ac Bc kk k a b = true)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero)) :
    let cC : ℕ → T.F 0 := (fun i ↦ (GPoly.toPoly (T.MP 0 h0) A).coeff i)
    let xC : Fin cs.length → T.F 0 := (fun q ↦ (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
    let βC : Fin cs.length → T.F 0 := (fun q ↦
      ((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
        ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
          (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkCK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨hchk0, hAc⟩, hBc⟩, hΔ⟩, hpt⟩ := hchk
  have hA : CPoly.toPoly Ac = Polynomial.C (a : ℚ) := by rw [hAc]; simp [CPoly.toPoly]
  have hB : CPoly.toPoly Bc = Polynomial.C (b : ℚ) := by rw [hBc]; simp [CPoly.toPoly]
  refine T.grp_of_chkC0 c0f g A B kt l cs z κ uF Ac Bc hFc h0 k hchk0 (fun PD hR0 n hn ↦ ?_)
    rtsF hrl hrs b₀ hb₀
  have hR := rel_normPt hR0
  split at hpt
  · rename_i fx fy hptd
    rw [hptd] at hR
    simp only [Bool.and_eq_true] at hpt
    obtain ⟨⟨⟨⟨hx1, hx2⟩, hy1⟩, hy2⟩, hc⟩ := hpt
    exact nontors_const a b hΔ kk fx fy hx1 hx2 hy1 hy2 hc _ _ hA hB PD hR n hn
  · exact absurd hpt (by decide)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The group condition for constant curves, same class.** -/
theorem grp_of_chkTK (c : ℚ) (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChkTK Fc ks c0f g A B kt l cs z uF Ac Bc kk k a b c = true)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero)) :
    let cC : ℕ → T.F 0 := (fun i ↦ (GPoly.toPoly (T.MP 0 h0) A).coeff i)
    let xC : Fin cs.length → T.F 0 := (fun q ↦ (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
    let βC : Fin cs.length → T.F 0 := (fun q ↦
      ((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
        ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
          (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkTK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨hchk0, hAc⟩, hBc⟩, hΔ⟩, hpt⟩ := hchk
  have hA : CPoly.toPoly Ac = Polynomial.C (a : ℚ) := by rw [hAc]; simp [CPoly.toPoly]
  have hB : CPoly.toPoly Bc = Polynomial.C (b : ℚ) := by rw [hBc]; simp [CPoly.toPoly]
  refine T.grp_of_chkT0 c0f g A B kt l cs z c uF Ac Bc hFc h0 k hchk0
    (fun PD PZ hRD0 hRZ0 m n h ↦ ?_) rtsF hrl hrs b₀ hb₀
  have hRD := rel_normPt hRD0
  have hRZ := rel_normPt hRZ0
  split at hpt
  · rename_i fx fy gx gy hD hZ
    rw [hD] at hRD; rw [hZ] at hRZ
    simp only [Bool.and_eq_true] at hpt
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hx1, hx2⟩, hy1⟩, hy2⟩, gx1⟩, gx2⟩, gy1⟩, gy2⟩, hc⟩ := hpt
    exact indep_const a b hΔ kk fx fy gx gy hx1 hx2 hy1 hy2 gx1 gx2 gy1 gy2 hc _ _ hA hB PD PZ
      hRD hRZ m n h
  · exact absurd hpt (by decide)

end MTower

end Curves.MT
