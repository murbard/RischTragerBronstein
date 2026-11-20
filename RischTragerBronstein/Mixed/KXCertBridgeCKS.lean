import RischTragerBronstein.Mixed.KXCertBridgeCS
import RischTragerBronstein.Mixed.EllConstK

/-!
# Constant curves at the levels `m + 1`: heights over `ℚ`

When the curve of the exception at a level `m + 1` has rational coefficients, the points of
interest have rational coordinates and their function-field heights over `Kₘ` vanish. As at level
`0` (`KXCertBridgeCK`), the certificate is a height certificate over `ℚ`: the coordinates of `D′`
(and `P₊′`) are checked to be rational constants (`ratOfK`, verified by equality in `Kₘ`), and
`QHeight.certH` / `certG` certify infinite order / independence (`nontors_constK`,
`indep_constK`). Checks `kxChkCKS`, `kxChkTKS`; soundness `grp_of_chkCKS`, `grp_of_chkTKS`.
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight NFEmbed

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section Rat

variable (Fc) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- A rational guess for an element of `Kₘ` (exact on rational constants). -/
def ratGuess : (m : ℕ) → KF Fc m → ℚ
  | 0, z => let c := RFC.canon (z.1.headD 0); c.1.headD 0 / c.2.headD 1
  | m + 1, z => let c := RFC.canon (K := KF Fc m) z;
      ratGuess m (c.1.headD 0) / ratGuess m (c.2.headD 1)

/-- **The rational value of an element of `Kₘ`, verified.** -/
def ratOfK (m : ℕ) (x : KF Fc m) : Option ℚ :=
  if ((ratGuess Fc m x : ℚ) : KF Fc m) = x then some (ratGuess Fc m x) else none

lemma ratOfK_spec {m : ℕ} {x : KF Fc m} {q : ℚ} (h : ratOfK Fc m x = some q) :
    ((q : ℚ) : KF Fc m) = x := by
  unfold ratOfK at h
  split_ifs at h with hq
  cases h; exact hq

/-- The rational value of a constant fraction. -/
def ratFr (m : ℕ) (f : Fr (KF Fc m)) : Option ℚ :=
  if isConstK f.1 && isConstK f.2 then ratOfK Fc m (f.1.headD 0 / f.2.headD 0) else none

lemma ratFr_spec {m : ℕ} {f : Fr (KF Fc m)} {q : ℚ} (h : ratFr Fc m f = some q) :
    Fr.val f = algebraMap ℚ (RatFunc (KF Fc m)) q := by
  unfold ratFr at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true] at hc
  exact val_of_constK f hc.1 hc.2 q (ratOfK_spec Fc h).symm

/-- Normalized coordinates over `Kₘ`. -/
def normPtK (m : ℕ) : PtC (KF Fc m) → PtC (KF Fc m)
  | none => none
  | some (fx, fy) => some (Fr.norm fx, Fr.norm fy)

lemma rel_normPtK {m : ℕ} {A B : (KF Fc m)[X]} {p : PtC (KF Fc m)}
    {P : (shortW A B).toAffine.Point} (h : Rel A B p P) : Rel A B (normPtK Fc m p) P := by
  rcases p with _ | ⟨fx, fy⟩ <;> rcases P with _ | ⟨x, y, hxy⟩
  · exact h
  · exact absurd h (by simp [FFHeight.Rel])
  · exact absurd h (by simp [FFHeight.Rel])
  · obtain ⟨ox, oy, hX, hY⟩ := h
    exact ⟨Fr.ok_norm ox, Fr.ok_norm oy, by rw [Fr.val_norm ox, hX], by rw [Fr.val_norm oy, hY]⟩

/-- The rational coordinates of a point. -/
def ptRat (m : ℕ) (p : PtC (KF Fc m)) : Option (ℚ × ℚ) :=
  match normPtK Fc m p with
  | some (fx, fy) =>
    match ratFr Fc m fx, ratFr Fc m fy with
    | some x0, some y0 => some (x0, y0)
    | _, _ => none
  | none => none

lemma ptRat_spec {m : ℕ} {p : PtC (KF Fc m)} {x0 y0 : ℚ} (h : ptRat Fc m p = some (x0, y0))
    {A B : (KF Fc m)[X]} {P : (shortW A B).toAffine.Point} (hR : Rel A B p P) :
    ∃ fx fy, Rel A B (some (fx, fy)) P ∧ Fr.val fx = algebraMap ℚ (RatFunc (KF Fc m)) x0 ∧
      Fr.val fy = algebraMap ℚ (RatFunc (KF Fc m)) y0 := by
  have hR' := rel_normPtK Fc hR
  unfold ptRat at h
  split at h
  · rename_i fx fy hn
    rw [hn] at hR'
    split at h
    · rename_i x1 y1 hx hy
      cases h
      exact ⟨fx, fy, hR', ratFr_spec Fc hx, ratFr_spec Fc hy⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end Rat

section ChkCKS

variable (Fc ks) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (kk kc : ℕ) (a b : ℤ)

/-- **Constant curves at level `m + 1`, different classes**: `kxChkC0S`, the integer model, and a
height certificate over `ℚ` for the rational point `D′`. -/
def kxChkCKS : Bool :=
  kxChkC0S Fc ks m g A B kt l cs z κ uF Ac Bc kc && Ac == [((a : ℚ) : KF Fc m)] &&
  Bc == [((b : ℚ) : KF Fc m)] && 4 * a ^ 3 + 27 * b ^ 2 != 0 &&
  match ptRat Fc m (ptDTS Fc ks m g A B kt l cs uF Ac kc) with
  | some (x0, _) => QHeight.certH a b kk x0
  | none => false

/-- **Constant curves at level `m + 1`, same class** (two-point certificate over `ℚ`). -/
def kxChkTKS (c : ℚ) : Bool :=
  kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc kc && Ac == [((a : ℚ) : KF Fc m)] &&
  Bc == [((b : ℚ) : KF Fc m)] && 4 * a ^ 3 + 27 * b ^ 2 != 0 &&
  match ptRat Fc m (ptDTS Fc ks m g A B kt l cs uF Ac kc),
    ptRat Fc m (ptZTS Fc ks m g A B kt l cs z c uF kc) with
  | some (x1, y1), some (x2, y2) => QHeight.certG a b kk x1 y1 x2 y2
  | _, _ => false

end ChkCKS

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (kk : ℕ) (a b : ℤ)

lemma toPoly_singleK (a : ℤ) : CPoly.toPoly [((a : ℚ) : KF Fc m)] = Polynomial.C ((a : KF Fc m)) := by
  simp [CPoly.toPoly]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The group condition for constant curves at level `m + 1`, different classes.** -/
theorem grp_of_chkCKS (h0 : T.Tr (m + 1)) (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    [Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs k * κ) : KF Fc m))]
    (hchk : kxChkCKS Fc ks m g A B kt l cs z κ uF Ac Bc kk k a b = true)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero)) :
    let cC : ℕ → T.F (m + 1) := (fun i ↦ (GPoly.toPoly (T.MP (m + 1) h0) A).coeff i)
    let xC : Fin cs.length → T.F (m + 1) := (fun q ↦ (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
    let βC : Fin cs.length → T.F (m + 1) := (fun q ↦
      ((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
        ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) *
          (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
          (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK
          (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkCKS, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨hchk0, hAc⟩, hBc⟩, hΔ⟩, hpt⟩ := hchk
  have hA : CPoly.toPoly Ac = Polynomial.C (a : KF Fc m) := by rw [hAc]; exact toPoly_singleK m a
  have hB : CPoly.toPoly Bc = Polynomial.C (b : KF Fc m) := by rw [hBc]; exact toPoly_singleK m b
  refine T.grp_of_chkC0S m g A B kt l cs z κ uF Ac Bc h0 k hchk0 (fun PD hR0 n hn ↦ ?_)
    rtsF hrl hrs b₀ hb₀
  split at hpt
  · rename_i x0 y0 hp
    obtain ⟨fx, fy, hR, hx, hy⟩ := ptRat_spec Fc hp hR0
    exact nontors_constK a b hΔ kk fx fy x0 y0 hx hy hpt _ _ hA hB PD hR n hn
  · exact absurd hpt (by decide)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The group condition for constant curves at level `m + 1`, same class.** -/
theorem grp_of_chkTKS (c : ℚ) (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkTKS Fc ks m g A B kt l cs z uF Ac Bc kk k a b c = true)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero)) :
    let cC : ℕ → T.F (m + 1) := (fun i ↦ (GPoly.toPoly (T.MP (m + 1) h0) A).coeff i)
    let xC : Fin cs.length → T.F (m + 1) := (fun q ↦ (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
    let βC : Fin cs.length → T.F (m + 1) := (fun q ↦
      ((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
        ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) *
          (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
          (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK
          (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkTKS, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨hchk0, hAc⟩, hBc⟩, hΔ⟩, hpt⟩ := hchk
  have hA : CPoly.toPoly Ac = Polynomial.C (a : KF Fc m) := by rw [hAc]; exact toPoly_singleK m a
  have hB : CPoly.toPoly Bc = Polynomial.C (b : KF Fc m) := by rw [hBc]; exact toPoly_singleK m b
  refine T.grp_of_chkT0S m g A B kt l cs z c uF Ac Bc h0 k hchk0
    (fun PD PZ hRD0 hRZ0 m' n h ↦ ?_) rtsF hrl hrs b₀ hb₀
  split at hpt
  · rename_i x1 y1 x2 y2 hD hZ
    obtain ⟨fx, fy, hRD, hx1, hy1⟩ := ptRat_spec Fc hD hRD0
    obtain ⟨gx, gy, hRZ, hx2, hy2⟩ := ptRat_spec Fc hZ hRZ0
    exact indep_constK a b hΔ kk fx fy gx gy x1 y1 x2 y2 hx1 hy1 hx2 hy2 hpt _ _ hA hB PD PZ
      hRD hRZ m' n h
  · exact absurd hpt (by decide)

end MTower

end Curves.MT
