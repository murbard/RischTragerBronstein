import RischTragerBronstein.Mixed.KXConstCompleteS
import RischTragerBronstein.Mixed.KXConstSearch

/-!
# The level-`m + 1` constant-curve searches answer

`kxMWSearchCKS_of` / `kxMWSearchTKS_of`: for a curve with rational coefficients `r` over a linear
base, the searches `kxMWSearchCKS` / `kxMWSearchTKS` succeed for every large `kmax`, at the rational
scaling `lcm(den a₁, den b₁)` of `mwScalesS`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)


lemma headRat_cast (p : CPoly (KF Fc m)) (x : ℚ) (h : p.headD 0 = ((x : ℚ) : KF Fc m)) :
    headRat Fc m p = x := by
  unfold headRat; rw [h, ratOfK_ratCast]; rfl

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The level-`m + 1` constant-curve search (different classes) succeeds** for large `kmax`. -/
theorem kxMWSearchCKS_of (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]]) (h0 : T.Tr (m + 1))
    (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
    (z : LC (m + 1)) (hz : kxZ Fc ks lv (m + 1) A = some z)
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hδ : ¬ IsSquare (sTS Fc ks m g A B kt l cs k * kxKap Fc ks (m + 1) A z))
    (hA4 : ∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true)
    (hBok : ∀ b ∈ B, okS (Fc := Fc) m b = true)
    (hcs : ∀ q < cs.length, okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) = true)
    (hD : ∀ q < cs.length, okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val (m + 1) (aCS Fc ks m A i) = (r i : T.F (m + 1)))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0)
    (hκ : kxKap Fc ks (m + 1) A z ≠ 0) (hs : sTS Fc ks m g A B kt l cs k ≠ 0)
    (hzκ : T.val (m + 1) z ^ 2 * T.val (m + 1) (aCS Fc ks m A 0) =
      (kxKap Fc ks (m + 1) A z : T.F (m + 1)))
    (hmG : mGS Fc ks m g A B kt l cs k ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
          ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) * (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
            (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * b₀))
    (hntF : ∀ n : ℤ, n • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
        (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) = 0 →
        n = 0) :
    ∃ K0, ∀ kmax, K0 ≤ kmax → kxMWSearchCKS Fc ks lv m g A B kt l cs kmax = true := by
  set κ := kxKap Fc ks (m + 1) A z with hκdef
  set s := sTS Fc ks m g A B kt l cs k with hsdef
  set z' := normC Fc (m + 1) z with hz'
  have hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i) := fun i hi ↦
    ⟨okS_spec (Fc := Fc) (hA4 i hi), T.frval_of_ratS m h0 _ (r i) (hr i hi)⟩
  set a1 := headRat Fc m (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m)
    (AFrS Fc ks m A (Fr.ofPoly [(1 : KF Fc m)])))) with ha1
  set b1 := headRat Fc m (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m)
    (BFrS Fc ks m A (Fr.ofPoly [(1 : KF Fc m)])))) with hb1
  have ha1v : a1 = s ^ 2 * (1 * 1 * (1 * 1) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) :=
    headRat_cast m _ _ (AcS_head Fc ks m A r hcF s _ 1 constFrS_one)
  have hb1v : b1 = s ^ 3 * (1 * 1 * (1 * 1 * (1 * 1)) *
      (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) :=
    headRat_cast m _ _ (BcS_head Fc ks m A r hcF s _ 1 constFrS_one)
  set mN := Nat.lcm a1.den b1.den with hmN
  set mm : ℚ := (mN : ℚ) with hmm
  have hmm0 : mm ≠ 0 := lcm_den_ne_zero a1 b1
  set uF : Fr (KF Fc m) := Fr.ofPoly [((mm : ℚ) : KF Fc m)] with huF
  have hu : IsConstFrS uF mm := constFrS_ofPoly mm
  have hAh := AcS_head Fc ks m A r hcF s uF _ hu
  have hBh := BcS_head Fc ks m A r hcF s uF _ hu
  set aX := headRat Fc m [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m)
    (AFrS Fc ks m A uF))).headD 0] with hX
  set bY := headRat Fc m [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m)
    (BFrS Fc ks m A uF))).headD 0] with hY
  have hXv : aX = s ^ 2 * (mm * mm * (mm * mm) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) :=
    headRat_cast m _ _ (by simp only [List.headD_cons]; exact hAh)
  have hYv : bY = s ^ 3 * (mm * mm * (mm * mm * (mm * mm)) *
      (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) :=
    headRat_cast m _ _ (by simp only [List.headD_cons]; exact hBh)
  obtain ⟨hXi, hYi⟩ := scale_int (r 1 * r 3 - 1 / 3 * (r 2 * r 2))
    (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2))) a1 b1 1 s
    (ha1v.trans (by ring)) (hb1v.trans (by ring)) a1 b1 (ha1v.trans (by ring))
    (hb1v.trans (by ring)) mN rfl aX bY (hXv.trans (by ring)) (hYv.trans (by ring))
  -- the structural part
  have hz'ok : okS (Fc := Fc) m z' = true := T.okS_normC m h0.of_succ z
  have hz'v : T.val (m + 1) z' = T.val (m + 1) z := by
    rw [← T.sem_MP_F (m + 1) h0, ← T.sem_MP_F (m + 1) h0, hz', T.sem_normC (m + 1) h0]
  have hchk0 := T.kxChkC0S_true m A h0 g B kt l cs z' κ k mm hA4 hBok hcs hD hz'ok r hr hBq
    hκ hs (by rw [hz'v]; exact hzκ) hmG hmm0 hdisc
  have hΔ : 4 * aX.num ^ 3 + 27 * bY.num ^ 2 ≠ 0 :=
    disc_scaled r s mm hs hmm0 hdisc _ _ (hXi.trans hXv) (hYi.trans hYv)
  haveI : Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs k * κ) : KF Fc m)) :=
    ⟨not_isSquare_KF' Fc _ hFc _ hδ m⟩
  obtain ⟨kk, hkk⟩ := T.kxChkCKS_exists m A c0f hFc h0 g B kt l cs z' κ uF _ _ aX.num bY.num k
    hchk0 (by rw [hAh, hXi, hXv]) (by rw [hBh, hYi, hYv]) hΔ rtsF hrl hrs b₀ hb₀ hns hns0 hntF
  refine ⟨kk + 1, fun kmax hkm ↦ ?_⟩
  unfold kxMWSearchCKS
  rw [hz]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne]
  refine ⟨k, k.2, ?_, mm, ?_, kk, by omega, ?_⟩
  · intro h
    exact hδ ⟨_, h.symm⟩
  · unfold mwScalesS
    simp only [List.mem_cons]
    right; right; right; right; left; rfl
  · exact hkk

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The level-`m + 1` constant-curve search (same class) succeeds** for large `kmax`. -/
theorem kxMWSearchTKS_of (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]]) (h0 : T.Tr (m + 1))
    (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
    (z : LC (m + 1)) (hz : kxZ Fc ks lv (m + 1) A = some z)
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hδ : IsSquare (kxKap Fc ks (m + 1) A z / sTS Fc ks m g A B kt l cs k))
    (hA4 : ∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true)
    (hBok : ∀ b ∈ B, okS (Fc := Fc) m b = true)
    (hcs : ∀ q < cs.length, okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) = true)
    (hD : ∀ q < cs.length, okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val (m + 1) (aCS Fc ks m A i) = (r i : T.F (m + 1)))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0)
    (hκ : kxKap Fc ks (m + 1) A z ≠ 0) (hs : sTS Fc ks m g A B kt l cs k ≠ 0)
    (hzκ : T.val (m + 1) z ^ 2 * T.val (m + 1) (aCS Fc ks m A 0) =
      (kxKap Fc ks (m + 1) A z : T.F (m + 1)))
    (hmG : mGS Fc ks m g A B kt l cs k ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
          ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) * (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
            (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * b₀))
    (hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0)
    (hP0 : ∀ n : ℤ, n • WeierstrassCurve.Affine.Point.some _ _ hns0 = 0 → n = 0) :
    ∃ K0, ∀ kmax, K0 ≤ kmax → kxMWSearchTKS Fc ks lv m g A B kt l cs kmax = true := by
  set κ := kxKap Fc ks (m + 1) A z with hκdef
  set s := sTS Fc ks m g A B kt l cs k with hsdef
  set z' := normC Fc (m + 1) z with hz'
  have hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i) := fun i hi ↦
    ⟨okS_spec (Fc := Fc) (hA4 i hi), T.frval_of_ratS m h0 _ (r i) (hr i hi)⟩
  set a1 := headRat Fc m (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m)
    (AFrS Fc ks m A (Fr.ofPoly [(1 : KF Fc m)])))) with ha1
  set b1 := headRat Fc m (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m)
    (BFrS Fc ks m A (Fr.ofPoly [(1 : KF Fc m)])))) with hb1
  have ha1v : a1 = s ^ 2 * (1 * 1 * (1 * 1) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) :=
    headRat_cast m _ _ (AcS_head Fc ks m A r hcF s _ 1 constFrS_one)
  have hb1v : b1 = s ^ 3 * (1 * 1 * (1 * 1 * (1 * 1)) *
      (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) :=
    headRat_cast m _ _ (BcS_head Fc ks m A r hcF s _ 1 constFrS_one)
  set mN := Nat.lcm a1.den b1.den with hmN
  set mm : ℚ := (mN : ℚ) with hmm
  have hmm0 : mm ≠ 0 := lcm_den_ne_zero a1 b1
  set uF : Fr (KF Fc m) := Fr.ofPoly [((mm : ℚ) : KF Fc m)] with huF
  have hu : IsConstFrS uF mm := constFrS_ofPoly mm
  have hAh := AcS_head Fc ks m A r hcF s uF _ hu
  have hBh := BcS_head Fc ks m A r hcF s uF _ hu
  set aX := headRat Fc m [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m)
    (AFrS Fc ks m A uF))).headD 0] with hX
  set bY := headRat Fc m [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m)
    (BFrS Fc ks m A uF))).headD 0] with hY
  have hXv : aX = s ^ 2 * (mm * mm * (mm * mm) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) :=
    headRat_cast m _ _ (by simp only [List.headD_cons]; exact hAh)
  have hYv : bY = s ^ 3 * (mm * mm * (mm * mm * (mm * mm)) *
      (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) :=
    headRat_cast m _ _ (by simp only [List.headD_cons]; exact hBh)
  obtain ⟨hXi, hYi⟩ := scale_int (r 1 * r 3 - 1 / 3 * (r 2 * r 2))
    (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2))) a1 b1 1 s
    (ha1v.trans (by ring)) (hb1v.trans (by ring)) a1 b1 (ha1v.trans (by ring))
    (hb1v.trans (by ring)) mN rfl aX bY (hXv.trans (by ring)) (hYv.trans (by ring))
  -- the structural part
  have hz'ok : okS (Fc := Fc) m z' = true := T.okS_normC m h0.of_succ z
  have hz'v : T.val (m + 1) z' = T.val (m + 1) z := by
    rw [← T.sem_MP_F (m + 1) h0, ← T.sem_MP_F (m + 1) h0, hz', T.sem_normC (m + 1) h0]
  set c := Rat.sqrt (κ / s) with hcdef
  have hcc : c * c = κ / s := (Rat.exists_mul_self _).mp (by
    obtain ⟨q, hq⟩ := hδ; exact ⟨q, hq.symm⟩)
  have hc0 : c ≠ 0 := fun h ↦ by
    rw [h, zero_mul, eq_comm, div_eq_zero_iff] at hcc
    exact hcc.elim hκ hs
  have hscc : s * c * c = κ := by rw [mul_assoc, hcc]; field_simp
  have hchk0 := T.kxChkT0S_true m A h0 g B kt l cs z' c k mm hA4 hBok hcs hD hz'ok r hr hBq
    hc0 hs (by rw [hz'v, hzκ, hscc]) hmG hmm0 hdisc
  have hΔ : 4 * aX.num ^ 3 + 27 * bY.num ^ 2 ≠ 0 :=
    disc_scaled r s mm hs hmm0 hdisc _ _ (hXi.trans hXv) (hYi.trans hYv)
  obtain ⟨kk, hkk⟩ := T.kxChkTKS_exists m A c0f hFc h0 g B kt l cs z' c uF _ _ aX.num bY.num k
    hchk0 (by rw [hAh, hXi, hXv]) (by rw [hBh, hYi, hYv]) hΔ rtsF hrl hrs b₀ hb₀ hns hns0 hgrp hP0
  refine ⟨kk + 1, fun kmax hkm ↦ ?_⟩
  unfold kxMWSearchTKS
  rw [hz]
  simp only [List.any_eq_true, List.mem_range]
  refine ⟨k, k.2, mm, ?_, kk, by omega, ?_⟩
  · unfold mwScalesS
    simp only [List.mem_cons]
    right; right; right; right; left; rfl
  · exact hkk

end MTower

end Curves.MT
