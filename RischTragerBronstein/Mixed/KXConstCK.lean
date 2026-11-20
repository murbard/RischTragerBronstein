import RischTragerBronstein.Mixed.KXConstComplete
import RischTragerBronstein.Mixed.KXMWDecideK
import RischTragerBronstein.Mixed.KXCertBridgeTRev

/-!
# The constant-curve conjugation check passes (completeness)

`kxChkCK_exists`: when the structural part `kxChkC0` passes, the model is integral and the class
divisor has infinite order on the curve, some level `kk` makes `kxChkCK` pass — by the export of
`indep_of_grpC0` (a certificate point `D′` of infinite order) and `ck_tail_exists`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Some level makes the constant-curve conjugation check pass.** -/
theorem kxChkCK_exists (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (z : LC 0) (κ : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (a b : ℤ)
    (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0) (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    [Fact (¬ IsSquare (sT Fc ks g A B kt l cs k * κ))]
    (hchk : kxChkC0 Fc ks c0f g A B kt l cs z κ uF Ac Bc k = true)
    (hAc : Ac = [(a : ℚ)]) (hBc : Bc = [(b : ℚ)]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
          ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
            (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * b₀))
    (hntF : ∀ n : ℤ, n • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
        (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) = 0 →
        n = 0) :
    ∃ kk, kxChkCK Fc ks c0f g A B kt l cs z κ uF Ac Bc kk k a b = true := by
  subst hAc hBc
  obtain ⟨⟨PD, hRD⟩, hnt⟩ := T.indep_of_grpC0 c0f g A B kt l cs z uF _ _ κ hFc h0 k hchk rtsF hrl
    hrs b₀ hb₀ hns hns0 hntF
  have hA : CPoly.toPoly [(a : ℚ)] = Polynomial.C (a : ℚ) := by simp [CPoly.toPoly]
  have hB : CPoly.toPoly [(b : ℚ)] = Polynomial.C (b : ℚ) := by simp [CPoly.toPoly]
  obtain ⟨kk, hkk⟩ := ck_tail_exists a b hΔ _ _ hA hB _ PD hRD (hnt PD hRD)
  refine ⟨kk, ?_⟩
  unfold kxChkCK
  rw [hchk]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨hΔ, hkk⟩

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Some level makes the same-class constant-curve check pass.** -/
theorem kxChkTK_exists (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (z : LC 0) (c : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (a b : ℤ)
    (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0) (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChkT0 Fc ks c0f g A B kt l cs z c uF Ac Bc k = true)
    (hAc : Ac = [(a : ℚ)]) (hBc : Bc = [(b : ℚ)]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
          ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
            (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * b₀))
    (hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0)
    (hP0 : ∀ n : ℤ, n • WeierstrassCurve.Affine.Point.some _ _ hns0 = 0 → n = 0) :
    ∃ kk, kxChkTK Fc ks c0f g A B kt l cs z uF Ac Bc kk k a b c = true := by
  subst hAc hBc
  obtain ⟨⟨PD, hRD⟩, ⟨PZ, hRZ⟩, hind⟩ := T.indep_of_grpT0 c0f g A B kt l cs z c uF _ _ hFc h0 k
    hchk rtsF hrl hrs b₀ hb₀ hns hns0 hgrp hP0
  have hA : CPoly.toPoly [(a : ℚ)] = Polynomial.C (a : ℚ) := by simp [CPoly.toPoly]
  have hB : CPoly.toPoly [(b : ℚ)] = Polynomial.C (b : ℚ) := by simp [CPoly.toPoly]
  obtain ⟨kk, hkk⟩ := tk_tail_exists a b hΔ _ _ hA hB _ _ PD PZ hRD hRZ (hind PD PZ hRD hRZ)
  refine ⟨kk, ?_⟩
  unfold kxChkTK
  rw [hchk]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨hΔ, hkk⟩
