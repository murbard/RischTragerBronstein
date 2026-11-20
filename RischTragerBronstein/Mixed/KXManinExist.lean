import RischTragerBronstein.Mixed.KXRepS2
import RischTragerBronstein.Mixed.ManinRep
import RischTragerBronstein.Mixed.KXMWDecideSM

/-!
# Completeness of the level-`m + 1` Manin search, relative to `MKT`

`kxChkTSM_true_nonIso`: for non-constant `j` (`β ≠ 0`), independent exception points and a passing
structural check, Manin's kernel theorem over `Kₘ` makes the Manin check `kxChkTSM` pass
(`manCertP_exists` + the exact rationality test `ratOfK`).
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (c : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m))

set_option maxHeartbeats 8000000 in
open Classical in
/-- **Completeness of the Manin search for non-constant `j`, relative to `MKT`**: when the structural
check passes and the exception points are independent, the level-`m + 1` Manin check `kxChkTSM`
passes, if `β ≠ 0` and Manin's kernel theorem holds over `Kₘ`. -/
theorem kxChkTSM_true_nonIso (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc k = true)
    (hM : Manin.MKT (KF Fc m))
    (hβ : Manin.bt Manin.dX (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) (CPoly.toPoly Ac))
      (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) (CPoly.toPoly Bc)) ≠ 0)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero)) :
    let cC : ℕ → T.F (m + 1) := (fun i ↦ (GPoly.toPoly (T.MP (m + 1) h0) A).coeff i)
    let xC : Fin cs.length → T.F (m + 1) := (fun q ↦ (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
    let βC : Fin cs.length → T.F (m + 1) := (fun q ↦
      ((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
        ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) * (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
          (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      (∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0) →
      (∀ n : ℤ, n • WeierstrassCurve.Affine.Point.some _ _ hns0 = 0 → n = 0) →
        kxChkTSM Fc ks m g A B kt l cs z c uF Ac Bc k = true := by
  intro cC xC βC hns hns0 hgrp hP0
  have hΔq : 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
    have hc := hchk
    simp only [kxChkT0S, Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hdisc := hc.1.1.1.1.2
    intro h0'
    rw [show 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 =
      CPoly.toPoly (discCS Fc m Ac Bc) by
      simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_ofNat,
        Polynomial.C_ofNat]; ring, ← CPoly.isZero_iff] at h0'
    rw [h0'] at hdisc; exact absurd hdisc (by decide)
  obtain ⟨D', Z', -, -, ⟨PD, PZ, hRD, hRZ⟩, -⟩ := T.rep_of_chkT0S m g A B kt l cs z c uF Ac Bc h0 k
    hchk rtsF hrl hrs b₀ hb₀ hns hns0
  have hind := T.indep_rep m g A B kt l cs z c uF Ac Bc h0 k hchk rtsF hrl hrs b₀ hb₀ hns hns0
    hgrp hP0 PD PZ hRD hRZ
  have hRat : ∀ x : KF Fc m, (ratOfK Fc m x).isSome = true ↔ ∃ q : ℚ, x = q := fun x ↦ by
    constructor
    · intro h
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
      exact ⟨q, (ratOfK_spec Fc hq).symm⟩
    · rintro ⟨q, rfl⟩; rw [ratOfK_ratCast]; rfl
  have hc := Manin.manCertP_exists hM hRat Ac Bc hΔq hβ _ _ PD PZ hRD hRZ hind
  simp only [kxChkTSM, hchk, Bool.true_and, Bool.or_eq_true]
  exact hc

end MTower

end Curves.MT

