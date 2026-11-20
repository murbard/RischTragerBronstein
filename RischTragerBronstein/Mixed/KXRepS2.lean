import RischTragerBronstein.Mixed.KXRepS
import RischTragerBronstein.Mixed.EllIsoNormal

/-!
# Independence of the represented exception points

`indep_of_grp_abs`: in any abelian group, if `D = g • D'` (`g ≠ 0`), `Z = ±Z'`, `Z` has infinite
order and `2N D + 2μ Z ≠ 0` for all `N > 0`, `μ` (the group condition of the `kx` exception), then
`D'` and `Z'` are independent. With `rep_of_chkT0S`: **`indep_rep`** — when the structural check
passes, the represented code points `PD`, `PZ` satisfy no relation (the input of the certificate
existence theorems `certQ_exists_*` / `cert_complete`).
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

theorem indep_of_grp_abs {G : Type*} [AddCommGroup G] (D Z D' Z' : G) (g : ℤ) (hg : g ≠ 0)
    (hD : D = g • D') (hZ : Z = Z' ∨ Z = -Z')
    (hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0)
    (hP0 : ∀ n : ℤ, n • Z = 0 → n = 0) (m n : ℤ) (h : m • D' = n • Z') : m = 0 ∧ n = 0 := by
  -- `Z' = ε Z`
  obtain ⟨ε, hε, hZ'⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Z' = ε • Z := by
    rcases hZ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_zsmul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_zsmul, neg_neg]⟩
  -- `m D = g n ε Z`
  have key : m • D = (g * n * ε) • Z := by
    rw [hD, smul_comm m g D', h, hZ', smul_smul, smul_smul]
  by_cases hm : m = 0
  · subst hm
    refine ⟨rfl, ?_⟩
    rw [zero_smul, eq_comm] at key
    have := hP0 _ key
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hg
      · exact h2
    · rcases hε with rfl | rfl <;> simp at h1
  · exfalso
    have k2 : (2 * m) • D = (2 * (g * n * ε)) • Z := by rw [mul_smul, key, ← mul_smul]
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · apply hgrp (-m).toNat (by omega) (g * n * ε)
      rw [show ((-m).toNat : ℤ) = -m by omega, show 2 * -m = -(2 * m) by ring, neg_smul, k2,
        ← neg_smul, ← add_smul, show -(2 * (g * n * ε)) + 2 * (g * n * ε) = 0 by ring, zero_smul]
    · apply hgrp m.toNat (by omega) (-(g * n * ε))
      rw [show (m.toNat : ℤ) = m by omega, k2, ← add_smul,
        show 2 * (g * n * ε) + 2 * -(g * n * ε) = 0 by ring, zero_smul]

/-- **Non-trivial twists of constant curves** (`j = 0`, `j = 1728`, or a quadratic twist). -/
def IsoNT {K : Type*} [Field K] (A B : K[X]) : Prop :=
  (A = 0 ∧ B ≠ 0 ∧ ∀ (c : K) (w : RatFunc K), c ≠ 0 →
      algebraMap K (RatFunc K) c * algebraMap K[X] (RatFunc K) B ≠ w ^ 3) ∨
  (B = 0 ∧ A ≠ 0 ∧ ∀ (c : K) (w : RatFunc K), c ≠ 0 →
      algebraMap K (RatFunc K) c * algebraMap K[X] (RatFunc K) A ≠ w ^ 2) ∨
  (∃ (a b : K) (D : K[X]), D ≠ 0 ∧ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 ∧ A = C a * D ^ 2 ∧ B = C b * D ^ 3 ∧
    ∀ (c : K) (w : RatFunc K), c ≠ 0 →
      algebraMap K (RatFunc K) c * algebraMap K[X] (RatFunc K) D ^ 3 ≠ w ^ 2)

open scoped Classical in
/-- **The height certificate exists on non-trivial twists of constant curves.** -/
theorem certQ_exists_iso {K : Type*} [Field K] [DecidableEq K] [CharZero K] (Ac Bc : CPoly K)
    (A B : K[X]) (hAc : CPoly.toPoly Ac = A) (hBc : CPoly.toPoly Bc = B)
    (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hiso : IsoNT A B)
    (oP oQ : PtC K) (P Q : (shortW A B).toAffine.Point) (hP : Rel A B oP P) (hQ : Rel A B oQ Q)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k, certQ Ac (max A.natDegree B.natDegree) k oP oQ = true := by
  rcases hiso with ⟨hA0, hB0, hcube⟩ | ⟨hB0, hA0, hsq⟩ | ⟨a, b, D, hD, hΔ, hA, hB, hsq⟩
  · subst hA0
    exact certQ_exists_0 Ac hAc hB0 hΔ' hcube oP oQ P Q hP hQ hind
  · subst hB0
    exact certQ_exists_1728 Ac hAc hA0 hΔ' hsq oP oQ P Q hP hQ hind
  · exact certQ_exists_quad Ac hAc hD hΔ hA hB hΔ' hsq oP oQ P Q hP hQ hind

end FFHeight

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
/-- **The represented exception points are independent** (given the group condition). -/
theorem indep_rep (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc k = true)
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
        ∀ PD PZ : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
          Rel _ _ (ptDTS Fc ks m g A B kt l cs uF Ac k) PD →
          Rel _ _ (ptZTS Fc ks m g A B kt l cs z c uF k) PZ →
          ∀ m n : ℤ, m • PD = n • PZ → m = 0 ∧ n = 0 := by
  intro cC xC βC hns hns0 hgrp hP0 PD PZ hRD hRZ m' n' h
  have hmG : mGS Fc ks m g A B kt l cs k ≠ 0 := by
    simp only [kxChkT0S, Bool.and_eq_true, bne_iff_ne, ne_eq] at hchk
    exact hchk.2
  obtain ⟨D', Z', hDs, hsign, -, hrel⟩ := T.rep_of_chkT0S m g A B kt l cs z c uF Ac Bc h0 k hchk rtsF hrl
    hrs b₀ hb₀ hns hns0
  exact indep_of_grp_abs _ _ D' Z' _ (by exact_mod_cast hmG) hDs hsign hgrp hP0 m' n'
    (hrel PD PZ hRD hRZ m' n' h)

set_option maxHeartbeats 8000000 in
open Classical in
/-- **Completeness of the height search on twists of constant curves**: when the structural check
passes, the exception points are independent, and the short model is a non-trivial twist of a
constant curve (`IsoNT`), some level makes the full height check `kxChkTS` pass. -/
theorem kxChkTS_exists_iso (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc k = true)
    (hiso : FFHeight.IsoNT (CPoly.toPoly Ac) (CPoly.toPoly Bc))
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
        ∃ kk, kxChkTS Fc ks m g A B kt l cs z c uF Ac Bc kk k = true := by
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
  obtain ⟨kk, hkk⟩ := certQ_exists_iso Ac Bc _ _ rfl rfl hΔq hiso _ _ PD PZ hRD hRZ hind
  refine ⟨kk, ?_⟩
  simp only [kxChkTS, hchk, Bool.true_and]
  rw [cdeg_spec, cdeg_spec]
  exact hkk

end MTower

end Curves.MT


