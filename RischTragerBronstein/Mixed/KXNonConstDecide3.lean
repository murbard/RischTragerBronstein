import RischTragerBronstein.Mixed.KXNonConstDecide2
import RischTragerBronstein.Mixed.KXNonConstCS
import RischTragerBronstein.Mixed.KXRepCS
import RischTragerBronstein.Mixed.EllIsoCert1

/-!
# Non-constant curves at the levels `m + 1`: the decision

`kxDecideNCS2_decides`: the non-constant decider with both branches answers, relative to `MKT` and
one condition on the search data (non-trivial twist or non-constant `j`).
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 16000000 in
/-- **Non-constant curves at the levels `m + 1` are decided, relative to two explicit gaps**:
Manin's kernel theorem over `Kₘ` (`hM`), and for every class with the zero code `z` the data of the
searches satisfy: the short model is a non-trivial twist of a constant curve or has non-constant `j` (else the curve is constant up
to scaling). Then for every large bound there are `N₀`, `K₀` such that `kxDecideNCS` answers, and
correctly. -/
theorem kxDecideNCS2_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (m : ℕ) (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (hdeg3 : degG (MO Fc ks (m + 1)) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks (m + 1) A B kt l cs = true)
    (hrep : kxConst Fc ks (m + 1) g A B kt l cs = true → kxRepOK Fc ks (m + 1) g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, WFm (MO Fc ks m) a) (hBw : ∀ b ∈ B, WFm (MO Fc ks m) b)
    (hcsw : ∀ c ∈ cs, WFm (MO Fc ks m) c) (hgw : WFm (MO Fc ks m) g)
    (hM : Manin.MKT (KF Fc m))
    (hmodel : ∀ z : LC (m + 1), kxZ Fc ks lv (m + 1) A = some z →
      ∀ kc < (kxCls Fc ks (m + 1) g A B kt l cs).length,
        (FFHeight.IsoNT (CPoly.toPoly (ncAc Fc ks m A (sTS Fc ks m g A B kt l cs kc)))
            (CPoly.toPoly (ncBc Fc ks m A (sTS Fc ks m g A B kt l cs kc))) ∨
          Manin.bt Manin.dX
            (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m))
              (CPoly.toPoly (ncAc Fc ks m A (sTS Fc ks m g A B kt l cs kc))))
            (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m))
              (CPoly.toPoly (ncBc Fc ks m A (sTS Fc ks m g A B kt l cs kc)))) ≠ 0))
    (hsqFc : sqOK Fc = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      ∃ b, kxDecideNCS2 Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax kmax = some b ∧
        (HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, hdec⟩ := T.kxDecideL_decides' hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop B kt l cs
    hr0 hok hrep
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  suffices h : ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      (kxDecideNCS2 Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome by
    obtain ⟨N0, h⟩ := h
    refine ⟨N0, fun nmax hnm ↦ ?_⟩
    obtain ⟨K0, hK⟩ := h nmax hnm
    refine ⟨K0, fun kmax hkm ↦ ?_⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hK kmax hkm)
    exact ⟨b, hb, T.kxDecideNCS2_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs
      _ _ rs nmax kmax b hb⟩
  have hDL : ∀ nmax kmax,
      (kxDecideDL Fc ks lv (m + 1) g A B kt l cs (primesBelow Bd) Bd rs nmax).isSome →
      (kxDecideNCS2 Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome := by
    intro nmax kmax h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    exact kxDecideNCS2_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax
      (Or.inl (by unfold kxDecideNCS; rw [hb]; rfl))
  rcases hdec Bd hBd with h1 | ⟨⟨z, hz, ht0, -⟩, hallS, hcst⟩
  · refine ⟨0, fun nmax _ ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    unfold kxDecideDL
    rw [hb]; rfl
  have MS := T.mspecs hmon hdeg lv (m + 2) (by omega) hc
  have hTr : T.Tr (m + 2) := MS.hyp.tr
  have hTm : T.Tr (m + 1) := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP (m + 1) hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP (m + 1) hTm) A).natDegree = degG (MO Fc ks (m + 1)) A :=
    (degG_eq (T.MP (m + 1) hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP (m + 1) hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP (m + 1) hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hrep' := hrep hcst
  have hok0 := T.kxOK_spec (m + 1) hTm A B kt l cs hok
  have ha0 : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero) = false := by
    cases h : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero)
    · rfl
    · exact absurd (((T.MP (m + 1) hTm).isZero_iff _).mp h) hok0.1
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs).2
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  obtain ⟨-, -, hκ0⟩ := T.ke_z_facts hmon hdeg (m + 1) hn hc A ha0 q0 z hq0
  have hκs : ∀ κ' ∈ kxKap Fc ks (m + 1) A z :: kxGens Fc ks (m + 1) g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
    rcases List.mem_cons.mp h with rfl | h
    · exact hκ0
    · exact hg0 κ' h
  -- a realization with the square roots
  obtain ⟨E, _, _, _, TE, ψ, rts0, hTEn, hev, hevP, hrl0, hrts0⟩ := T.lift_sqrts _ hκs
  obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
  have hTEn1 : TE.n = m + 2 := by rw [hTEn, hn]
  set θE := ψ θ with hθEdef
  have hθE : θE ^ 2 = TE.evP (m + 1) A := by rw [hevP, ← map_pow, hθ]
  have MSE := TE.mspecs hmon hdeg lv (m + 2) (by omega) hc
  have hTrE : TE.Tr (m + 2) := MSE.hyp.tr
  have hsqE := GPoly.squarefreeCheck_sound (TE.MP (m + 1) hTrE.of_succ) hsqc
  have hdegAE : 0 < (GPoly.toPoly (TE.MP (m + 1) hTrE.of_succ) A).natDegree := by
    rw [← degG_eq (TE.MP (m + 1) hTrE.of_succ) A]; exact hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := TE.roots_F (m + 1) rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : TE.F (m + 1)) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  set cls := kxCls Fc ks (m + 1) g A B kt l cs with hcls
  have hDI := fun (k : Fin cls.length) htk ↦ TE.kx_dep_or_indep hmon hdeg (m + 1) hTEn1 hc hk A hsqc
    hdegpos hcop hdeg3 B kt l cs hok hcst hrep' (primesBelow Bd) Bd rs (fun fK ↦ localCert fK 2) k
    htk z s hz ht0 hs2 hs' θE hθE hTrE hsqE hdegAE rtsF hrlF hrsF c0f hFc
  by_cases hgood : ∀ k : Fin cls.length,
      kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
        some none →
      ∃ (N M : ℕ) (b bt : KF Fc (m + 1)), 1 ≤ N ∧ 1 ≤ M ∧
        kxBt0 Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)] z = some b ∧ (bt = b ∨ bt = -b) ∧
        kxWitD Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)] bt N M ≠ none ∧
        bt * bt = (kxFKm Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)]).getD 0 0 ∧ bt ≠ 0
  · -- every non-torsion class is dependent: the relation search answers
    have hNk : ∀ k : Fin cls.length, ∃ Nk : ℕ, ∀ nmax, Nk ≤ nmax →
        kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
          some none → kxDepSearch Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)] z nmax ≠ none := by
      intro k
      by_cases htk : kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs
          cls[(k : ℕ)] = some none
      · obtain ⟨N, M, b, bt, hN1, hM1, hb, hpm, hw, h2, h0⟩ := hgood k htk
        exact ⟨max N M, fun nmax hnm _ ↦ kxDepSearch_ne_none (m + 1) g A B kt l cs _ z nmax N M b bt hN1
          hM1 (le_of_max_le_left hnm) (le_of_max_le_right hnm) hb hpm hw h2 h0⟩
      · exact ⟨0, fun _ _ h ↦ absurd h htk⟩
    choose Nk hNk using hNk
    refine ⟨∑ k, Nk k, fun nmax hnm ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    unfold kxDecideDL
    rcases hL : kxDecideL Fc ks lv (m + 1) g A B kt l cs (primesBelow Bd) Bd rs with _ | b
    swap
    · rfl
    dsimp only
    have hnone : ¬ (cls.map (kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2)
        (primesBelow Bd) Bd rs)).any (· == none) = true := by
      intro h
      obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp h
      obtain ⟨T', hT', rfl⟩ := List.mem_map.mp hx
      have := hallS T' hT'
      simp only [beq_iff_eq] at hx0
      rw [hx0] at this; exact absurd this (by simp)
    unfold kxDecideDepC
    dsimp only
    rw [if_neg hr0, if_neg (by simp [hok]), if_neg (by simp [hcst]), if_neg (by simp [hrep']),
      if_neg hnone]
    simp only [hz, ht0]
    refine T.kxSolveDepC_isSome (m + 1) MS.hyp hk A B hsq hdegA hcopA kt l cs hok hcst hrep' rs Bd z nmax
      fun T' hT' ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT'
    rcases h : kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[i]
      with _ | _ | N
    · have := hallS _ hT'; rw [h] at this; exact absurd this (by simp)
    · right
      refine ⟨rfl, hNk ⟨i, hi⟩ nmax ?_ h⟩
      exact le_trans (Finset.single_le_sum (fun k _ ↦ Nat.zero_le (Nk k)) (Finset.mem_univ _)) hnm
    · left; exact ⟨N, rfl⟩
  -- an independent class: a certificate search succeeds
  obtain ⟨k, hk'⟩ := not_forall.mp hgood
  obtain ⟨htk, hnl⟩ := Classical.not_imp.mp hk'
  obtain ⟨b₀, hb₀, hns, hns0, hgrp, hP0, hntF⟩ := (hDI k htk).resolve_left hnl
  have hcase := hmodel z hz k k.2
  obtain ⟨hA4, hBok, hcs, hD, hBq, hκ, hs, hzκ, hmG, hdisc⟩ := TE.nonconst_sideS hmon hdeg m hTEn1 hc hk
    A hsqc hdeg3 B kt l cs hok hcst hrep' c0f hFc hAw hBw hcsw hgw z hz hTrE.of_succ k
  set s := sTS Fc ks m g A B kt l cs k with hsdef
  set κ := kxKap Fc ks (m + 1) A z with hκdef
  set z' := normC Fc (m + 1) z with hz'
  have hz'ok : okS (Fc := Fc) m z' = true := TE.okS_normC m hTrE.of_succ.of_succ z
  have hz'v : TE.val (m + 1) z' = TE.val (m + 1) z := by
    rw [← TE.sem_MP_F (m + 1) hTrE.of_succ, ← TE.sem_MP_F (m + 1) hTrE.of_succ, hz',
      TE.sem_normC (m + 1) hTrE.of_succ]
  by_cases hsqk : IsSquare (κ / s)
  · set cc := Rat.sqrt (κ / s) with hccdef
    have hcc : cc * cc = κ / s :=
      (Rat.exists_mul_self _).mp (by obtain ⟨r, hr⟩ := hsqk; exact ⟨r, hr.symm⟩)
    have hcc0 : cc ≠ 0 := by
      intro h; rw [h, zero_mul] at hcc; exact div_ne_zero hκ hs hcc.symm
    have hzκ' : TE.val (m + 1) z' ^ 2 * TE.val (m + 1) (aCS Fc ks m A 0) =
        ((s * cc * cc : ℚ) : TE.F (m + 1)) := by
      rw [hz'v, hzκ, mul_assoc, hcc, mul_div_cancel₀ _ hs]
    have hchk0 := TE.kxChkT0S_true_nc m A hTrE.of_succ g B kt l cs z' cc k hA4 hBok hcs hD hz'ok hBq hcc0
      hs hzκ' hmG hdisc
    refine ⟨0, fun nmax _ ↦ ?_⟩
    rcases hcase with hiso | hβ
    · obtain ⟨kk, hkk⟩ := TE.kxChkTS_exists_iso m g A B kt l cs z' cc (mwUS Fc ks m A)
        (ncAc Fc ks m A s) (ncBc Fc ks m A s) hTrE.of_succ k hchk0 hiso rtsF hrlF hrsF b₀ hb₀ hns hns0
        hgrp hP0
      refine ⟨kk + 1, fun kmax hkm ↦ kxDecideNCS2_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax
        (Or.inl (kxDecideNCS_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax (Or.inr ?_)))⟩
      simp only [kxMWOKSN, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨hdeg3, hok⟩, hcst⟩, hrep'⟩, ?_⟩
      unfold kxMWSearchSN
      rw [hz]
      simp only [List.any_eq_true, List.mem_range]
      exact ⟨k, k.2, kk, by omega, hkk⟩
    · have hM' := TE.kxChkTSM_true_nonIso m g A B kt l cs z' cc (mwUS Fc ks m A)
        (ncAc Fc ks m A s) (ncBc Fc ks m A s) hTrE.of_succ k hchk0 hM hβ rtsF hrlF hrsF b₀ hb₀ hns hns0
        hgrp hP0
      refine ⟨0, fun kmax _ ↦ kxDecideNCS2_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax
        (Or.inl (kxDecideNCS_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax (Or.inl ?_)))⟩
      simp only [kxMWOKSMN, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨hdeg3, hok⟩, hcst⟩, hrep'⟩, ?_⟩
      unfold kxMWSearchSMN
      rw [hz]
      simp only [List.any_eq_true, List.mem_range]
      exact ⟨k, k.2, hM'⟩
  · -- the conjugation branch
    have hns' : ¬ IsSquare (s * κ) := by
      rintro ⟨t', ht'⟩
      refine hsqk ⟨t' / s, ?_⟩
      rw [div_mul_div_comm, ← ht', mul_comm s κ, mul_div_mul_right _ _ hs]
    have hδ : (Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact hns' ⟨_, h.symm⟩
    have : Fact (¬ IsSquare (Rat.cast (s * κ) : KF Fc m)) :=
      ⟨not_isSquare_KF_sqOK Fc hsqFc _ hns' m⟩
    have hzκ'' : TE.val (m + 1) z' ^ 2 * TE.val (m + 1) (aCS Fc ks m A 0) =
        ((κ : ℚ) : TE.F (m + 1)) := by rw [hz'v, hzκ]
    have hchk0 : kxChkC0S Fc ks m g A B kt l cs z' κ (mwUS Fc ks m A) (ncAc Fc ks m A s)
        (ncBc Fc ks m A s) k = true :=
      TE.kxChkC0S_true_nc m A hTrE.of_succ g B kt l cs z' κ k hA4 hBok hcs hD hz'ok hBq hκ
        hs hzκ'' hmG hdisc
    obtain ⟨D', hDs, ⟨PD, hRD⟩, htor⟩ := TE.rep_of_chkC0S m g A B kt l cs z' κ (mwUS Fc ks m A)
      (ncAc Fc ks m A s) (ncBc Fc ks m A s) hTrE.of_succ k hchk0 rtsF hrlF hrsF b₀ hb₀ hns hns0
    have hntPD : ∀ n : ℤ, n • PD = 0 → n = 0 := fun n hn ↦ by
      have h1 := htor PD hRD n hn
      apply hntF n
      rw [hDs, smul_comm n, h1, smul_zero]
    have hΔq : 4 * (CPoly.toPoly (ncAc Fc ks m A s)) ^ 3 +
        27 * (CPoly.toPoly (ncBc Fc ks m A s)) ^ 2 ≠ 0 := by
      have hc' := hchk0
      simp only [kxChkC0S, Bool.and_eq_true, Bool.not_eq_true'] at hc'
      have hdisc' := hc'.1.1.1.1.2
      intro h0'
      rw [show 4 * (CPoly.toPoly (ncAc Fc ks m A s)) ^ 3 + 27 * (CPoly.toPoly (ncBc Fc ks m A s)) ^ 2 =
        CPoly.toPoly (discCS Fc m (ncAc Fc ks m A s) (ncBc Fc ks m A s)) by
        simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_ofNat,
          Polynomial.C_ofNat]; ring, ← CPoly.isZero_iff] at h0'
      rw [h0'] at hdisc'; exact absurd hdisc' (by decide)
    refine ⟨0, fun nmax _ ↦ ?_⟩
    rcases hcase with hiso | hβ
    · obtain ⟨kk, hkk⟩ := certQ1_exists_iso (ncAc Fc ks m A s) _ _ rfl hΔq hiso _ PD hRD hntPD
      refine ⟨kk + 1, fun kmax hkm ↦ kxDecideNCS2_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax
        kmax (Or.inr (Or.inr ?_))⟩
      simp only [kxMWOKCSN, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨⟨hsqFc, hdeg3⟩, hok⟩, hcst⟩, hrep'⟩, ?_⟩
      unfold kxMWSearchCSN
      rw [hz]
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
      have hkk' : certQ1 (ncAc Fc ks m A s) (max (cdeg (ncAc Fc ks m A s)) (cdeg (ncBc Fc ks m A s))) kk
          (ptDTS Fc ks m g A B kt l cs (mwUS Fc ks m A) (ncAc Fc ks m A s) k) = true := by
        rw [cdeg_spec, cdeg_spec]; exact hkk
      refine ⟨k, k.2, by rw [hδ]; rfl, kk, by omega, ?_⟩
      unfold kxChkCS
      rw [Bool.and_eq_true]
      exact ⟨hchk0, hkk'⟩
    · have hc1 := Manin.manCert1P_exists hM _ _ hΔq hβ _ PD hRD hntPD
      refine ⟨0, fun kmax _ ↦ kxDecideNCS2_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax
        (Or.inr (Or.inl ?_))⟩
      simp only [kxMWOKCSMN, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨⟨hsqFc, hdeg3⟩, hok⟩, hcst⟩, hrep'⟩, ?_⟩
      unfold kxMWSearchCSMN
      rw [hz]
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
      refine ⟨k, k.2, by rw [hδ]; rfl, ?_⟩
      unfold kxChkCSM
      rw [Bool.and_eq_true]
      exact ⟨hchk0, hc1⟩

end MTower

end Curves.MT

