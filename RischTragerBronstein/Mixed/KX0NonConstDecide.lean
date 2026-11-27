import RischTragerBronstein.Mixed.KX0NonConstRec

/-!
# Level `0`: the decision for all curves

**`kxDecideNC0_decides`**: for a cubic `A` over a linear base with arbitrary coefficients (constant
or not, any `j`), `kxDecideNC0` answers for all large bounds, and correctly, with no
further hypothesis. In the Mordell–Weil case the recursive step `stepI` over `ℚ` covers curves not
constant up to scaling (height certificates, `ExH.certQ_exists_nc`; Manin certificates as a fast
path) and curves constant up to scaling (descent to `E(ℚ)`, Néron–Tate heights).
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
/-- **Level-`0` curves are decided, relative to Manin's kernel theorem over `ℚ`.** For any cubic
`A` over a linear base (well-formed codes, any coefficients: constant or not, any `j`), for every
large bound there is `N₀` such that for every relation bound `nmax ≥ N₀` there is `K₀` such that
for every level `kmax ≥ K₀`, `kxDecideNC0` answers, and correctly. -/
theorem kxDecideNC0_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (hdeg3 : degG (MO Fc ks 0) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks 0 A B kt l cs = true)
    (hrep : kxConst Fc ks 0 g A B kt l cs = true → kxRepOK Fc ks 0 g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, codeOKb a = true) (hBw : ∀ b ∈ B, codeOKb b = true)
    (hcsw : ∀ c ∈ cs, codeOKb c = true) (hgw : codeOKb g = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      ∃ b, kxDecideNC0 Fc ks lv g A B kt l cs (primesBelow Bd) Bd rs nmax kmax = some b ∧
        (HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, hdec⟩ := T.kxDecideL_decides' hmon hdeg 0 hn hc hk A hsqc hdegpos hcop B kt l cs
    hr0 hok hrep
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  suffices h : ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      (kxDecideNC0 Fc ks lv g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome by
    obtain ⟨N0, h⟩ := h
    refine ⟨N0, fun nmax hnm ↦ ?_⟩
    obtain ⟨K0, hK⟩ := h nmax hnm
    refine ⟨K0, fun kmax hkm ↦ ?_⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hK kmax hkm)
    exact ⟨b, hb, T.kxDecideNC0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs
      _ _ rs nmax kmax b hb⟩
  have hDL : ∀ nmax kmax,
      (kxDecideDL Fc ks lv 0 g A B kt l cs (primesBelow Bd) Bd rs nmax).isSome →
      (kxDecideNC0 Fc ks lv g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome := by
    intro nmax kmax h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    exact kxDecideNC0_isSome_of (lv := lv) g A B kt l cs _ _ rs nmax kmax
      (Or.inl (by unfold kxDecideDK0; rw [hb]; rfl))
  rcases hdec Bd hBd with h1 | ⟨⟨z, hz, ht0, -⟩, hallS, hcst⟩
  · refine ⟨0, fun nmax _ ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    unfold kxDecideDL
    rw [hb]; rfl
  have MS := T.mspecs hmon hdeg lv 1 (by omega) hc
  have hTr : T.Tr 1 := MS.hyp.tr
  have hTm : T.Tr 0 := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP 0 hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP 0 hTm) A).natDegree = degG (MO Fc ks 0) A :=
    (degG_eq (T.MP 0 hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP 0 hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP 0 hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hrep' := hrep hcst
  have hok0 := T.kxOK_spec 0 hTm A B kt l cs hok
  have ha0 : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero) = false := by
    cases h : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero)
    · rfl
    · exact absurd (((T.MP 0 hTm).isZero_iff _).mp h) hok0.1
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs).2
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  obtain ⟨-, -, hκ0⟩ := T.ke_z_facts hmon hdeg 0 hn hc A ha0 q0 z hq0
  have hκs : ∀ κ' ∈ kxKap Fc ks 0 A z :: kxGens Fc ks 0 g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
    rcases List.mem_cons.mp h with rfl | h
    · exact hκ0
    · exact hg0 κ' h
  -- a realization with the square roots
  obtain ⟨E, _, _, _, TE, ψ, rts0, hTEn, hev, hevP, hrl0, hrts0⟩ := T.lift_sqrts _ hκs
  obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
  have hTEn1 : TE.n = 1 := by rw [hTEn, hn]
  set θE := ψ θ with hθEdef
  have hθE : θE ^ 2 = TE.evP 0 A := by rw [hevP, ← map_pow, hθ]
  have MSE := TE.mspecs hmon hdeg lv 1 (by omega) hc
  have hTrE : TE.Tr 1 := MSE.hyp.tr
  have hsqE := GPoly.squarefreeCheck_sound (TE.MP 0 hTrE.of_succ) hsqc
  have hdegAE : 0 < (GPoly.toPoly (TE.MP 0 hTrE.of_succ) A).natDegree := by
    rw [← degG_eq (TE.MP 0 hTrE.of_succ) A]; exact hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := TE.roots_F 0 rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : TE.F 0) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  set cls := kxCls Fc ks 0 g A B kt l cs with hcls
  have hDI := fun (k : Fin cls.length) htk ↦ TE.kx_dep_or_indep hmon hdeg 0 hTEn1 hc hk A hsqc
    hdegpos hcop hdeg3 B kt l cs hok hcst hrep' (primesBelow Bd) Bd rs (fun fK ↦ localCert fK 2) k
    htk z s hz ht0 hs2 hs' θE hθE hTrE hsqE hdegAE rtsF hrlF hrsF c0f hFc
  by_cases hgood : ∀ k : Fin cls.length,
      kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
        some none →
      ∃ (N M : ℕ) (b bt : KF Fc 0), 1 ≤ N ∧ 1 ≤ M ∧
        kxBt0 Fc ks 0 g A B kt l cs cls[(k : ℕ)] z = some b ∧ (bt = b ∨ bt = -b) ∧
        kxWitD Fc ks 0 g A B kt l cs cls[(k : ℕ)] bt N M ≠ none ∧
        bt * bt = (kxFKm Fc ks 0 g A B kt l cs cls[(k : ℕ)]).getD 0 0 ∧ bt ≠ 0
  · -- every non-torsion class is dependent: the relation search answers
    have hNk : ∀ k : Fin cls.length, ∃ Nk : ℕ, ∀ nmax, Nk ≤ nmax →
        kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
          some none → kxDepSearch Fc ks 0 g A B kt l cs cls[(k : ℕ)] z nmax ≠ none := by
      intro k
      by_cases htk : kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs
          cls[(k : ℕ)] = some none
      · obtain ⟨N, M, b, bt, hN1, hM1, hb, hpm, hw, h2, h0⟩ := hgood k htk
        exact ⟨max N M, fun nmax hnm _ ↦ kxDepSearch_ne_none 0 g A B kt l cs _ z nmax N M b bt hN1
          hM1 (le_of_max_le_left hnm) (le_of_max_le_right hnm) hb hpm hw h2 h0⟩
      · exact ⟨0, fun _ _ h ↦ absurd h htk⟩
    choose Nk hNk using hNk
    refine ⟨∑ k, Nk k, fun nmax hnm ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    unfold kxDecideDL
    rcases hL : kxDecideL Fc ks lv 0 g A B kt l cs (primesBelow Bd) Bd rs with _ | b
    swap
    · rfl
    dsimp only
    have hnone : ¬ (cls.map (kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2)
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
    refine T.kxSolveDepC_isSome 0 MS.hyp hk A B hsq hdegA hcopA kt l cs hok hcst hrep' rs Bd z nmax
      fun T' hT' ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT'
    rcases h : kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[i]
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
  obtain ⟨hA4, hcs, hD, hBq, hκ, hs, hzκ, hmG, hdisc⟩ := TE.nonconst_side0 hmon hdeg hTEn1 hc hk
    A hsqc hdeg3 B kt l cs hok hcst hrep' c0f hFc hAw hBw hcsw hgw z hz hTrE.of_succ k
  have hFc' : Fc = [Fc.headD [], [1]] := by rw [hFc]; rfl
  set κ := kxKap Fc ks 0 A z with hκdef
  set s := sT Fc ks g A B kt l cs k with hsdef
  set z' := normC Fc 0 z with hz'
  have hz'ok : codeOKb z' = true := codeOKb_normC Fc z
  have hz'v : TE.val 0 z' = TE.val 0 z := by
    rw [← TE.sem_MP_F 0 hTrE.of_succ, ← TE.sem_MP_F 0 hTrE.of_succ, hz', TE.sem_normC 0 hTrE.of_succ]
  have hRat : ∀ x : ℚ, (fun _ ↦ true) x = true ↔ ∃ q : ℚ, x = q :=
    fun x ↦ ⟨fun _ ↦ ⟨x, (Rat.cast_id x).symm⟩, fun _ ↦ rfl⟩
  refine ⟨0, fun nmax _ ↦ ?_⟩
  by_cases hsqr : IsSquare (κ / s)
  · set c := Rat.sqrt (κ / s) with hcdef
    have hcc : c * c = κ / s := (Rat.exists_mul_self _).mp (by
      obtain ⟨q, hq⟩ := hsqr; exact ⟨q, hq.symm⟩)
    have hc0 : c ≠ 0 := fun h ↦ by
      rw [h, zero_mul, eq_comm, div_eq_zero_iff] at hcc
      exact hcc.elim hκ hs
    have hscc : s * c * c = κ := by rw [mul_assoc, hcc]; field_simp
    have hchk0 := TE.kxChkT0_true_nc (Fc.headD []) hFc' hTrE.of_succ g A B kt l cs z' c k hA4 hBw hcs
      hD hz'ok hBq hc0 hs (by rw [hz'v, hzκ, hscc]) hmG hdisc
    obtain ⟨⟨PD, hRD⟩, ⟨PZ, hRZ⟩, hind⟩ := TE.indep_of_grpT0 (Fc.headD []) g A B kt l cs z' c _ _ _
      hFc' hTrE.of_succ k hchk0 rtsF hrlF hrsF b₀ hb₀ hns hns0 hgrp hP0
    obtain ⟨K0, hK0⟩ := stepI_complete recQ_complete _ _ _ _ (disc_of_chkT0 hchk0) PD PZ hRD
      hRZ (hind PD PZ hRD hRZ)
    refine ⟨K0, fun kmax hkm ↦ kxDecideNC0_isSome_of (lv := lv) g A B kt l cs _ _ rs nmax kmax
      (Or.inr (Or.inl ?_))⟩
    simp only [kxMWOKT0R, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨hFc', hdeg3⟩, hok⟩, hcst⟩, hrep'⟩, ?_⟩
    unfold kxMWSearchT0R
    rw [hz]
    simp only [List.any_eq_true, List.mem_range]
    refine ⟨k, k.2, ?_⟩
    unfold kxChkT0R
    rw [Bool.and_eq_true]
    exact ⟨hchk0, hK0 kmax hkm⟩
  · have hnsq : ¬ IsSquare (s * κ) := by
      rintro ⟨t, ht⟩
      refine hsqr ⟨t / s, ?_⟩
      rw [div_mul_div_comm, ← ht, mul_comm s, mul_div_mul_right _ _ hs]
    have hδ : (Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact hnsq ⟨_, h.symm⟩
    haveI : Fact (¬ IsSquare (sT Fc ks g A B kt l cs k * κ)) := ⟨hnsq⟩
    have hchk0 := TE.kxChkC0_true_nc (Fc.headD []) hFc' hTrE.of_succ g A B kt l cs z' κ k hA4 hBw hcs
      hD hz'ok hBq hκ hs (by rw [hz'v, hzκ]) hmG hdisc
    obtain ⟨⟨PD, hRD⟩, hnt⟩ := TE.indep_of_grpC0 (Fc.headD []) g A B kt l cs z' _ _ _ κ
      hFc' hTrE.of_succ k hchk0 rtsF hrlF hrsF b₀ hb₀ hns hns0 hntF
    obtain ⟨K0, hK0⟩ := stepI1_complete recQ1_complete _ _ _ (disc_of_chkC0 hchk0) PD hRD
      (hnt PD hRD)
    refine ⟨K0, fun kmax hkm ↦ kxDecideNC0_isSome_of (lv := lv) g A B kt l cs _ _ rs nmax kmax
      (Or.inr (Or.inr ?_))⟩
    simp only [kxMWOKC0R, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨hFc', hdeg3⟩, hok⟩, hcst⟩, hrep'⟩, ?_⟩
    unfold kxMWSearchC0R
    rw [hz]
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
    refine ⟨k, k.2, by rw [hδ]; rfl, ?_⟩
    unfold kxChkC0R
    rw [Bool.and_eq_true]
    exact ⟨hchk0, hK0 kmax hkm⟩

end MTower

end Curves.MT
