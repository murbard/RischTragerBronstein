import RischTragerBronstein.Mixed.KXDecides
import RischTragerBronstein.Mixed.KXDepMain
import RischTragerBronstein.Mixed.KXDepFind

/-!
# The Mordell–Weil exception with dependent classes: the decision answers (linear base)

`kxDecideDL_decided`: for accepted data over a linear base curve, at suitable residues, for every
large bound there is `N₀` such that for every `nmax ≥ N₀` either `kxDecideDL` answers (correctly), or
the integral is **not elementary**. So the only remaining `none` answers are non-elementary
integrals in which a non-torsion class is independent of `P₊ − ∞` (decided by `kxe_norel`; the
independence certificates of `kxDecideMW…` turn them into answers).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecideL_decides` with the oracle answers in the exception**: then every class oracle
answers and the squared residues are constant. -/
theorem kxDecideL_decides' (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks m A B kt l cs = true)
    (hrep : kxConst Fc ks m g A B kt l cs = true → kxRepOK Fc ks m g A B kt l cs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (kxDecideL Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs).isSome ∨
      (∃ z, kxZ Fc ks lv m A = some z ∧
        kxTors0C Fc ks m A (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs z = some none ∧
        ((kxCls Fc ks m g A B kt l cs).map (kxTorsC Fc ks m g A B kt l cs
          (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs)).any (· == some none) = true) ∧
        (∀ T' ∈ kxCls Fc ks m g A B kt l cs,
          (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs T').isSome) ∧
        kxConst Fc ks m g A B kt l cs = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  by_cases hcst : kxConst Fc ks m g A B kt l cs = true
  swap
  · refine ⟨fun _ ↦ 0, 0, fun _ _ ↦ Or.inl ?_⟩
    unfold kxDecideL kxDecideC
    simp only [if_neg hr0, hok, Bool.not_true, Bool.false_eq_true, if_false]
    rw [if_pos (by simpa using hcst)]; rfl
  have hrep' := hrep hcst
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hKF := fun T' ↦ T.kxm_class_KF0 m MS.hyp hk A B hsq hdegA hcopA kt l cs hok hcst hrep' T'
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    have h0 := (T.kxOK_spec m hTm A B kt l cs hok).1
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) h0
  set cls := kxCls Fc ks m g A B kt l cs with hcls
  -- the queries: `P₊ − ∞` (index `none`) and the classes
  set Q : Option (List Bool) → (ℕ → ℕ) → Prop := fun o rs ↦ match o with
    | none => ∀ z, kxZ Fc ks lv m A = some z → ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kxTors0C Fc ks m A (fun fK ↦ localCert fK 2) (primesBelow Bb) Bb rs z).isSome
    | some T' => ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bb) Bb rs T').isSome
    with hQdef
  obtain ⟨rs, hrs⟩ := exists_rs_many Fc m (none :: cls.map some) Q (fun o _ ↦ by
    cases o with
    | none =>
      rcases hz : kxZ Fc ks lv m A with _ | z
      · exact ⟨[], fun rs _ _ z' hz' ↦ by rw [hz] at hz'; cases hz'⟩
      · obtain ⟨q, hq⟩ := kxZ_some hz
        obtain ⟨hd, hlc, hsqK, hcop2, hf0⟩ :=
          T.ke_fK_facts hmon hdeg m hn hc A hsqc hdegpos hcop ha0 q z hq
        have hf0' : (toPoly (kxFK0 Fc ks m A z)).eval 0 = 1 := hf0
        obtain ⟨Els, hEls⟩ := kf_query_els_gamma Fc m (fK := kxFK0 Fc ks m A z) hd hlc hsqK hcop2
          ![(0 : KF Fc m)] ![1] ![1] (fun i ↦ by fin_cases i; simp [hf0'])
          (fun a b _ ↦ Subsingleton.elim a b)
        refine ⟨Els, fun rs h0 hE z' hz' ↦ ?_⟩
        rw [hz] at hz'
        obtain rfl := Option.some.inj hz'
        exact hEls rs h0 hE
    | some T' =>
      obtain ⟨hd, hlc, hsqK, hcop2, hvK, hinjK⟩ := hKF T'
      exact kf_query_els_gamma Fc m hd hlc hsqK hcop2 _ _ (kxMqm Fc ks m g A B kt l cs T') hvK hinjK)
  -- a uniform bound
  have hrsC : ∀ T' ∈ cls, ∃ B0, ∀ Bb, B0 ≤ Bb →
      (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bb) Bb rs T').isSome :=
    fun T' hT' ↦ hrs (some T') (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨T', hT', rfl⟩))
  obtain ⟨B1, hB1⟩ := eventually_list cls (fun T' Bb ↦
    (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bb) Bb rs T').isSome) hrsC
  obtain ⟨B2, hB2⟩ : ∃ B2, ∀ Bb, B2 ≤ Bb → ∀ z, kxZ Fc ks lv m A = some z →
      (kxTors0C Fc ks m A (fun fK ↦ localCert fK 2) (primesBelow Bb) Bb rs z).isSome := by
    rcases hz : kxZ Fc ks lv m A with _ | z
    · exact ⟨0, fun _ _ z' hz' ↦ absurd hz' (by simp)⟩
    · obtain ⟨B2, h2⟩ := hrs none (by simp) z hz
      exact ⟨B2, fun Bb hBb z' hz' ↦ by obtain rfl := Option.some.inj hz'; exact h2 Bb hBb⟩
  refine ⟨rs, max B1 B2, fun Bd hBd ↦ ?_⟩
  have hB1' := hB1 Bd (le_of_max_le_left hBd)
  have hB2' := hB2 Bd (le_of_max_le_right hBd)
  set tors := cls.map (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd
    rs) with htorsdef
  have hnone : ¬ tors.any (· == none) = true := by
    intro h
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp h
    obtain ⟨T', hT', rfl⟩ := List.mem_map.mp hx
    have := hB1' T' hT'
    simp only [beq_iff_eq] at hx0
    rw [hx0] at this; exact absurd this (by simp)
  have hallT : ¬ tors.any (· == some none) = true → ∀ T' ∈ cls, ∃ N,
      kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs T' =
        some (some N) := by
    intro hsn T' hT'
    rcases h : kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs T'
      with _ | _ | N
    · have := hB1' T' hT'; rw [h] at this; exact absurd this (by simp)
    · exfalso; apply hsn
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, hT', h⟩, by simp⟩
    · exact ⟨N, rfl⟩
  have hsolve := fun extra hsn ↦ T.kxSolveC_isSome (lv := lv) m MS.hyp hk A B hsq hdegA hcopA kt l
    cs hok hcst hrep' rs Bd extra (hallT hsn)
  unfold kxDecideL kxDecideC
  simp only [if_neg hr0, hok, hcst, hrep', Bool.not_true, Bool.false_eq_true, if_false]
  rw [← hcls, ← htorsdef, if_neg hnone]
  rcases hz : kxZ Fc ks lv m A with _ | z
  · left
    by_cases hsn : tors.any (· == some none) = true
    · rw [if_neg (by simp [hsn])]; rfl
    · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hsn)]
      exact hsolve [] hsn
  · dsimp only
    rcases ht0 : kxTors0C Fc ks m A (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs z
      with _ | _ | N
    · have := hB2' z hz; rw [ht0] at this; exact absurd this (by simp)
    · by_cases hsn : tors.any (· == some none) = true
      · right; exact ⟨⟨z, rfl, ht0, hsn⟩, hB1', trivial⟩
      · left
        dsimp only
        rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hsn)]
        exact hsolve [] hsn
    · left
      obtain ⟨q, hq⟩ := kxZ_some hz
      obtain ⟨hd, hlc, hsqK, hcop2, hf0⟩ :=
        T.ke_fK_facts hmon hdeg m hn hc A hsqc hdegpos hcop ha0 q z hq
      have hf0' : (toPoly (kxFK0 Fc ks m A z)).eval 0 = 1 := hf0
      have hspec := torsOracleC_spec (redAtKF Fc m rs) (localCert (kxFK0 Fc ks m A z) 2)
        (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) (primesBelow Bd) Bd hsqK hcop2
      have hv : ∀ q : Fin 1, (![(1 : KF Fc m)] q) ≠ 0 ∧
          (![(1 : KF Fc m)] q) ^ 2 = (toPoly (kxFK0 Fc ks m A z)).eval (![(0 : KF Fc m)] q) :=
        fun q ↦ by fin_cases q; simp [hf0']
      have hP := ((hspec 1 ![(0 : KF Fc m)] ![1] ![1] hv
        (fun a b _ ↦ Subsingleton.elim a b)).1 N ht0).2
      have hw := witW_ne_none (kxFK0 Fc ks m A z) 2 two_pos _ ![(0 : KF Fc m)] ![1] ![1] N
        (fun q ↦ by fin_cases q; simp [hf0']) hP
      rcases hw0 : kxWit0 Fc ks m A z N with _ | W0b
      · exact absurd hw0 hw
      · dsimp only; rw [hw0]; dsimp only
        by_cases hsn : tors.any (· == some none) = true
        · rw [if_neg (by simp [hsn])]; rfl
        · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hsn)]
          exact hsolve _ hsn


/-- A passing candidate makes `kxDepSearch` answer, once `nmax ≥ N, M`. -/
lemma kxDepSearch_ne_none (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (T' : List Bool) (z : LC m) (nmax N M : ℕ) (b bt : KF Fc m) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hNn : N ≤ nmax) (hMn : M ≤ nmax) (hb : kxBt0 Fc ks m g A B kt l cs T' z = some b)
    (hpm : bt = b ∨ bt = -b) (hw : kxWitD Fc ks m g A B kt l cs T' bt N M ≠ none)
    (h2 : bt * bt = (kxFKm Fc ks m g A B kt l cs T').getD 0 0) (h0 : bt ≠ 0) :
    kxDepSearch Fc ks m g A B kt l cs T' z nmax ≠ none := by
  unfold kxDepSearch
  rw [hb]
  intro h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : (N, M, bt) ∈ kxDepCands Fc m b nmax := by
    unfold kxDepCands
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨N - 1, by omega, M - 1, by omega, ?_⟩
    rcases hpm with rfl | rfl
    · left; simp [Nat.sub_add_cancel hN, Nat.sub_add_cancel hM]
    · right; simp [Nat.sub_add_cancel hN, Nat.sub_add_cancel hM]
  have := h _ hmem
  unfold kxDepTry at this
  rw [if_pos (by simp [h2, h0])] at this
  exact hw this

open Classical in
/-- `kxSolveDepC` answers when every class has a torsion answer or a found relation. -/
lemma kxSolveDepC_isSome (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g)
    (A B : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hM.tr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (hcst : kxConst Fc ks m g A B kt l cs = true)
    (hrep : kxRepOK Fc ks m g A B kt l cs = true) (rs : ℕ → ℕ) (Bd : ℕ) (z : LC m) (nmax : ℕ)
    (hall : ∀ T' ∈ kxCls Fc ks m g A B kt l cs,
      (∃ N, kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs T' =
        some (some N)) ∨
      (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs T' =
        some none ∧ kxDepSearch Fc ks m g A B kt l cs T' z nmax ≠ none)) :
    (kxSolveDepC Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs z
      nmax).isSome := by
  unfold kxSolveDepC
  dsimp only
  set cls := kxCls Fc ks m g A B kt l cs with hcls
  set tors := cls.map (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd
    rs) with htorsdef
  have hws : ∀ p ∈ List.zip cls tors, kxWitAny Fc ks m g A B kt l cs z nmax p.1 p.2 ≠ none := by
    intro p hp
    have hp1 : p.1 ∈ cls := (List.of_mem_zip hp).1
    have hp2 : p.2 = kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd
        rs p.1 := by
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      rw [← hpi]
      simp [htorsdef]
    rcases hall p.1 hp1 with ⟨N, hN⟩ | ⟨hN, hs⟩
    · obtain ⟨hd, hlc, hsqK, hcop2, hvK, hinjK⟩ :=
        T.kxm_class_KF0 m hM hk A B hsq hdegA hcopA kt l cs hok hcst hrep p.1
      rw [hp2, hN]
      unfold kxWitAny
      have hspec := torsOracleC_spec (redAtKF Fc m rs)
        (localCert (kxFKm Fc ks m g A B kt l cs p.1) 2)
        (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) (primesBelow Bd) Bd hsqK hcop2
      have hP := ((hspec _ _ _ (kxMqm Fc ks m g A B kt l cs p.1) hvK hinjK).1 N hN).2
      exact witW_ne_none _ 2 two_pos _ _ _ _ N
        (fun q ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK q).1, (hvK q).2⟩) hP
    · rw [hp2, hN]
      exact hs
  rcases hW : ((List.zip cls tors).map fun p ↦
      kxWitAny Fc ks m g A B kt l cs z nmax p.1 p.2).allSome with _ | Wbs
  · exfalso
    refine allSome_ne_none _ (fun y hy h0 ↦ ?_) hW
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact hws p hp h0
  · simp only [hW, Option.isSome_some]

open Classical in
/-- **`kxDecideDL` is correct**: whenever it answers `some b`, the integral is elementary exactly
when `b = true`. -/
theorem kxDecideDL_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (nmax : ℕ) (b : Bool) (hdec : kxDecideDL Fc ks lv m g A B kt l cs ps bound rs nmax = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔
      b = true := by
  unfold kxDecideDL at hdec
  cases hkx : kxDecideL Fc ks lv m g A B kt l cs ps bound rs with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound rs
      _ _ hkx
  | none =>
    rw [hkx] at hdec
    exact T.kxDecideDepC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs _ nmax b hdec

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The decision, up to independent points** (linear base): at suitable residues, for every large
bound there is `N₀` such that for every `nmax ≥ N₀`, either `kxDecideDL` answers correctly, or the
integral is not elementary. -/
theorem kxDecideDL_decided (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks m A B kt l cs = true)
    (hrep : kxConst Fc ks m g A B kt l cs = true → kxRepOK Fc ks m g A B kt l cs = true)
    (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ N0, ∀ nmax, N0 ≤ nmax →
      (∃ b, kxDecideDL Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax = some b ∧
        (HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔
          b = true)) ∨
      ¬ HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) := by
  obtain ⟨rs, B0, hdec⟩ := T.kxDecideL_decides' hmon hdeg m hn hc hk A hsqc hdegpos hcop B kt l cs
    hr0 hok hrep
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  suffices h : ∃ N0, ∀ nmax, N0 ≤ nmax →
      (kxDecideDL Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax).isSome ∨
      ¬ HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) by
    obtain ⟨N0, h⟩ := h
    refine ⟨N0, fun nmax hnm ↦ (h nmax hnm).imp (fun hs ↦ ?_) id⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨b, hb, T.kxDecideDL_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs _
      _ rs nmax b hb⟩
  by_cases hf : HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ)
  swap
  · exact ⟨0, fun _ _ ↦ Or.inr hf⟩
  rcases hdec Bd hBd with h1 | ⟨⟨z, hz, ht0, -⟩, hallS, hcst⟩
  · refine ⟨0, fun nmax _ ↦ Or.inl ?_⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    unfold kxDecideDL
    rw [hb]; rfl
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hrep' := hrep hcst
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hok0.1
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs).2
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  obtain ⟨-, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q0 z hq0
  have hκs : ∀ κ' ∈ kxKap Fc ks m A z :: kxGens Fc ks m g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
    rcases List.mem_cons.mp h with rfl | h
    · exact hκ0
    · exact hg0 κ' h
  obtain ⟨E, _, _, _, TE, θE, rts0, ι, sI, c, u, v, hTEn, hθE, hrl0, hrts0, hcd, hu, hv, heq⟩ :=
    T.kqm_lift m hn A θ hθ hgen _ hf _ hκs
  obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
  set cls := kxCls Fc ks m g A B kt l cs with hcls
  have hNk : ∀ k : Fin cls.length, ∃ Nk : ℕ, ∀ nmax, Nk ≤ nmax →
      kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
        some none → kxDepSearch Fc ks m g A B kt l cs cls[(k : ℕ)] z nmax ≠ none := by
    intro k
    by_cases htk : kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs
        cls[(k : ℕ)] = some none
    · obtain ⟨N, M, b, bt, hN1, hM1, hb, hpm, hw, h2, h0⟩ :=
        TE.kx_rel_found hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B kt l cs hok hcst hrep'
          (primesBelow Bd) Bd rs _ k htk z s hz ht0 hs2 hs' θE hθE sI c u hcd hu v hv heq rts hrl
          hrts c0 hFc
      exact ⟨max N M, fun nmax hnm _ ↦ kxDepSearch_ne_none m g A B kt l cs _ z nmax N M b bt hN1
        hM1 (le_of_max_le_left hnm) (le_of_max_le_right hnm) hb hpm hw h2 h0⟩
    · exact ⟨0, fun _ _ h ↦ absurd h htk⟩
  choose Nk hNk using hNk
  refine ⟨∑ k, Nk k, fun nmax hnm ↦ Or.inl ?_⟩
  unfold kxDecideDL
  rcases hL : kxDecideL Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs with _ | b
  swap
  · rfl
  dsimp only
  have hnone : ¬ (cls.map (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd)
      Bd rs)).any (· == none) = true := by
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
  refine T.kxSolveDepC_isSome m MS.hyp hk A B hsq hdegA hcopA kt l cs hok hcst hrep' rs Bd z nmax
    fun T' hT' ↦ ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT'
  rcases h : kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[i]
    with _ | _ | N
  · have := hallS _ hT'; rw [h] at this; exact absurd this (by simp)
  · right
    refine ⟨rfl, hNk ⟨i, hi⟩ nmax ?_ h⟩
    exact le_trans (Finset.single_le_sum (fun k _ ↦ Nat.zero_le (Nk k)) (Finset.mem_univ _)) hnm
  · left; exact ⟨N, rfl⟩

end MTower

end Curves.MT
