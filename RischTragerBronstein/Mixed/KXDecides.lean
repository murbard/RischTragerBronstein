import RischTragerBronstein.Mixed.KXMain
import RischTragerBronstein.Mixed.KEDecides
import RischTragerBronstein.Mixed.KQMDecides

/-!
# Square roots over an exponential level with poles: the decision answers

`kxDecideL` (local torsion certificates) answers for every large bound at suitable residues
(`kxDecideL_decides`), for accepted data, **except** when `P₊ − ∞` (the point over `t = 0`) and some
pole class are both non-torsion — the case needing the relations between independent points
(Mordell–Weil), which the algorithm leaves open. The class data over `Kₘ` (`kxm_class_KF0`) need
no square roots; the curve of `P₊ − ∞` is the normalized curve of `ke_fK_facts`.
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

open Classical in
/-- **The data of a class over `Kₘ`** (no square roots needed). -/
theorem kxm_class_KF0 (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g)
    (A B : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hM.tr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (hcst : kxConst Fc ks m g A B kt l cs = true)
    (hrep : kxRepOK Fc ks m g A B kt l cs = true) (T' : List Bool) :
    let fK := kxFKm Fc ks m g A B kt l cs T'
    0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime 2 (fK.length - 1) ∧
      (∀ i, kxBem Fc ks m g A B kt l cs T' i ≠ 0 ∧
        kxBem Fc ks m g A B kt l cs T' i ^ 2 =
          (toPoly fK).eval (kxAlm Fc ks m g A B kt l cs T' i)) ∧
      Function.Injective
        (fun i ↦ (kxAlm Fc ks m g A B kt l cs T' i, kxBem Fc ks m g A B kt l cs T' i)) := by
  intro fK
  set hm : T.Tr m := hM.tr.of_succ
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs).2
  set S : T.F m := ((kxS Fc ks m g A B kt l cs T' : ℚ) : T.F m) with hSdef
  have hS0 : kxS Fc ks m g A B kt l cs T' ≠ 0 := prodSub_ne _ hg0 _
  have hS : S ≠ 0 := by simp only [hSdef]; exact_mod_cast hS0
  have hpf : Polynomial.C S * GPoly.toPoly (T.MP m hm) A = (toPoly fK).map (T.psiF m hm) :=
    (T.toPoly_kxFKm m hm g A B kt l cs T').symm
  have hsqp : Squarefree (Polynomial.C S * GPoly.toPoly (T.MP m hm) A) :=
    (Associated.squarefree_iff (associated_unit_mul_left _ (Polynomial.C S)
      (isUnit_C.mpr (Ne.isUnit hS)))).mpr hsq
  have hcopp : Nat.Coprime 2 (Polynomial.C S * GPoly.toPoly (T.MP m hm) A).natDegree := by
    rw [natDegree_C_mul hS]; exact hcopA
  obtain ⟨hd, hsqK, hcop2⟩ := fK_facts' (T.psiF m hm) fK (CPoly.trim_trim _) _ hpf
    hsqp.ne_zero hsqp hcopp
  have hne : toPoly fK ≠ 0 := hsqK.ne_zero
  have hdpos : 0 < fK.length - 1 := by
    rw [← hd, ← natDegree_map_eq_of_injective (T.psiF m hm).injective, ← hpf, natDegree_C_mul hS]
    exact hdegA
  have hlc : fK.getD (fK.length - 1) 0 ≠ 0 := by
    rw [← coeff_toPoly, ← hd]; exact leadingCoeff_ne_zero.mpr hne
  have hpt : ∀ q (hq : q < cs.length), (kxRep Fc ks m g A B kt l cs q).1 = T' →
      (T.MP m hm).sem (kxBm Fc ks m g A B kt l cs q) ≠ 0 ∧
      (T.MP m hm).sem (kxBm Fc ks m g A B kt l cs q) ^ 2 =
        (Polynomial.C S * GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) := by
    intro q hq hqT
    obtain ⟨-, hκ, -⟩ := kxRep_spec m g A B kt l cs hrep q hq
    have hok' := (T.kxOK_spec m hm A B kt l cs hok).2 q hq
    have hQ := T.kxConst_spec m hm g A B kt l cs hcst q hq
    rw [T.sem_kxQ m hm] at hQ
    have hκ0 := T.kxK_ne m hM hk A B kt l cs hok hcst q hq
    have hcq0 : (kxRep Fc ks m g A B kt l cs q).2 ≠ 0 := by
      intro h0; rw [h0] at hκ; simp at hκ; exact hκ0 hκ
    have hd0 : (T.MP m hm).sem (kxD Fc ks m g cs q) ≠ 0 := T.kxD_ne m hM hk cs q hok'.1
    have hB0 := hok'.2.2.2
    have hR0 := hok'.2.1
    rw [T.sem_kxBm m hm, hqT]
    refine ⟨mul_ne_zero (by push_cast; exact mul_ne_zero hS (by exact_mod_cast hcq0))
      (div_ne_zero (mul_ne_zero hd0 hR0) hB0), ?_⟩
    have hκF : ((kxK Fc ks m g A B kt l cs q : ℚ) : T.F m) =
        ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) ^ 2 * S := by
      rw [hκ, hqT]; push_cast; ring
    rw [hκF] at hQ
    rw [eval_mul, eval_C]
    push_cast
    rw [show (S * ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) * ((T.MP m hm).sem (kxD Fc ks m g cs q) *
      (T.MP m hm).sem (kxR Fc ks m A kt l cs q) / (GPoly.toPoly (T.MP m hm) B).eval
        ((T.MP m hm).sem (kqC Fc ks m cs q)))) ^ 2 = S * ((((kxRep Fc ks m g A B kt l cs q).2 : T.F m) ^ 2 *
          S) * ((T.MP m hm).sem (kxD Fc ks m g cs q) * (T.MP m hm).sem (kxR Fc ks m A kt l cs q)) ^ 2 /
          (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ 2) by ring, ← hQ]
    field_simp
  have hmem : ∀ i : Fin (kxQs Fc ks m g A B kt l cs T').length,
      (kxQs Fc ks m g A B kt l cs T')[i] < cs.length ∧
        (kxRep Fc ks m g A B kt l cs (kxQs Fc ks m g A B kt l cs T')[i]).1 = T' := fun i ↦
    (mem_kxQs m g A B kt l cs _ _).mp (List.getElem_mem _)
  have hA : ∀ i, T.psiF m hm (kxAlm Fc ks m g A B kt l cs T' i) =
      (T.MP m hm).sem (kqC Fc ks m cs (kxQs Fc ks m g A B kt l cs T')[i]) := fun i ↦
    T.psiF_trC m hm _
  have hB : ∀ i, T.psiF m hm (kxBem Fc ks m g A B kt l cs T' i) =
      (T.MP m hm).sem (kxBm Fc ks m g A B kt l cs (kxQs Fc ks m g A B kt l cs T')[i]) := fun i ↦
    T.psiF_trC m hm _
  have hcinj := T.kx_cinj m hm A B kt l cs hok
  refine ⟨hdpos, hlc, hsqK, hcop2, fun i ↦ ⟨fun h0 ↦ ?_, ?_⟩, fun i j hij ↦ ?_⟩
  · have := hB i
    rw [h0, map_zero] at this
    exact (hpt _ (hmem i).1 (hmem i).2).1 this.symm
  · apply (T.psiF m hm).injective
    rw [map_pow, hB i, (hpt _ (hmem i).1 (hmem i).2).2, hpf, eval_map, ← hA i, eval₂_at_apply]
  · have h1 := congrArg (fun z ↦ T.psiF m hm z.1) hij
    simp only at h1
    rw [hA, hA] at h1
    have h2 := hcinj (a₁ := ⟨_, (hmem i).1⟩) (a₂ := ⟨_, (hmem j).1⟩) h1
    have h3 : (kxQs Fc ks m g A B kt l cs T')[i] = (kxQs Fc ks m g A B kt l cs T')[j] :=
      congrArg Fin.val h2
    exact Fin.ext ((List.Nodup.getElem_inj_iff (kxQs_nodup m g A B kt l cs T')).mp h3)

open Classical in
/-- `kxSolveC` answers when every class is torsion. -/
lemma kxSolveC_isSome (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g)
    (A B : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hM.tr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (hcst : kxConst Fc ks m g A B kt l cs = true)
    (hrep : kxRepOK Fc ks m g A B kt l cs = true) (rs : ℕ → ℕ) (Bd : ℕ)
    (extra : List (LC (m + 1)))
    (hall : ∀ T' ∈ kxCls Fc ks m g A B kt l cs, ∃ N,
      kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs T' =
        some (some N)) :
    (kxSolveC Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs
      extra).isSome := by
  unfold kxSolveC
  dsimp only
  set cls := kxCls Fc ks m g A B kt l cs with hcls
  set tors := cls.map (kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd
    rs) with htorsdef
  have hws : ∀ p ∈ List.zip cls tors,
      kxWit Fc ks m g A B kt l cs p.1 ((p.2.getD none).getD 0) ≠ none := by
    intro p hp
    have hp1 : p.1 ∈ cls := (List.of_mem_zip hp).1
    have hp2 : p.2 = kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd
        rs p.1 := by
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      rw [← hpi]
      simp [htorsdef]
    obtain ⟨hd, hlc, hsqK, hcop2, hvK, hinjK⟩ :=
      T.kxm_class_KF0 m hM hk A B hsq hdegA hcopA kt l cs hok hcst hrep p.1
    obtain ⟨N, hN⟩ := hall p.1 hp1
    rw [hp2, hN]
    have hspec := torsOracleC_spec (redAtKF Fc m rs)
      (localCert (kxFKm Fc ks m g A B kt l cs p.1) 2)
      (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) (primesBelow Bd) Bd hsqK hcop2
    have hP := ((hspec _ _ _ (kxMqm Fc ks m g A B kt l cs p.1) hvK hinjK).1 N hN).2
    exact witW_ne_none _ 2 two_pos _ _ _ _ N
      (fun q ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK q).1, (hvK q).2⟩) hP
  rcases hW : ((List.zip cls tors).map fun p ↦
      kxWit Fc ks m g A B kt l cs p.1 ((p.2.getD none).getD 0)).allSome with _ | Wbs
  · exfalso
    refine allSome_ne_none _ (fun y hy h0 ↦ ?_) hW
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact hws p hp h0
  · simp only [hW, Option.isSome_some]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecideL` answers** for every large bound, at suitable residues (accepted data), unless
`P₊ − ∞` and some pole class are both non-torsion. -/
theorem kxDecideL_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
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
          (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs)).any (· == some none) = true) := by
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
      · right; exact ⟨z, rfl, ht0, hsn⟩
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

open Classical in
/-- **Square roots over an exponential level with poles are decided** (accepted data), outside the
Mordell–Weil case: at suitable residues, for every large bound, either `kxDecideL` answers
correctly, or `P₊ − ∞` and some pole class are both certified non-torsion. -/
theorem kx_decided (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks m A B kt l cs = true)
    (hrep : kxConst Fc ks m g A B kt l cs = true → kxRepOK Fc ks m g A B kt l cs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (∃ b, kxDecideL Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs = some b ∧
        (HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔
          b = true)) ∨
      (∃ z, kxZ Fc ks lv m A = some z ∧
        kxTors0C Fc ks m A (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs z = some none ∧
        ((kxCls Fc ks m g A B kt l cs).map (kxTorsC Fc ks m g A B kt l cs
          (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs)).any (· == some none) = true) := by
  obtain ⟨rs, B0, h⟩ := T.kxDecideL_decides hmon hdeg m hn hc hk A hsqc hdegpos hcop B kt l cs hr0
    hok hrep
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  rcases h Bd hBd with h1 | h1
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    exact Or.inl ⟨b, hb, T.kxDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt
      l cs _ _ rs _ b hb⟩
  · exact Or.inr h1

end MTower

end Curves.MT
