import RischTragerBronstein.Mixed.KQMMain
import RischTragerBronstein.Mixed.KFSpecExist

/-!
# Several residue classes over a logarithmic level: the decision always answers

`kqmDecideL` (local torsion certificates) answers for every large bound at suitable residues
(`kqmDecideL_decides`), for accepted data (`cs ≠ []`, `kqOK`, every squared residue represented
when they are constant); with `kqmDecideC_correct` these integrals are **decided** (`kqm_decided`).
The class data over `Kₘ` (`kqm_class_KF0`) need no square roots of the generators: the ordinates
satisfy `β_q² = s_T A(c_q)` directly.
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
theorem kqm_class_KF0 (m : ℕ) (hM : T.MixHyp (m + 1)) {η : LC m} (hk : ks m = .prim η)
    (A B : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hM.tr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (l : ℕ) (cs : List (LC m))
    (hok : kqOK Fc ks m A B l cs = true) (hcst : kqConst Fc ks m η A B l cs = true)
    (hrep : kqRepOK Fc ks m η A B l cs = true) (T' : List Bool) :
    let fK := kqFKm Fc ks m η A B l cs T'
    0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime 2 (fK.length - 1) ∧
      (∀ i, kqBem Fc ks m η A B l cs T' i ≠ 0 ∧
        kqBem Fc ks m η A B l cs T' i ^ 2 = (toPoly fK).eval (kqAlm Fc ks m η A B l cs T' i)) ∧
      Function.Injective (fun i ↦ (kqAlm Fc ks m η A B l cs T' i, kqBem Fc ks m η A B l cs T' i)) := by
  intro fK
  set hm : T.Tr m := hM.tr.of_succ
  have hg0 := (kqGens_spec (Fc := Fc) (ks := ks) m η A B l cs).2
  set S : T.F m := ((kqS Fc ks m η A B l cs T' : ℚ) : T.F m) with hSdef
  have hS0 : kqS Fc ks m η A B l cs T' ≠ 0 := prodSub_ne _ hg0 _
  have hS : S ≠ 0 := by simp only [hSdef]; exact_mod_cast hS0
  have hpf : Polynomial.C S * GPoly.toPoly (T.MP m hm) A = (toPoly fK).map (T.psiF m hm) :=
    (T.toPoly_kqFKm m hm η A B l cs T').symm
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
  -- the points
  have hpt : ∀ q (hq : q < cs.length), (kqRep Fc ks m η A B l cs q).1 = T' →
      (T.MP m hm).sem (kqBm Fc ks m η A B l cs q) ≠ 0 ∧
      (T.MP m hm).sem (kqBm Fc ks m η A B l cs q) ^ 2 =
        (Polynomial.C S * GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) := by
    intro q hq hqT
    obtain ⟨-, hκ, -⟩ := kqRep_spec m η A B l cs hrep q hq
    have hok' := T.kqOK_spec m hm A B l cs hok q hq
    have hQ := T.kqConst_spec m hm η A B l cs hcst q hq
    rw [T.sem_kqQ m hm] at hQ
    have hκ0 := T.kqK_ne m hM hk A B l cs hok hcst q hq
    have hcq0 : (kqRep Fc ks m η A B l cs q).2 ≠ 0 := by
      intro h0; rw [h0] at hκ; simp at hκ; exact hκ0 hκ
    have hd0 : (T.MP m hm).sem (kqD Fc ks m η cs q) ≠ 0 := fun h0 ↦ by
      rw [T.sem_kqD m hm, T.sem_eq_val m hm η] at h0
      exact T.kqS_good m hM hk (algebraMap (T.F m) _ ((T.MP m hm).sem (kqC Fc ks m cs q)))
        (by rw [deriv_algebraMap, ← sub_eq_zero.mp h0])
    have hB0 := hok'.2.2
    have hR0 := hok'.1
    rw [T.sem_kqBm m hm, hqT]
    refine ⟨mul_ne_zero (by push_cast; exact mul_ne_zero hS (by exact_mod_cast hcq0))
      (div_ne_zero (mul_ne_zero hd0 hR0) hB0), ?_⟩
    have hκF : ((kqK Fc ks m η A B l cs q : ℚ) : T.F m) =
        ((kqRep Fc ks m η A B l cs q).2 : T.F m) ^ 2 * S := by
      rw [hκ, hqT]; push_cast; ring
    rw [hκF] at hQ
    rw [eval_mul, eval_C]
    push_cast
    rw [show (S * ((kqRep Fc ks m η A B l cs q).2 : T.F m) * ((T.MP m hm).sem (kqD Fc ks m η cs q) *
      (T.MP m hm).sem (kqR Fc ks m A l cs q) / (GPoly.toPoly (T.MP m hm) B).eval
        ((T.MP m hm).sem (kqC Fc ks m cs q)))) ^ 2 = S * ((((kqRep Fc ks m η A B l cs q).2 : T.F m) ^ 2 *
          S) * ((T.MP m hm).sem (kqD Fc ks m η cs q) * (T.MP m hm).sem (kqR Fc ks m A l cs q)) ^ 2 /
          (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ 2) by ring, ← hQ]
    field_simp
  have hmem : ∀ i : Fin (kqQs Fc ks m η A B l cs T').length,
      (kqQs Fc ks m η A B l cs T')[i] < cs.length ∧
        (kqRep Fc ks m η A B l cs (kqQs Fc ks m η A B l cs T')[i]).1 = T' := fun i ↦
    (mem_kqQs m η A B l cs _ _).mp (List.getElem_mem _)
  have hA : ∀ i, T.psiF m hm (kqAlm Fc ks m η A B l cs T' i) =
      (T.MP m hm).sem (kqC Fc ks m cs (kqQs Fc ks m η A B l cs T')[i]) := fun i ↦ T.psiF_trC m hm _
  have hB : ∀ i, T.psiF m hm (kqBem Fc ks m η A B l cs T' i) =
      (T.MP m hm).sem (kqBm Fc ks m η A B l cs (kqQs Fc ks m η A B l cs T')[i]) := fun i ↦
    T.psiF_trC m hm _
  have hcinj := T.kq_cinj m hm A B l cs hok
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
    have h3 : (kqQs Fc ks m η A B l cs T')[i] = (kqQs Fc ks m η A B l cs T')[j] :=
      congrArg Fin.val h2
    exact Fin.ext ((List.Nodup.getElem_inj_iff (kqQs_nodup m η A B l cs T')).mp h3)

/-- A uniform bound for finitely many eventual facts. -/
lemma eventually_list {α : Type*} (Ts : List α) (P : α → ℕ → Prop)
    (h : ∀ T ∈ Ts, ∃ B0, ∀ B, B0 ≤ B → P T B) : ∃ B0, ∀ B, B0 ≤ B → ∀ T ∈ Ts, P T B := by
  induction Ts with
  | nil => exact ⟨0, fun _ _ T hT ↦ absurd hT (by simp)⟩
  | cons T Ts ih =>
    obtain ⟨B1, h1⟩ := h T (by simp)
    obtain ⟨B2, h2⟩ := ih fun T' hT' ↦ h T' (List.mem_cons_of_mem _ hT')
    refine ⟨max B1 B2, fun B hB T' hT' ↦ ?_⟩
    rcases List.mem_cons.mp hT' with rfl | hT'
    · exact h1 B (le_of_max_le_left hB)
    · exact h2 B (le_of_max_le_right hB) T' hT'

lemma allSome_ne_none {α : Type*} : ∀ l : List (Option α), (∀ x ∈ l, x ≠ none) → l.allSome ≠ none
  | [], _ => by simp [List.allSome]
  | x :: l, h => by
    obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp (h x (by simp))
    have ih := allSome_ne_none l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    obtain ⟨l', hl'⟩ := Option.ne_none_iff_exists'.mp ih
    simp only [List.allSome] at hl' ⊢
    simp [List.mapM_cons, hl']

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`kqmDecideL` answers** for every large bound, at suitable residues (accepted data). -/
theorem kqmDecideL_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kqOK Fc ks m A B l cs = true)
    (hrep : kqConst Fc ks m η A B l cs = true → kqRepOK Fc ks m η A B l cs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (kqmDecideL Fc ks lv m η A B l cs (primesBelow Bd) Bd rs).isSome := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  unfold kqmDecideL kqmDecideC
  dsimp only
  simp only [if_neg hr0, hok, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hcst : kqConst Fc ks m η A B l cs = true
  swap
  · refine ⟨fun _ ↦ 0, 0, fun _ _ ↦ ?_⟩
    rw [if_pos (by simpa using hcst)]; rfl
  have hrep' := hrep hcst
  simp only [hcst, hrep', Bool.not_true, Bool.false_eq_true, if_false]
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hKF := fun T' ↦ T.kqm_class_KF0 m MS.hyp hk A B hsq hdegA hcopA l cs hok hcst hrep' T'
  set cls := kqCls Fc ks m η A B l cs with hcls
  -- residues serving every class
  obtain ⟨rs, hrs⟩ := exists_rs_many Fc m cls
    (fun T' rs ↦ ∃ B0, ∀ Bb, B0 ≤ Bb →
      (kqTorsC Fc ks m η A B l cs (fun fK ↦ localCert fK 2) (primesBelow Bb) Bb rs T').isSome)
    (fun T' _ ↦ by
      obtain ⟨hd, hlc, hsqK, hcop2, hvK, hinjK⟩ := hKF T'
      exact kf_query_els_gamma Fc m hd hlc hsqK hcop2 _ _ (kqMqm Fc ks m η A B l cs T') hvK hinjK)
  obtain ⟨B0, hB0⟩ := eventually_list cls (fun T' Bb ↦
    (kqTorsC Fc ks m η A B l cs (fun fK ↦ localCert fK 2) (primesBelow Bb) Bb rs T').isSome) hrs
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  set tors := cls.map (kqTorsC Fc ks m η A B l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs)
    with htorsdef
  have hnone : ¬ tors.any (· == none) = true := by
    intro h
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp h
    obtain ⟨T', hT', rfl⟩ := List.mem_map.mp hx
    have := hB0 Bd hBd T' hT'
    simp only [beq_iff_eq] at hx0
    rw [hx0] at this; exact absurd this (by simp)
  rw [if_neg hnone]
  by_cases hsn : tors.any (· == some none) = true
  · rw [if_pos hsn]; rfl
  rw [if_neg hsn]
  -- every class is torsion, and its witness is found
  have hws : ∀ p ∈ List.zip cls tors,
      (kqWit Fc ks m η A B l cs p.1 ((p.2.getD none).getD 0)).isSome := by
    intro p hp
    have hp1 : p.1 ∈ cls := (List.of_mem_zip hp).1
    have hp2 : p.2 = kqTorsC Fc ks m η A B l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs
        p.1 := by
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      rw [← hpi]
      simp [htorsdef]
    obtain ⟨hd, hlc, hsqK, hcop2, hvK, hinjK⟩ := hKF p.1
    rcases ht : kqTorsC Fc ks m η A B l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs p.1
      with _ | _ | N
    · have := hB0 Bd hBd p.1 hp1; rw [ht] at this; exact absurd this (by simp)
    · exfalso; apply hsn
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, hp1, ht⟩, by simp⟩
    · rw [hp2, ht]
      have hspec := torsOracleC_spec (redAtKF Fc m rs) (localCert (kqFKm Fc ks m η A B l cs p.1) 2)
        (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) (primesBelow Bd) Bd hsqK hcop2
      have hP := ((hspec _ _ _ (kqMqm Fc ks m η A B l cs p.1) hvK hinjK).1 N ht).2
      have hw := witW_ne_none _ 2 two_pos _ _ _ _ N
        (fun q ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK q).1, (hvK q).2⟩) hP
      exact Option.isSome_iff_ne_none.mpr hw
  rcases hall : ((List.zip cls tors).map fun p ↦
      kqWit Fc ks m η A B l cs p.1 ((p.2.getD none).getD 0)).allSome with _ | Wbs
  · exfalso
    refine allSome_ne_none _ (fun y hy h0 ↦ ?_) hall
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    have := hws p hp
    rw [h0] at this; exact absurd this (by simp)
  · simp only [hall, Option.isSome_some]

open Classical in
/-- **Several residue classes over a logarithmic level are decided** (accepted data): at suitable
residues, for every large bound `kqmDecideL` answers, and its answer is correct. -/
theorem kqm_decided (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kqOK Fc ks m A B l cs = true)
    (hrep : kqConst Fc ks m η A B l cs = true → kqRepOK Fc ks m η A B l cs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ b,
      kqmDecideL Fc ks lv m η A B l cs (primesBelow Bd) Bd rs = some b ∧
      (HasElementaryIntegral (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
        (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, h⟩ := T.kqmDecideL_decides hmon hdeg m hn hc hk A hsqc hdegpos hcop B l cs hr0
    hok hrep
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h Bd hBd)
  exact ⟨b, hb, T.kqmDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B l cs _ _
    rs _ b hb⟩

end MTower

end Curves.MT
