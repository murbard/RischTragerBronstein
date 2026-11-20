import RischTragerBronstein.Mixed.KXDecides
import RischTragerBronstein.Mixed.SqColWit

/-!
# Square roots over an exponential with poles: the antiderivative

`kxDecideCW` mirrors `kxDecideC` (`kxDecideCW_isSome`) and returns, with a `true` answer, the
solution of the parametric Risch equation and its columns as `SqCol` data: one per class
(`Â = s_T A`, `z = 1`, `ρ² = 1/s_T`) and possibly the column of `P₊ − ∞` (`Â = (z²/κ) A`, `ρ² = κ`).
`kxDecideCW_valid`: the solution is a solution and every column is `Good`, so by
`sqcols_antiderivative` and `SqCol.logs`

  `∫ f = (y/q₀) θ + ∑ₖ (−qₖ/q₀) ρₖ (log(W₀ₖ + W₁ₖ Yₖ) − ½ log Nₖ)`,  `Yₖ = zₖ θ/ρₖ`.
-/

open Polynomial CPoly Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- The column of a class as data. -/
def kxSq (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (T : List Bool)
    (Wb : BPoly (KF Fc m)) : SqCol m :=
  ⟨A.map ((MO Fc ks m).mul (mcst Fc ks m (kxS Fc ks m g A B kt l cs T))),
    (Wb.getD 0 []).map (unTr Fc m), (Wb.getD 1 []).map (unTr Fc m), (MO Fc ks m).one,
    (kxS Fc ks m g A B kt l cs T)⁻¹⟩

/-- The column of `P₊ − ∞` as data. -/
def kxSq0 (m : ℕ) (A : GPoly (LC m)) (z : LC m) (Wb : BPoly (KF Fc m)) : SqCol m :=
  ⟨kxAh Fc ks m A z, (Wb.getD 0 []).map (unTr Fc m), (Wb.getD 1 []).map (unTr Fc m), z,
    kxKap Fc ks m A z⟩

/-- **The antiderivative data**: the parametric solution and the columns. -/
abbrev KXW (m : ℕ) := (List ℚ × LC (m + 1)) × List (SqCol m)

/-- `kxSolveC` with the antiderivative. -/
def kxSolveCW (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (extra : List (SqCol m)) : Option (Option (KXW m)) :=
  let cls := kxCls Fc ks m g A B kt l cs
  let tors := cls.map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  let wits := (List.zip cls tors).map fun p ↦
    kxWit Fc ks m g A B kt l cs p.1 ((p.2.getD none).getD 0)
  match wits.allSome with
  | none => none
  | some Wbs =>
    let cols := extra ++ (List.zip cls Wbs).map fun p ↦ kxSq Fc ks m g A B kt l cs p.1 p.2
    some ((prdeSolN Fc ks lv m (kpFr Fc ks m 1 2 A) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1))
      (cols.map (SqCol.code Fc ks))).map fun r ↦ (r, cols))

lemma kxSolveCW_isSome (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (extra : List (SqCol m)) :
    (kxSolveCW Fc ks lv m g A B kt l cs cpf ps bound rs extra).map Option.isSome =
      kxSolveC Fc ks lv m g A B kt l cs cpf ps bound rs (extra.map (SqCol.code Fc ks)) := by
  unfold kxSolveCW kxSolveC
  dsimp only
  split
  · rename_i heq; rw [heq]; rfl
  · rename_i Wbs heq
    rw [heq]
    simp only [Option.map_some, Option.isSome_map]
    exact congrArg some ((prdeSolN_isSome _ _ _ _ _ _ _).trans
      (by rw [List.map_append, List.map_map]; rfl))

/-- **`kxDecideC` with the antiderivative.** -/
def kxDecideCW (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option (Option (KXW m)) :=
  let tors := (kxCls Fc ks m g A B kt l cs).map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  if cs.length = 0 then none
  else if !kxOK Fc ks m A B kt l cs then none
  else if !kxConst Fc ks m g A B kt l cs then some none
  else if !kxRepOK Fc ks m g A B kt l cs then none
  else if tors.any (· == none) then none
  else
    let allT := !(tors.any (· == some none))
    match kxZ Fc ks lv m A with
    | none => if allT then kxSolveCW Fc ks lv m g A B kt l cs cpf ps bound rs [] else some none
    | some z =>
      match kxTors0C Fc ks m A cpf ps bound rs z with
      | none => none
      | some none => if allT then kxSolveCW Fc ks lv m g A B kt l cs cpf ps bound rs [] else none
      | some (some N) =>
        match kxWit0 Fc ks m A z N with
        | none => none
        | some W0b =>
          if allT then kxSolveCW Fc ks lv m g A B kt l cs cpf ps bound rs [kxSq0 Fc ks m A z W0b]
          else some none

/-- **`kxDecideCW` answers exactly as `kxDecideC`.** -/
theorem kxDecideCW_isSome (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (kxDecideCW Fc ks lv m g A B kt l cs cpf ps bound rs).map Option.isSome =
      kxDecideC Fc ks lv m g A B kt l cs cpf ps bound rs := by
  unfold kxDecideCW kxDecideC
  dsimp only
  rcases hz : kxZ Fc ks lv m A with _ | z
  · simp only [hz]
    split_ifs <;> first | rfl | exact kxSolveCW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · rcases ht : kxTors0C Fc ks m A cpf ps bound rs z with _ | _ | N
    · simp only [hz, ht]
      split_ifs <;> rfl
    · simp only [hz, ht]
      split_ifs <;> first | rfl | exact kxSolveCW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · rcases hw : kxWit0 Fc ks m A z N with _ | W0b
      · simp only [hz, ht, hw]
        split_ifs <;> rfl
      · simp only [hz, ht, hw]
        split_ifs <;> first | rfl | exact kxSolveCW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Validity of the KX data**: a solution with `q₀ ≠ 0`, and good columns. -/
def KXW.Valid (lv : (m : ℕ) → LC m) (m : ℕ) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (w : KXW m) : Prop :=
  w.1 ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
    (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: w.2.map (SqCol.code Fc ks)) ∧
  w.1.1.getD 0 0 ≠ 0 ∧ ∀ c ∈ w.2, SqCol.Good T A c

lemma kxSq_good (m : ℕ) (h : T.Tr m) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (Tc : List Bool) (Wb : BPoly (KF Fc m)) :
    SqCol.Good T A (kxSq Fc ks m g A B kt l cs Tc Wb) := by
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs).2
  have hs0 : kxS Fc ks m g A B kt l cs Tc ≠ 0 := prodSub_ne _ hg0 _
  refine ⟨inv_ne_zero hs0, ?_, ?_⟩
  · show T.ev m (MO Fc ks m).one ≠ 0
    rw [T.ev_one_code m h]; exact one_ne_zero
  show T.evP m (A.map ((MO Fc ks m).mul (mcst Fc ks m (kxS Fc ks m g A B kt l cs Tc)))) *
    (((kxS Fc ks m g A B kt l cs Tc)⁻¹ : ℚ) : L) = T.ev m (MO Fc ks m).one ^ 2 * T.evP m A
  rw [T.evP_mapMul m h, ← T.sem_MP m h, T.sem_mcst, T.ev_one_code m h]
  have : ((kxS Fc ks m g A B kt l cs Tc : ℚ) : L) ≠ 0 := by exact_mod_cast hs0
  push_cast
  field_simp

lemma kxSolveCW_valid (m : ℕ) (h : T.Tr m) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (extra : List (SqCol m)) (hextra : ∀ c ∈ extra, SqCol.Good T A c) (w : KXW m)
    (hw : kxSolveCW Fc ks lv m g A B kt l cs cpf ps bound rs extra = some (some w)) :
    KXW.Valid T lv m A B kt l cs w := by
  unfold kxSolveCW at hw
  dsimp only at hw
  split at hw
  · exact absurd hw (by simp)
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hw)
    have hr0 := List.find?_some hr
    simp only [decide_eq_true_eq] at hr0
    refine ⟨List.mem_of_find?_eq_some hr, hr0, fun c hc ↦ ?_⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact hextra c hc
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
      exact T.kxSq_good m h g A B kt l cs p.1 p.2

/-- **Every antiderivative returned by `kxDecideCW` is valid.** -/
theorem kxDecideCW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (g : LC m) (A B : GPoly (LC m))
    (kt l : ℕ) (cs : List (LC m)) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (w : KXW m)
    (hdec : kxDecideCW Fc ks lv m g A B kt l cs cpf ps bound rs = some (some w)) :
    KXW.Valid T lv m A B kt l cs w := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hnil : ∀ c ∈ ([] : List (SqCol m)), SqCol.Good T A c := fun c hc ↦ absurd hc (by simp)
  unfold kxDecideCW at hdec
  dsimp only at hdec
  by_cases hok : kxOK Fc ks m A B kt l cs = true
  swap
  · simp [hok] at hdec
  have hcol0 : ∀ z W0b, kxZ Fc ks lv m A = some z →
      ∀ c ∈ [kxSq0 Fc ks m A z W0b], SqCol.Good T A c := by
    intro z W0b hz c hcm
    simp only [List.mem_singleton] at hcm
    subst hcm
    have hok0 := T.kxOK_spec m hTm A B kt l cs hok
    have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
      cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
      · rfl
      · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hok0.1
    obtain ⟨q0, hq0⟩ := kxZ_some hz
    obtain ⟨hz0, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q0 z hq0
    refine ⟨hκ0, hz0, ?_⟩
    show T.evP m (kxAh Fc ks m A z) * ((kxKap Fc ks m A z : ℚ) : L) = T.ev m z ^ 2 * T.evP m A
    rw [kxAh, T.evP_mapMul m hTm, ← T.sem_MP m hTm, (T.MP m hTm).sem_mul,
      (T.MP m hTm).sem_mul, T.sem_mcst, IntermediateField.coe_mul, IntermediateField.coe_mul,
      T.sem_MP m hTm]
    have : ((kxKap Fc ks m A z : ℚ) : L) ≠ 0 := by exact_mod_cast hκ0
    push_cast
    field_simp
  rcases hz : kxZ Fc ks lv m A with _ | z
  · simp only [hz] at hdec
    split_ifs at hdec
    all_goals first | (simp at hdec; done) |
      exact T.kxSolveCW_valid m hTm g A B kt l cs cpf ps bound rs [] hnil w hdec
  · rcases ht : kxTors0C Fc ks m A cpf ps bound rs z with _ | _ | N
    · simp only [hz, ht] at hdec
      split_ifs at hdec
      all_goals simp at hdec
    · simp only [hz, ht] at hdec
      split_ifs at hdec
      all_goals first | (simp at hdec; done) |
        exact T.kxSolveCW_valid m hTm g A B kt l cs cpf ps bound rs [] hnil w hdec
    · rcases hw : kxWit0 Fc ks m A z N with _ | W0b
      · simp only [hz, ht, hw] at hdec
        split_ifs at hdec
        all_goals simp at hdec
      · simp only [hz, ht, hw] at hdec
        split_ifs at hdec
        all_goals first | (simp at hdec; done) |
          exact T.kxSolveCW_valid m hTm g A B kt l cs cpf ps bound rs _ (hcol0 z W0b hz) w hdec

end MTower

end Curves.MT
