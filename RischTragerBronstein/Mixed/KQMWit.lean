import RischTragerBronstein.Mixed.KQMDecides
import RischTragerBronstein.Mixed.KXWit

/-!
# Square roots over a logarithm, several residue classes: the antiderivative

`kqmDecideCW` mirrors `kqmDecideC` (`kqmDecideCW_isSome`) and returns, with a `true` answer, the
solution of the parametric Risch equation and one `SqCol` per residue class (`Â = s_T A`,
`z = 1`, `ρ² = 1/s_T`); `kqmDecideCW_valid`: the solution is a solution and every column is
`Good`, so the antiderivative is explicit by `sqcols_antiderivative` and `SqCol.logs`.
-/

open Polynomial CPoly Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- The column of a class as data. -/
def kqSq (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (T : List Bool)
    (Wb : BPoly (KF Fc m)) : SqCol m :=
  ⟨A.map ((MO Fc ks m).mul (mcst Fc ks m (kqS Fc ks m η A B l cs T))),
    (Wb.getD 0 []).map (unTr Fc m), (Wb.getD 1 []).map (unTr Fc m), (MO Fc ks m).one,
    (kqS Fc ks m η A B l cs T)⁻¹⟩

/-- **`kqmDecideC` with the antiderivative.** -/
def kqmDecideCW (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option (Option (KXW m)) :=
  let O := MO Fc ks m
  let rhs : LC (m + 1) := (B, GPoly.mul O (prodLinG Fc ks m cs) (powG O A l))
  let frA := kpFr Fc ks m 1 2 A
  let cls := kqCls Fc ks m η A B l cs
  if cs.length = 0 then none
  else if !kqOK Fc ks m A B l cs then none
  else if !kqConst Fc ks m η A B l cs then some none
  else if !kqRepOK Fc ks m η A B l cs then none
  else
    let tors := cls.map (kqTorsC Fc ks m η A B l cs cpf ps bound rs)
    if tors.any (· == none) then none
    else if tors.any (· == some none) then some none
    else
      let wits := (List.zip cls tors).map fun p ↦
        kqWit Fc ks m η A B l cs p.1 ((p.2.getD none).getD 0)
      match wits.allSome with
      | none => none
      | some Wbs =>
        let cols := (List.zip cls Wbs).map fun p ↦ kqSq Fc ks m η A B l cs p.1 p.2
        some ((prdeSolN Fc ks lv m frA rhs (cols.map (SqCol.code Fc ks))).map fun r ↦ (r, cols))

/-- **`kqmDecideCW` answers exactly as `kqmDecideC`.** -/
theorem kqmDecideCW_isSome (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (kqmDecideCW Fc ks lv m η A B l cs cpf ps bound rs).map Option.isSome =
      kqmDecideC Fc ks lv m η A B l cs cpf ps bound rs := by
  unfold kqmDecideCW kqmDecideC
  dsimp only
  split_ifs
  all_goals try rfl
  split
  · rename_i heq; rw [heq]; rfl
  · rename_i Wbs heq
    rw [heq]
    simp only [Option.map_some, Option.isSome_map]
    exact congrArg some ((prdeSolN_isSome _ _ _ _ _ _ _).trans (by rw [List.map_map]; rfl))

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Validity of the KQM data**: a solution with `q₀ ≠ 0`, and good columns. -/
def KQMW.Valid (lv : (m : ℕ) → LC m) (m : ℕ) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (w : KXW m) : Prop :=
  w.1 ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
    (((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) : LC (m + 1)) ::
      w.2.map (SqCol.code Fc ks)) ∧
  w.1.1.getD 0 0 ≠ 0 ∧ ∀ c ∈ w.2, SqCol.Good T A c

lemma kqSq_good (m : ℕ) (h : T.Tr m) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (Tc : List Bool) (Wb : BPoly (KF Fc m)) :
    SqCol.Good T A (kqSq Fc ks m η A B l cs Tc Wb) := by
  have hg0 := (kqGens_spec (Fc := Fc) (ks := ks) m η A B l cs).2
  have hs0 : kqS Fc ks m η A B l cs Tc ≠ 0 := prodSub_ne _ hg0 _
  refine ⟨inv_ne_zero hs0, ?_, ?_⟩
  · show T.ev m (MO Fc ks m).one ≠ 0
    rw [T.ev_one_code m h]; exact one_ne_zero
  show T.evP m (A.map ((MO Fc ks m).mul (mcst Fc ks m (kqS Fc ks m η A B l cs Tc)))) *
    (((kqS Fc ks m η A B l cs Tc)⁻¹ : ℚ) : L) = T.ev m (MO Fc ks m).one ^ 2 * T.evP m A
  rw [T.evP_mapMul m h, ← T.sem_MP m h, T.sem_mcst, T.ev_one_code m h]
  have : ((kqS Fc ks m η A B l cs Tc : ℚ) : L) ≠ 0 := by exact_mod_cast hs0
  push_cast
  field_simp

/-- **Every antiderivative returned by `kqmDecideCW` is valid.** -/
theorem kqmDecideCW_valid (m : ℕ) (h : T.Tr m) (η : LC m) (A B : GPoly (LC m)) (l : ℕ)
    (cs : List (LC m)) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (w : KXW m)
    (hdec : kqmDecideCW Fc ks lv m η A B l cs cpf ps bound rs = some (some w)) :
    KQMW.Valid T lv m A B l cs w := by
  unfold kqmDecideCW at hdec
  dsimp only at hdec
  split_ifs at hdec
  all_goals try (simp at hdec; done)
  split at hdec
  · simp at hdec
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hdec)
    have hr0 := List.find?_some hr
    simp only [decide_eq_true_eq] at hr0
    refine ⟨List.mem_of_find?_eq_some hr, hr0, fun c hc ↦ ?_⟩
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
    exact T.kqSq_good m h η A B l cs p.1 p.2

end MTower

end Curves.MT
