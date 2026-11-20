import RischTragerBronstein.Mixed.SysPrimVG
import RischTragerBronstein.Mixed.SysPrimVSome

/-!
# When `primSysVG` answers

`primSysVG_isSome`: `primSysVG` answers when the limit `Λ = lim A₀/q` becomes upper triangular with
diagonal `fCode dgᵢ` after the gauge `C Λ C⁻¹ − C′ C⁻¹` and the limit system is non-degenerate.
`invOKG_of`: the inverse check holds for codes of inverse matrices.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable {m : ℕ}

/-- **The inverse check** for codes of mutually inverse matrices. -/
lemma invOKG_of (h : T.Tr m) {n : ℕ} (C Ci : List (List (LC m)))
    (h1 : ∀ i j : Fin n, ∑ k : Fin n, (T.MP m h).sem (cgV Fc ks m C i k) *
      (T.MP m h).sem (cgV Fc ks m Ci k j) = if i = j then 1 else 0)
    (h2 : ∀ i j : Fin n, ∑ k : Fin n, (T.MP m h).sem (cgV Fc ks m Ci i k) *
      (T.MP m h).sem (cgV Fc ks m C k j) = if i = j then 1 else 0) :
    invOKG Fc ks m n C Ci = true := by
  set M := T.MP m h with hM
  simp only [invOKG, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true]
  intro i j
  have e : M.sem (if i = j then (MO Fc ks m).one else (MO Fc ks m).zero) =
      if i = j then 1 else 0 := by
    split_ifs
    · exact M.sem_one
    · exact M.sem_zero
  refine ⟨?_, ?_⟩
  · rw [M.isZero_iff, M.sem_add, M.sem_neg, T.sem_lsumC_fin h, e]
    simp only [(T.MP m h).sem_mul]
    rw [h1 i j, add_neg_cancel]
  · rw [M.isZero_iff, M.sem_add, M.sem_neg, T.sem_lsumC_fin h, e]
    simp only [(T.MP m h).sem_mul]
    rw [h2 i j, add_neg_cancel]

/-- **`primSysVG` answers** when the gauged limit is upper triangular with diagonal `fCode dgᵢ`
and the limit system is non-degenerate. -/
theorem primSysVG_isSome (h0 : T.Tr m) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h0) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).natDegree ≤
      (GPoly.toPoly (T.MP m h0) q).natDegree)
    (Λ : Fin n → Fin n → T.F m)
    (hΛ : ∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).coeff (GPoly.toPoly (T.MP m h0) q).natDegree =
      Λ i j)
    (hinv : invOKG Fc ks m n C Ci = true)
    (htri : ∀ i j, j < i → gaugeM (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m C i j))
      (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m Ci i j)) Λ i j = 0)
    (hdiag : ∀ i, gaugeM (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m C i j))
      (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m Ci i j)) Λ i i =
        (T.MP m h0).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg i)))
    (hok : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h0).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin n → T.F m, c ≠ 0 →
      (∀ i, (c i)′ + ∑ j, Λ i j * c j = 0) →
      ¬ ∃ y : Fin n → T.F m, ∀ i, (y i)′ + ∑ j, Λ i j * y j = (T.MP m h0).sem η * c i) :
    (primSysVG Fc ks m η rde dg C Ci n A0 q hh G0).isSome := by
  classical
  set M := T.MP m h0 with hM
  rw [Bool.and_eq_true] at hmon
  have hqM := isMonicC_spec M q hmon.1
  have hhM := isMonicC_spec M hh hmon.2
  have hsem := fun i j ↦ (T.sem_lamCL0 h0 η n A0 q hh G0 hqM hhM hA i j).trans (hΛ i j)
  have hsemF : (fun i j ↦ M.sem (lamCL Fc ks m η n A0 q hh G0 0 i j)) = Λ := funext fun i ↦
    funext fun j ↦ hsem i j
  have hG := T.sem_gaugeLC h0 C Ci (lamCL Fc ks m η n A0 q hh G0 0)
  rw [hsemF] at hG
  have hGij : ∀ i j, M.sem (gaugeLG Fc ks m n C Ci (lamCL Fc ks m η n A0 q hh G0 0) i j) =
      gaugeM (fun i j : Fin n ↦ M.sem (cgV Fc ks m C i j))
        (fun i j : Fin n ↦ M.sem (cgV Fc ks m Ci i j)) Λ i j := fun i j ↦
    congrFun (congrFun hG i) j
  have htriOK : triOKC Fc ks m dg n
      (gaugeLG Fc ks m n C Ci (lamCL Fc ks m η n A0 q hh G0 0)) = true := by
    simp only [triOKC, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    intro i j
    refine ⟨⟨?_, ?_⟩, fun cw hcw ↦ ?_⟩
    · by_cases hji : j < i
      · right; rw [M.isZero_iff, hGij]; exact htri i j hji
      · left; exact not_lt.mp hji
    · rw [M.isZero_iff, M.sem_add, M.sem_neg, hGij, hdiag, add_neg_cancel]
    · rw [M.isZero_iff, M.sem_deriv]; exact hok i cw hcw
  unfold primSysVG
  rw [if_pos (by rw [hinv, htriOK]; rfl)]
  refine T.primSysBL_isSome m h0 η n A0 q hh G0 0 _
    (fun ws ↦ T.gaugeLowG_spec h0 rde hrde dg C Ci n _ hinv htriOK ws)
    (by rw [hmon.1, hmon.2]; rfl) (fun i j ↦ ?_) ?_
  · rw [degree_eq_natDegree hqM.ne_zero]
    exact (degree_le_natDegree).trans (by exact_mod_cast hA i j)
  · intro c hc hhom hy
    simp only [mv, hsem] at hhom hy
    exact hnd c hc hhom hy

end MTower

end Curves.MT
