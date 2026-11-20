import RischTragerBronstein.Mixed.SysPrimV
import RischTragerBronstein.Mixed.SysExpB

/-!
# When `primSysV` answers

`sem_lamCL0`: for monic `q`, `h` and `deg A₀ ≤ deg q`, the limit matrix `lamCL … 0` of the
`W`-system is `lim A₀/q`, the coefficients of `A₀` at `deg q`. `primSysV_isSome`: `primSysV`
answers when this limit matrix is upper triangular with diagonal `fCode dgᵢ` (constant log
coefficients) and the limit system is non-degenerate.
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

/-- **The limit matrix of the `W`-system with `B = 0`** is `lim A₀/q`. -/
theorem sem_lamCL0 (h : T.Tr m) (η : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m))
    (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (hqM : (GPoly.toPoly (T.MP m h) q).Monic) (hhM : (GPoly.toPoly (T.MP m h) hh).Monic)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h) (A0 i j)).natDegree ≤ (GPoly.toPoly (T.MP m h) q).natDegree)
    (i j : Fin n) :
    (T.MP m h).sem (lamCL Fc ks m η n A0 q hh G0 0 i j) =
      (GPoly.toPoly (T.MP m h) (A0 i j)).coeff (GPoly.toPoly (T.MP m h) q).natDegree := by
  classical
  have hDs : GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 0).Den =
      GPoly.toPoly (T.MP m h) hh := by
    rw [T.wSys_Den m h η n A0 q hh G0 0, pow_zero, mul_one]
  have hWa := T.wSys_a m h η n A0 q hh G0 0
  rw [hDs] at hWa
  have hBW := T.wSys_BW m h η n A0 q hh G0 0 i j
  rw [hDs] at hBW
  simp only [lamCL]
  change (T.MP m h).sem ((MO Fc ks m).mul ((MO Fc ks m).inv (leadG (MO Fc ks m)
    (wSys Fc ks m η n A0 q hh G0 0).a)) (((wSys Fc ks m η n A0 q hh G0 0).BW i j).getD
      (degG (MO Fc ks m) (wSys Fc ks m η n A0 q hh G0 0).a) (MO Fc ks m).zero)) = _
  generalize wSys Fc ks m η n A0 q hh G0 0 = W at hWa hBW ⊢
  have haM : (GPoly.toPoly (T.MP m h) W.a).Monic := by
    rw [hWa]; exact monic_X.mul (hqM.mul (hhM.mul hhM))
  have hlead : (T.MP m h).sem (leadG (MO Fc ks m) W.a) = 1 := by
    rw [leadG, ← GPoly.leadingCoeff_toPoly (T.MP m h) haM.ne_zero]; exact haM.leadingCoeff
  rw [CField.sem_mul, CField.sem_inv, hlead, inv_one, one_mul, ← coeff_toPoly_sem (T.MP m h),
    degG_eq (T.MP m h) W.a]
  change (semPM (T.MP m h) W.BW i j).coeff _ = _
  rw [hBW, hWa]
  generalize GPoly.toPoly (T.MP m h) q = qs at hqM hA ⊢
  generalize GPoly.toPoly (T.MP m h) hh = hs at hhM ⊢
  rw [monic_X.natDegree_mul (hqM.mul (hhM.mul hhM)), hqM.natDegree_mul (hhM.mul hhM),
    hhM.natDegree_mul hhM, natDegree_X, add_comm 1, coeff_X_mul, coeff_sub]
  have h1 : (hs * hs * semMat (T.MP m h) A0 i j).coeff (qs.natDegree + (hs.natDegree + hs.natDegree)) =
      (GPoly.toPoly (T.MP m h) (A0 i j)).coeff qs.natDegree := by
    rw [show qs.natDegree + (hs.natDegree + hs.natDegree) = (hs * hs).natDegree + qs.natDegree by
      rw [hhM.natDegree_mul hhM]; ring]
    change (hs * hs * GPoly.toPoly (T.MP m h) (A0 i j)).coeff _ = _
    rw [MTower.coeff_mul_of_natDegree_le' le_rfl (hA i j), (hhM.mul hhM).coeff_natDegree, one_mul]
  rw [h1]
  split_ifs
  · have hlt : (qs * (hs * DzL ((T.MP m h).sem η) 0 hs)).degree <
        ((qs.natDegree + (hs.natDegree + hs.natDegree) : ℕ) : WithBot ℕ) := by
      have hq0 : qs.degree ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hqM.ne_zero
      have hh0 : hs.degree ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hhM.ne_zero
      calc (qs * (hs * DzL ((T.MP m h).sem η) 0 hs)).degree
          = qs.degree + (hs.degree + (DzL ((T.MP m h).sem η) 0 hs).degree) := by
            rw [degree_mul, degree_mul]
        _ < qs.degree + (hs.degree + hs.degree) :=
            WithBot.add_lt_add_left hq0 (WithBot.add_lt_add_left hh0
              (degree_DzL_lt ((T.MP m h).sem η) hs hhM))
        _ = ((qs.natDegree + (hs.natDegree + hs.natDegree) : ℕ) : WithBot ℕ) := by
            rw [degree_eq_natDegree hqM.ne_zero, degree_eq_natDegree hhM.ne_zero]; push_cast; rfl
    rw [coeff_eq_zero_of_degree_lt hlt, sub_zero]
  · rw [coeff_zero, sub_zero]

/-- **`primSysV` answers** when the limit `lim A₀/q` is upper triangular with diagonal
`fCode dgᵢ` (constant log coefficients) and the limit system is non-degenerate. -/
theorem primSysV_isSome (h0 : T.Tr m) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h0) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (dg : List (FRep (LC m))) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).natDegree ≤
      (GPoly.toPoly (T.MP m h0) q).natDegree)
    (Λ : Fin n → Fin n → T.F m)
    (hΛ : ∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).coeff (GPoly.toPoly (T.MP m h0) q).natDegree =
      Λ i j)
    (htri : ∀ i j, j < i → Λ i j = 0)
    (hdiag : ∀ i, Λ i i = (T.MP m h0).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg i)))
    (hok : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h0).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin n → T.F m, c ≠ 0 →
      (∀ i, (c i)′ + ∑ j, Λ i j * c j = 0) →
      ¬ ∃ y : Fin n → T.F m, ∀ i, (y i)′ + ∑ j, Λ i j * y j = (T.MP m h0).sem η * c i) :
    (primSysV Fc ks m η rde dg n A0 q hh G0).isSome := by
  classical
  set M := T.MP m h0 with hM
  rw [Bool.and_eq_true] at hmon
  have hqM := isMonicC_spec M q hmon.1
  have hhM := isMonicC_spec M hh hmon.2
  have hsem := fun i j ↦ (T.sem_lamCL0 h0 η n A0 q hh G0 hqM hhM hA i j).trans (hΛ i j)
  have htriOK : triOKC Fc ks m dg n (lamCL Fc ks m η n A0 q hh G0 0) = true := by
    simp only [triOKC, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    intro i j
    refine ⟨⟨?_, ?_⟩, fun cw hcw ↦ ?_⟩
    · by_cases hji : j < i
      · right; rw [M.isZero_iff, hsem]; exact htri i j hji
      · left; exact not_lt.mp hji
    · rw [M.isZero_iff, M.sem_add, M.sem_neg, hsem, hdiag, add_neg_cancel]
    · rw [M.isZero_iff, M.sem_deriv]; exact hok i cw hcw
  unfold primSysV
  rw [if_pos htriOK]
  refine T.primSysBL_isSome m h0 η n A0 q hh G0 0 _
    (fun ws ↦ T.triLowC_spec h0 rde hrde dg n _ htriOK ws) (by rw [hmon.1, hmon.2]; rfl)
    (fun i j ↦ ?_) ?_
  · rw [degree_eq_natDegree hqM.ne_zero]
    exact (degree_le_natDegree).trans (by exact_mod_cast hA i j)
  · intro c hc hhom hy
    simp only [mv, hsem] at hhom hy
    exact hnd c hc hhom hy

end MTower

end Curves.MT
