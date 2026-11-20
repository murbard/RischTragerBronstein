import RischTragerBronstein.Mixed.MTRdeP4
import RischTragerBronstein.Computable.NestXRdeP5

/-!
# Mixed towers over a curve (`RdeP5`)

Ported from `Tower.NestX` (`NestXRdeP5`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u


namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


section Nb

variable (m : ℕ) (h : T.Tr (m + 1)) {η : LC m}

set_option maxHeartbeats 1600000 in
/-- **The degree bound at a logarithmic level.** -/
theorem prim_NbXP (hnd : ∀ y : T.F m, y′ ≠ T.ηX m h η)
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MX m h) lim) (A B : GPoly (LC m))
    (hA0 : GPoly.toPoly (T.MX m h) A ≠ 0) (Y r : (T.F m)[X]) (R : ℕ) (hr : r.natDegree ≤ R)
    (heq : GPoly.toPoly (T.MX m h) A * implicitDeriv (C (T.ηX m h η)) Y +
      GPoly.toPoly (T.MX m h) B * Y = r) :
    (∀ N, primNbXP (MO Fc ks m) lim η A B R = some N → Y.natDegree ≤ N) ∧
      (primNbXP (MO Fc ks m) lim η A B R = none → Y = 0) := by
  set M := T.MX m h with hM
  have hlA : M.sem (leadG (MO Fc ks m) A) = (GPoly.toPoly M A).leadingCoeff := sem_leadGXP M A
  have hlB : M.sem (leadG (MO Fc ks m) B) = (GPoly.toPoly M B).leadingCoeff := sem_leadGXP M B
  have hFinf : M.sem ((MO Fc ks m).mul (leadG (MO Fc ks m) B) (MO Fc ks m |>.inv (leadG (MO Fc ks m) A))) =
      (GPoly.toPoly M B).leadingCoeff / (GPoly.toPoly M A).leadingCoeff := by
    rw [M.sem_mul, M.sem_inv, hlA, hlB, div_eq_mul_inv]
  have hlimN : ∀ (ρ : LC m) (n : ℕ), (∃ z : T.F m, z′ + (n : T.F m) * T.ηX m h η = M.sem ρ) →
      n ≤ limN lim ρ η := fun ρ n ⟨z, hz⟩ ↦ le_limNXP (algebraMap Cc (T.F m)) M lim hlim ρ η hnd n z hz
  unfold primNbXP
  simp only [degG_eq M]
  by_cases hBz : GPoly.isZero (MO Fc ks m) B = true
  · -- `B = 0`
    rw [if_pos hBz]
    have hB0 : GPoly.toPoly M B = 0 := (GPoly.isZero_iff _ _).mp hBz
    have := natDegree_le_of_rdePrim_AXP hnd _ _ Y r R hr hA0 (Or.inl hB0) heq
    exact ⟨fun N hN ↦ by cases hN; exact this, fun h' ↦ by cases h'⟩
  rw [if_neg hBz]
  have hB0 : GPoly.toPoly M B ≠ 0 := fun h0 ↦ hBz ((GPoly.isZero_iff _ _).mpr h0)
  by_cases hlt : (GPoly.toPoly M A).natDegree < (GPoly.toPoly M B).natDegree
  · rw [if_pos hlt]
    rcases natDegree_le_of_rdePrim_BXP _ _ Y r R hr hB0 hlt heq with h0 | h1
    · refine ⟨fun N hN ↦ ?_, fun _ ↦ h0⟩
      rw [h0, natDegree_zero]; exact Nat.zero_le _
    · rw [if_pos (by omega : (GPoly.toPoly M B).natDegree ≤ R)]
      exact ⟨fun N hN ↦ by cases hN; omega, fun h' ↦ by cases h'⟩
  rw [if_neg hlt]
  by_cases hlt2 : (GPoly.toPoly M B).natDegree + 1 < (GPoly.toPoly M A).natDegree
  · rw [if_pos hlt2]
    have := natDegree_le_of_rdePrim_AXP hnd _ _ Y r R hr hA0 (Or.inr hlt2) heq
    exact ⟨fun N hN ↦ by cases hN; exact this, fun h' ↦ by cases h'⟩
  rw [if_neg hlt2]
  by_cases hsub : (GPoly.toPoly M B).natDegree + 1 = (GPoly.toPoly M A).natDegree
  · rw [if_pos hsub]
    refine ⟨fun N hN ↦ ?_, fun h' ↦ by cases h'⟩
    cases hN
    rcases natDegree_le_of_rdePrim_subXP _ _ Y r R hr hA0 hsub heq with h1 | ⟨z, hz⟩
    · exact h1.trans (le_max_left _ _)
    · refine (hlimN _ _ ⟨z, ?_⟩).trans (le_max_right _ _)
      rw [M.sem_neg, hFinf, hz]
  rw [if_neg hsub]
  refine ⟨fun N hN ↦ ?_, fun h' ↦ by cases h'⟩
  cases hN
  have hdAB : (GPoly.toPoly M A).natDegree = (GPoly.toPoly M B).natDegree := by omega
  rcases natDegree_le_of_rdePrim_balXP _ _ Y r R hr hA0 hdAB heq with h1 | ⟨z, hz⟩
  · exact h1.trans (le_max_left _ _)
  · refine (hlimN _ _ ⟨z, ?_⟩).trans (le_max_right _ _)
    rw [hz, M.sem_neg, M.sem_mul, M.sem_add, M.sem_mul, M.sem_neg, hFinf, M.sem_inv, hlA]
    split_ifs with hd0
    · simp only [M.sem_zero]
      ring
    · rw [← coeff_toPoly_getD', ← coeff_toPoly_getD']
      ring

end Nb


end MTower

end Curves.MT
