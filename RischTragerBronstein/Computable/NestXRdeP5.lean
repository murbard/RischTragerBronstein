import RischTragerBronstein.Computable.NestXRdeP4

/-!
# The Risch equation over a logarithmic level: the degree bound

`primNbXP` is the degree bound of `prdePrimX` (`B = 0`, `A` dominates, `B` dominates,
`deg B + 1 = deg A`, balanced); `prim_NbXP`: every solution `Y` of `A Y′ + B Y = r`
(`deg r ≤ R`) has `deg Y ≤ N`, or `Y = 0` when there is no bound.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestX

open Tower.NestP Tower.NestM

/-- The degree bound of `prdePrimX`. -/
def primNbXP {α : Type} (O : COps α) (lim : List α → List (List ℚ × α)) (η : α)
    (A B : GPoly α) (R : ℕ) : Option ℕ :=
  let dA := degG O A
  let bZ := GPoly.isZero O B
  let dB := degG O B
  let lcA := leadG O A
  let lcB := leadG O B
  let Finf := O.mul lcB (O.inv lcA)
  let Am := if dA = 0 then O.zero else A.getD (dA - 1) O.zero
  let Bm := if dA = 0 then O.zero else B.getD (dA - 1) O.zero
  let β := O.neg (O.mul (O.add (O.mul Am (O.neg Finf)) Bm) (O.inv lcA))
  if bZ then some (R - dA + 1)
  else if dA < dB then (if dB ≤ R then some (R - dB) else none)
  else if dB + 1 < dA then some (R - dA + 1)
  else if dB + 1 = dA then some (max (R - dA + 1) (limN lim (O.neg Finf) η))
  else some (max (R - dA + 1) (limN lim β η))

lemma primNb_geXP {α : Type} (O : COps α) (lim : List α → List (List ℚ × α)) (η : α)
    (A B : GPoly α) (R N : ℕ) (h : primNbXP O lim η A B R = some N) :
    R ≤ N + (if (!GPoly.isZero O B && decide (degG O A < degG O B)) = true then degG O B
      else degG O A) := by
  unfold primNbXP at h
  simp only at h
  by_cases hz : GPoly.isZero O B = true
  · rw [if_pos hz] at h
    cases h
    simp [hz]
    omega
  · rw [if_neg hz] at h
    have hz' : GPoly.isZero O B = false := by simpa using hz
    by_cases hlt : degG O A < degG O B
    · rw [if_pos hlt] at h
      split_ifs at h with hle
      cases h
      simp [hz', hlt]
      omega
    · rw [if_neg hlt] at h
      simp only [hz', hlt, Bool.not_false, decide_false, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      split_ifs at h <;> cases h <;>
        first
        | omega
        | exact (by omega : R ≤ R - degG O A + 1 + degG O A).trans
            (Nat.add_le_add_right (le_max_left _ _) _)

end Tower.NestX

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

section Nb

variable (m : ℕ) (h : T.Tr (m + 1)) {η : Code (m + 1)}

set_option maxHeartbeats 1600000 in
/-- **The degree bound at a logarithmic level.** -/
theorem prim_NbXP (hnd : ∀ y : T.F m, y′ ≠ T.ηX m h η)
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MX m h) lim) (A B : GPoly (Code (m + 1)))
    (hA0 : GPoly.toPoly (T.MX m h) A ≠ 0) (Y r : (T.F m)[X]) (R : ℕ) (hr : r.natDegree ≤ R)
    (heq : GPoly.toPoly (T.MX m h) A * implicitDeriv (C (T.ηX m h η)) Y +
      GPoly.toPoly (T.MX m h) B * Y = r) :
    (∀ N, primNbXP (opsM ks m) lim η A B R = some N → Y.natDegree ≤ N) ∧
      (primNbXP (opsM ks m) lim η A B R = none → Y = 0) := by
  set M := T.MX m h with hM
  have hlA : M.sem (leadG (opsM ks m) A) = (GPoly.toPoly M A).leadingCoeff := sem_leadGXP M A
  have hlB : M.sem (leadG (opsM ks m) B) = (GPoly.toPoly M B).leadingCoeff := sem_leadGXP M B
  have hFinf : M.sem ((opsM ks m).mul (leadG (opsM ks m) B) (opsM ks m |>.inv (leadG (opsM ks m) A))) =
      (GPoly.toPoly M B).leadingCoeff / (GPoly.toPoly M A).leadingCoeff := by
    rw [M.sem_mul, M.sem_inv, hlA, hlB, div_eq_mul_inv]
  have hlimN : ∀ (ρ : Code (m + 1)) (n : ℕ), (∃ z : T.F m, z′ + (n : T.F m) * T.ηX m h η = M.sem ρ) →
      n ≤ limN lim ρ η := fun ρ n ⟨z, hz⟩ ↦ le_limNXP (algebraMap Kc (T.F m)) M lim hlim ρ η hnd n z hz
  unfold primNbXP
  simp only [degG_eq M]
  by_cases hBz : GPoly.isZero (opsM ks m) B = true
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

end NestMTower

end Tower.NestM
