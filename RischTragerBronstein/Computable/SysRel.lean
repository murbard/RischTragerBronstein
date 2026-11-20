import RischTragerBronstein.Computable.SysVecLim

/-!
# Coupled Risch systems: constant relations satisfying many coordinates

Given a scalar relation finder `rel` (`RelSpec`: all constant relations among values, over
`ℚ`-vectors) and coordinates `vals x` (one code per basis element), `relRun` refines the unit
basis coordinate by coordinate: after `x` steps its vectors span exactly the constant vectors
`β` with `∑_b β_b vals y b = 0` for all `y < x` (`relRun_inv`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

open Tower.NestM Tower.NestP

section Codes

variable {α : Type} (O : COps α) (cst : ℚ → α)

/-- One refinement with the coordinate `vals`. -/
def relStep (rel : List α → List (List ℚ)) (p : ℕ) (vals : List α) (U : List (List ℚ)) :
    List (List ℚ) :=
  (rel (U.map fun u ↦ lcombCode O cst u vals)).map fun ρ ↦ vcomb p ρ U

/-- The refinement over the coordinates `0, …, x − 1`. -/
def relRun (rel : List α → List (List ℚ)) (p : ℕ) (vals : ℕ → List α) : ℕ → List (List ℚ)
  | 0 => (List.range p).map (unitV p)
  | x + 1 => relStep O cst rel p (vals x) (relRun rel p vals x)

end Codes

section Sem

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = q)

/-- **The specification of a scalar relation finder.** -/
structure RelSpec (rel : List α → List (List ℚ)) : Prop where
  sound : ∀ vs, ∀ u ∈ rel vs,
    ∑ j ∈ Finset.range vs.length, ((u.getD j 0 : ℚ) : K) * M.sem (vs.getD j O.zero) = 0
  complete : ∀ vs (c : List Cs), (∀ j, vs.length ≤ j → c.getD j 0 = 0) →
    ∑ j ∈ Finset.range vs.length, ι (c.getD j 0) * M.sem (vs.getD j O.zero) = 0 →
    ∃ β : List Cs, ∀ j, c.getD j 0 = ∑ k ∈ Finset.range (rel vs).length,
      β.getD k 0 * algebraMap ℚ Cs (((rel vs).getD k []).getD j 0)

variable (rel : List α → List (List ℚ)) (p : ℕ) (vals : ℕ → List α)

/-- Soundness after `x` coordinates. -/
def RSound (x : ℕ) (U : List (List ℚ)) : Prop :=
  ∀ u ∈ U, ∀ y < x, ∑ b ∈ Finset.range p, ((u.getD b 0 : ℚ) : K) * M.sem ((vals y).getD b O.zero) = 0

/-- Completeness after `x` coordinates. -/
def RComplete (x : ℕ) (U : List (List ℚ)) : Prop :=
  ∀ β : List Cs, (∀ b, p ≤ b → β.getD b 0 = 0) →
    (∀ y < x, ∑ b ∈ Finset.range p, ι (β.getD b 0) * M.sem ((vals y).getD b O.zero) = 0) →
    ∃ γ : List Cs, ∀ b, β.getD b 0 = ∑ k ∈ Finset.range U.length,
      γ.getD k 0 * algebraMap ℚ Cs ((U.getD k []).getD b 0)

include hcst in
lemma sem_lcomb_vals (u : List ℚ) (vs : List α) (hvs : vs.length = p) :
    M.sem (lcombCode O cst u vs) =
      ∑ b ∈ Finset.range p, ((u.getD b 0 : ℚ) : K) * M.sem (vs.getD b O.zero) := by
  rw [sem_lcombCode M cst hcst, zipWith_sum_getD (fun (q : ℚ) a ↦ (q : K) * M.sem a) 0 O.zero
    (by simp), hvs]

include hcst in
/-- **The refinement invariants.** -/
lemma relRun_inv (hrel : RelSpec ι M rel) (hlen : ∀ x, (vals x).length = p)
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    ∀ x, RSound M p vals x (relRun O cst rel p vals x) ∧
      RComplete ι M p vals x (relRun O cst rel p vals x)
  | 0 => by
    refine ⟨fun u _ y hy ↦ absurd hy (Nat.not_lt_zero _), fun β hβ _ ↦ ?_⟩
    refine ⟨(List.range p).map fun b ↦ β.getD b 0, fun b ↦ ?_⟩
    simp only [relRun, List.length_map, List.length_range]
    have e : ∀ k ∈ Finset.range p, ((List.range p).map fun b ↦ β.getD b 0).getD k 0 *
        algebraMap ℚ Cs ((((List.range p).map (unitV p)).getD k []).getD b 0) =
        if b = k then (if b < p then β.getD b 0 else 0) else 0 := fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      rw [NestTower.getD_range_map _ _ hk', NestTower.getD_range_map _ _ hk', getD_unitV]
      by_cases hbk : b = k
      · subst hbk; simp [hk']
      · simp [hbk]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
    by_cases hb : b < p
    · simp [hb]
    · simp only [Finset.mem_range, hb, if_false]
      exact hβ b (by omega)
  | x + 1 => by
    obtain ⟨hS, hC⟩ := relRun_inv hrel hlen hιrat x
    set U := relRun O cst rel p vals x with hU
    set vs := U.map fun u ↦ lcombCode O cst u (vals x) with hvs
    have hsv : ∀ k < U.length, M.sem (vs.getD k O.zero) =
        ∑ b ∈ Finset.range p, (((U.getD k []).getD b 0 : ℚ) : K) * M.sem ((vals x).getD b O.zero) :=
      fun k hk ↦ by
        rw [hvs, NestTower.getD_map' _ _ [] _ hk, sem_lcomb_vals M cst hcst p _ _ (hlen x)]
    -- a new vector, coordinate by coordinate
    have hnew : ∀ ρ : List ℚ, ∀ y : ℕ, ∑ b ∈ Finset.range p,
        (((vcomb p ρ U).getD b 0 : ℚ) : K) * M.sem ((vals y).getD b O.zero) =
        ∑ k ∈ Finset.range U.length, ((ρ.getD k 0 : ℚ) : K) * ∑ b ∈ Finset.range p,
          (((U.getD k []).getD b 0 : ℚ) : K) * M.sem ((vals y).getD b O.zero) := by
      intro ρ y
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [getD_vcomb, if_pos (Finset.mem_range.mp hb)]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ by ring
    refine ⟨fun u hu y hy ↦ ?_, fun β hβ hβy ↦ ?_⟩
    · simp only [relRun, relStep] at hu
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hu
      rw [hnew]
      rcases Nat.lt_or_ge y x with hyx | hyx
      · refine Finset.sum_eq_zero fun k hk ↦ ?_
        have hmem : U.getD k [] ∈ U := by
          rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
        rw [hS _ hmem y hyx, mul_zero]
      · have hyx' : y = x := by omega
        subst hyx'
        have := hrel.sound vs ρ hρ
        rw [hvs, List.length_map] at this
        rw [← this]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [← hvs, hsv k (Finset.mem_range.mp hk)]
    · obtain ⟨γ, hγ⟩ := hC β hβ (fun y hy ↦ hβy y (by omega))
      set γt := (List.range U.length).map fun k ↦ γ.getD k 0 with hγt
      have hγtD : ∀ k < U.length, γt.getD k 0 = γ.getD k 0 := fun k hk ↦
        NestTower.getD_range_map _ _ hk
      have h0 : ∑ k ∈ Finset.range vs.length, ι (γt.getD k 0) * M.sem (vs.getD k O.zero) = 0 := by
        rw [← hβy x (by omega), hvs, List.length_map]
        have e1 : ∀ b ∈ Finset.range p, ι (β.getD b 0) * M.sem ((vals x).getD b O.zero) =
            ∑ k ∈ Finset.range U.length, ι (γ.getD k 0) *
              ((((U.getD k []).getD b 0 : ℚ) : K) * M.sem ((vals x).getD b O.zero)) := fun b _ ↦ by
          rw [hγ b, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [map_mul, hιrat]; ring
        rw [Finset.sum_congr rfl e1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [← hvs, hsv k (Finset.mem_range.mp hk), hγtD k (Finset.mem_range.mp hk), Finset.mul_sum]
      obtain ⟨δ, hδ⟩ := hrel.complete vs γt (fun k hk ↦ List.getD_eq_default _ _ (by
        simp only [hγt, List.length_map, List.length_range]; simpa [hvs] using hk)) h0
      set R := rel vs with hR
      have hγδ : ∀ k < U.length, γ.getD k 0 = ∑ j ∈ Finset.range R.length,
          δ.getD j 0 * algebraMap ℚ Cs ((R.getD j []).getD k 0) := fun k hk ↦ by
        rw [← hγtD k hk, hδ k]
      have hlenS : (relRun O cst rel p vals (x + 1)).length = R.length := by
        simp [relRun, relStep, hR, hvs, hU]
      refine ⟨δ, fun b ↦ ?_⟩
      rw [hlenS]
      have e : ∀ j ∈ Finset.range R.length, δ.getD j 0 * algebraMap ℚ Cs
          (((relRun O cst rel p vals (x + 1)).getD j []).getD b 0) =
          δ.getD j 0 * algebraMap ℚ Cs ((vcomb p (R.getD j []) U).getD b 0) := fun j hj ↦ by
        simp only [relRun, relStep]
        rw [NestTower.getD_map' _ _ [] _ (Finset.mem_range.mp hj)]
      rw [Finset.sum_congr rfl e]
      by_cases hb : b < p
      · rw [recombine p U.length R.length (fun k b ↦ (U.getD k []).getD b 0)
          (fun j k ↦ (R.getD j []).getD k 0) (fun b ↦ β.getD b 0) (fun k ↦ γ.getD k 0)
          (fun j ↦ δ.getD j 0) (fun b _ ↦ hγ b) hγδ b hb]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [getD_vcomb, if_pos hb]
      · rw [hβ b (by omega)]
        symm
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [getD_vcomb, if_neg hb, map_zero, mul_zero]

end Sem

end Tower.Sys
