import RischTragerBronstein.Jacobian.PrincipalTest

/-!
# Searching for a non-zero kernel vector

`nullSearch cols`: a non-trivial linear relation `∑ cᵢ colᵢ = 0` among computable polynomials,
normalised to `c_j = 1`, by `linSolve` on the other columns.

* `nullSearch_sound`: an answer is a relation with `c_j = 1`;
* `nullSearch_complete`: if a non-trivial relation exists over an extension field, the search
  answers.
-/

open Polynomial CPoly

namespace Sup

variable {F : Type*} [Field F] [DecidableEq F]

/-- The search. -/
def nullSearch (cols : List (CPoly F)) : Option (ℕ × List F) :=
  (List.range cols.length).findSome? fun j ↦
    (linSolve (cols.set j []) (neg (cols.getD j []))).map fun cs ↦ (j, cs)

/-- **Soundness**: the full coefficient vector `cs.set j 1` is a relation. -/
theorem nullSearch_sound (cols : List (CPoly F)) {j : ℕ} {cs : List F}
    (h : nullSearch cols = some (j, cs)) :
    j < cols.length ∧ (cs.set j 1).length = cols.length ∧ (cs.set j 1).getD j 0 = 1 ∧
      lcombS (RingHom.id F) (cs.set j 1) cols = 0 := by
  classical
  obtain ⟨j', hj', hjs⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨cs', hcs', he⟩ := Option.map_eq_some_iff.mp hjs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hjA : j' < cols.length := List.mem_range.mp hj'
  obtain ⟨hlen, hlc⟩ := linSolve_sound _ _ _ hcs'
  rw [List.length_set] at hlen
  refine ⟨hjA, by simp [hlen], ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set, hlen, hjA]
  · rw [Jac.lcombS_set (RingHom.id F) cs' cols j' 1 hlen hjA, Jac.lcombS_id, hlc]
    simp

/-- **Completeness over extension fields.** -/
theorem nullSearch_complete {S : Type*} [Field S] (φ : F →+* S) (cols : List (CPoly F))
    (cL : List S) (hcL : cL.length = cols.length) (hnz : ∃ j < cols.length, cL.getD j 0 ≠ 0)
    (h0 : lcombS φ cL cols = 0) : nullSearch cols ≠ none := by
  classical
  obtain ⟨j, hj, hcj⟩ := hnz
  set c := cL.getD j 0
  set cL' := cL.map (c⁻¹ * ·)
  have h0' : lcombS φ cL' cols = 0 := by rw [lcombS_mapMul, h0, mul_zero]
  have hcj' : cL'.getD j 0 = 1 := by
    simp only [cL', List.getD_eq_getElem?_getD, List.getElem?_map]
    have : j < cL.length := by rw [hcL]; exact hj
    rw [List.getElem?_eq_getElem this]
    simp only [Option.map_some, Option.getD_some]
    have hc : cL[j] = c := by simp [c, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    rw [hc, inv_mul_cancel₀ hcj]
  have hlin : linSolve (cols.set j []) (neg (cols.getD j [])) ≠ none := by
    refine linSolve_complete_map φ _ _ (cL'.set j 0) (by simp [cL', hcL]) ?_
    have hss : cL'.set j 1 = cL' := by
      apply List.ext_getElem (by simp)
      intro m h1 h2
      rw [List.getElem_set]
      split_ifs with hm
      · subst hm
        have := hcj'
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this
        exact this.symm
      · rfl
    have e1 := Jac.lcombS_set φ cL' cols j 1 (by simp [cL', hcL]) hj
    rw [hss, h0', C_1, one_mul] at e1
    have hz : lcombS φ (cL'.set j 0) (cols.set j []) = lcombS φ cL' (cols.set j []) := by
      have := Jac.lcombS_set φ cL' (cols.set j []) j 0 (by simp [cL', hcL]) (by simp [hj])
      rw [this, List.set_set]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, hj]
    rw [hz, toPoly_neg, Polynomial.map_neg]
    linear_combination -e1
  intro hnone
  rw [nullSearch, List.findSome?_eq_none_iff] at hnone
  have := hnone j (List.mem_range.mpr hj)
  exact hlin (Option.map_eq_none_iff.mp this)

end Sup
