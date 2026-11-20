import RischTragerBronstein.Differential.Constants
import RischTragerBronstein.Elementary.Algebraic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Field
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Partial fractions as a sum of logarithmic derivatives

Let `L` be a differential field containing a field `F` of constants and an element `x` with
`x′ = 1`. If `s ∈ F[X]` is separable and splits in `L`, and `deg r < deg s`, then

  `r(x) / s(x) = ∑_α c_α * (x - α)′ / (x - α)`,   `c_α = r(α) / s′(α)` constant,

the sum running over the roots `α` of `s` in `L`. This is the logarithmic part of the integral of a
rational function (Bronstein §2.4); the identity itself is the barycentric form of Lagrange
interpolation.
-/

open Polynomial Finset

namespace Differential

variable {F L : Type*} [Field F] [Field L] [Differential L] [Algebra F L]

/-- **Partial fractions, explicit form.** With residues `r(α) / s′(α)`:
`r(x) / s(x) = ∑_{s(α) = 0} (r(α) / s′(α)) * (x - α)′ / (x - α)`; the roots `α` are constants
distinct from `x`. -/
theorem partial_fractions_logDeriv_explicit [DecidableEq L]
    (hF : ∀ a : F, algebraMap F L a ∈ constants L) (x : L)
    (hx : x′ = 1) (r s : F[X]) (hsep : s.Separable) (hsplit : (s.map (algebraMap F L)).Splits)
    (hdeg : r.degree < s.degree) :
    (∀ α ∈ (s.map (algebraMap F L)).roots.toFinset, α′ = 0 ∧ x - α ≠ 0) ∧
    aeval x r / aeval x s = ∑ α ∈ (s.map (algebraMap F L)).roots.toFinset,
      (aeval α r / aeval α (derivative s)) * logDeriv (x - α) := by
  set ι := algebraMap F L
  set sL := s.map ι with hsL
  set rL := r.map ι with hrL
  have hs0 : s ≠ 0 := by rintro rfl; simp at hdeg
  have hsL0 : sL ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hs0
  have hnodup : sL.roots.Nodup := nodup_roots hsep.map
  set S : Finset L := sL.roots.toFinset with hS
  have hSval : S.val = sL.roots := by rw [hS, Multiset.toFinset_val, hnodup.dedup]
  set lc := sL.leadingCoeff with hlc
  have hlc0 : lc ≠ 0 := leadingCoeff_ne_zero.mpr hsL0
  have hfac : sL = C lc * Lagrange.nodal S id := by
    rw [Lagrange.nodal_eq, Finset.prod, hSval]
    exact hsplit.eq_prod_roots
  have hcard : #S = s.natDegree := by
    rw [Finset.card_def, hSval, ← hsplit.natDegree_eq_card_roots, natDegree_map]
  have hroot : ∀ α ∈ S, eval α sL = 0 := fun α hα ↦ by
    have : α ∈ sL.roots := by rwa [hS, Multiset.mem_toFinset] at hα
    exact (mem_roots'.mp this).2
  have hconst : ∀ α ∈ S, α ∈ constants L := fun α hα ↦ by
    refine deriv_eq_zero_of_aeval_eq_zero (A := L) sL (fun i ↦ ?_) α ?_ ?_
    · rw [hsL, coeff_map]; exact hF _
    · simpa using hroot α hα
    · exact hsep.map.aeval_derivative_ne_zero (by simpa using hroot α hα)
  have hxα : ∀ α ∈ S, x ≠ α := fun α hα h ↦ by
    have := hconst α hα
    rw [mem_constants, ← h, hx] at this
    exact one_ne_zero this
  refine ⟨fun α hα ↦ ⟨hconst α hα, sub_ne_zero.mpr (hxα α hα)⟩, ?_⟩
  have hdegL : rL.degree < #S := by
    rw [hcard, hrL, degree_map, ← degree_eq_natDegree hs0]
    exact hdeg
  have hint := Lagrange.eq_interpolate (v := id) (s := S) (f := rL) (Set.injOn_id _) hdegL
  have hev := Lagrange.eval_interpolate_not_at_node (s := S) (v := id)
    (r := fun α ↦ eval (id α) rL) (x := x) hxα
  rw [← hint] at hev
  have hnod : eval x (Lagrange.nodal S id) ≠ 0 := by
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun α hα ↦ sub_ne_zero.mpr (hxα α hα)
  have hr : ∀ y : L, aeval y r = eval y rL := fun y ↦ by rw [hrL, aeval_def, eval₂_eq_eval_map]
  have hs : aeval x s = lc * eval x (Lagrange.nodal S id) := by
    rw [aeval_def, eval₂_eq_eval_map, ← hsL, hfac, eval_mul, eval_C]
  have hs' : ∀ α ∈ S, aeval α (derivative s) =
      lc * (Lagrange.nodalWeight S id α)⁻¹ := fun α hα ↦ by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, ← hsL, hfac, derivative_mul, derivative_C,
      zero_mul, zero_add, eval_mul, eval_C, Lagrange.nodalWeight_eq_eval_derivative_nodal hα,
      inv_inv]
    rfl
  rw [hr, hs, hev, mul_comm lc, mul_div_mul_left _ _ hnod, Finset.sum_div]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have hα' : α′ = 0 := hconst α hα
  have hw : Lagrange.nodalWeight S id α ≠ 0 := Lagrange.nodalWeight_ne_zero (Set.injOn_id _) hα
  have hxa : x - α ≠ 0 := sub_ne_zero.mpr (hxα α hα)
  rw [hs' α hα, hr]
  simp only [logDeriv, map_sub, hx, hα', sub_zero, id]
  field_simp

theorem partial_fractions_logDeriv (hF : ∀ a : F, algebraMap F L a ∈ constants L) (x : L)
    (hx : x′ = 1) (r s : F[X]) (hsep : s.Separable) (hsplit : (s.map (algebraMap F L)).Splits)
    (hdeg : r.degree < s.degree) :
    ∃ l : List (L × L), (∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0) ∧
      aeval x r / aeval x s = (l.map fun p ↦ p.1 * logDeriv p.2).sum := by
  classical
  set ι := algebraMap F L
  set sL := s.map ι with hsL
  set rL := r.map ι with hrL
  have hs0 : s ≠ 0 := by rintro rfl; simp at hdeg
  have hsL0 : sL ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hs0
  have hnodup : sL.roots.Nodup := nodup_roots hsep.map
  set S : Finset L := sL.roots.toFinset with hS
  have hSval : S.val = sL.roots := by rw [hS, Multiset.toFinset_val, hnodup.dedup]
  -- `s = lc * ∏ (X - α)`
  set lc := sL.leadingCoeff with hlc
  have hlc0 : lc ≠ 0 := leadingCoeff_ne_zero.mpr hsL0
  have hfac : sL = C lc * Lagrange.nodal S id := by
    rw [Lagrange.nodal_eq, Finset.prod, hSval]
    exact hsplit.eq_prod_roots
  have hcard : #S = s.natDegree := by
    rw [Finset.card_def, hSval, ← hsplit.natDegree_eq_card_roots, natDegree_map]
  -- roots are constants, and distinct from `x`
  have hroot : ∀ α ∈ S, eval α sL = 0 := fun α hα ↦ by
    have : α ∈ sL.roots := by rwa [hS, Multiset.mem_toFinset] at hα
    exact (mem_roots'.mp this).2
  have hconst : ∀ α ∈ S, α ∈ constants L := fun α hα ↦ by
    refine deriv_eq_zero_of_aeval_eq_zero (A := L) sL (fun i ↦ ?_) α ?_ ?_
    · rw [hsL, coeff_map]; exact hF _
    · simpa using hroot α hα
    · exact hsep.map.aeval_derivative_ne_zero (by simpa using hroot α hα)
  have hxα : ∀ α ∈ S, x ≠ α := fun α hα h ↦ by
    have := hconst α hα
    rw [mem_constants, ← h, hx] at this
    exact one_ne_zero this
  -- Lagrange interpolation
  have hdegL : rL.degree < #S := by
    rw [hcard, hrL, degree_map, ← degree_eq_natDegree hs0]
    exact hdeg
  have hint := Lagrange.eq_interpolate (v := id) (s := S) (f := rL) (Set.injOn_id _) hdegL
  have hev := Lagrange.eval_interpolate_not_at_node (s := S) (v := id)
    (r := fun α ↦ eval (id α) rL) (x := x) hxα
  rw [← hint] at hev
  have hnod : eval x (Lagrange.nodal S id) ≠ 0 := by
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun α hα ↦ sub_ne_zero.mpr (hxα α hα)
  -- assemble
  let c : L → L := fun α ↦ Lagrange.nodalWeight S id α * eval α rL / lc
  refine ⟨S.toList.map fun α ↦ (c α, x - α), ?_, ?_⟩
  · intro p hp
    obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hp
    rw [Finset.mem_toList] at hα
    refine ⟨?_, sub_ne_zero.mpr (hxα α hα)⟩
    rw [← mem_constants]
    refine div_mem (mul_mem (prod_mem fun β hβ ↦ inv_mem (sub_mem (hconst α hα)
      (hconst β (Finset.mem_of_mem_erase hβ)))) ?_) ?_
    · have := aeval_mem_constants hF r (hconst α hα)
      rwa [aeval_def, eval₂_eq_eval_map] at this
    · rw [hlc, hsL, leadingCoeff_map]; exact hF _
  · have hr : aeval x r = eval x rL := by rw [hrL, aeval_def, eval₂_eq_eval_map]
    have hs : aeval x s = lc * eval x (Lagrange.nodal S id) := by
      rw [aeval_def, eval₂_eq_eval_map, ← hsL, hfac, eval_mul, eval_C]
    rw [hr, hs, hev, List.map_map, Finset.sum_map_toList]
    rw [mul_comm lc, mul_div_mul_left _ _ hnod, Finset.sum_div]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    have hα' : α′ = 0 := hconst α hα
    simp only [Function.comp, logDeriv, map_sub, hx, hα', sub_zero, id, c]
    field_simp

end Differential
