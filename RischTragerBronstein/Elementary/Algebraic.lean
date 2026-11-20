import RischTragerBronstein.Elementary.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Algebraic extensions are elementary; algebraic constants

* `isElementaryExtension_of_finiteDimensional`: a finite extension of differential fields is an
  elementary extension (a tower of algebraic adjunctions).
* `deriv_eq_zero_of_aeval_eq_zero`: a simple root of a polynomial with constant coefficients is a
  constant. This is how the new constants produced by the Rothstein–Trager resultant are recognised
  as constants.
-/

open IntermediateField Polynomial

namespace Differential

section Tower

variable {K L : Type*} [Field K] [Field L] [Differential L] [Algebra K L]

/-- Adjoining finitely many algebraic elements gives an elementary tower. -/
lemma isElementaryTower_adjoin_finset (S : Finset L) (hS : ∀ t ∈ S, IsAlgebraic K t) :
    IsElementaryTower (adjoin K (S : Set L)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [adjoin_empty] using IsElementaryTower.base
  | insert t S _ ih =>
    have h : adjoin K ((insert t S : Finset L) : Set L) = adjoin K (S : Set L) ⊔ K⟮t⟯ := by
      rw [Finset.coe_insert, Set.insert_eq, adjoin_union, sup_comm]
    rw [h]
    refine .adjoin _ _ (ih fun x hx ↦ hS x (Finset.mem_insert_of_mem hx)) (Or.inl ?_)
    exact (hS t (Finset.mem_insert_self t S)).tower_top _

/-- A finite extension of differential fields is elementary. -/
theorem isElementaryExtension_of_finiteDimensional [FiniteDimensional K L] :
    IsElementaryExtension K L := by
  obtain ⟨S, hS⟩ := fg_of_noetherian (⊤ : IntermediateField K L)
  unfold IsElementaryExtension
  rw [← hS]
  exact isElementaryTower_adjoin_finset S fun t _ ↦ Algebra.IsAlgebraic.isAlgebraic t

end Tower

section Constants

variable {A R : Type*} [CommRing A] [Differential A] [CommRing R] [IsDomain R] [Differential R]
variable [Algebra A R] [DifferentialAlgebra A R]

/-- A simple root of a polynomial with constant coefficients is a constant. -/
theorem deriv_eq_zero_of_aeval_eq_zero (p : A[X]) (hp : ∀ i, (p.coeff i)′ = 0) (α : R)
    (hα : aeval α p = 0) (hα' : aeval α (derivative p) ≠ 0) : α′ = 0 := by
  have h := deriv_aeval_eq α p
  have hmc : mapCoeffs p = 0 := by ext i; simp [hp]
  rw [hα, hmc] at h
  simp only [map_zero, zero_add] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hα'

end Constants

end Differential
