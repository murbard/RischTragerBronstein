import Mathlib.FieldTheory.Differential.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The subfield of constants

`Differential.constants L` is the subfield `{a | a′ = 0}` of a differential field `L`. Closure
under the field operations is what lets residues such as `r(α) / s′(α)` be recognised as constants
without computing their derivatives by hand.
-/

open Polynomial

namespace Differential

variable (L : Type*) [Field L] [Differential L]

/-- The subfield of constants of a differential field. -/
def constants : Subfield L where
  carrier := {a | a′ = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [Derivation.leibniz, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [ha, hb]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp [ha]
  inv_mem' a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp [Derivation.leibniz_inv, ha]

variable {L}

@[simp] lemma mem_constants {a : L} : a ∈ constants L ↔ a′ = 0 := Iff.rfl

/-- A polynomial with constant coefficients takes constant values at constants. -/
lemma aeval_mem_constants {F : Type*} [Field F] [Algebra F L]
    (hF : ∀ a : F, algebraMap F L a ∈ constants L) (p : F[X]) {α : L} (hα : α ∈ constants L) :
    aeval α p ∈ constants L := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact mul_mem (hF _) (pow_mem hα i)

end Differential
