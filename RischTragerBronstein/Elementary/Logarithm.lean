import RischTragerBronstein.Elementary.Defs
import RischTragerBronstein.Differential.Monomial
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Logarithmic derivatives have elementary integrals

For nonzero `a ∈ F`, the element `a′ / a` has an elementary integral over `F`, namely `log a`.
The content is the *construction* of `log a`: the monomial extension `F(t)` with `t′ = a′ / a`
is an elementary extension of `F`, and `t` is the antiderivative.

Besides being the easy half of Liouville's theorem, this validates the specification in
`Elementary/Defs.lean` against the constructions in `Differential/Monomial.lean`.
-/

open Polynomial IntermediateField

namespace Differential

universe u

variable {F : Type u} [Field F] [Differential F]

/-- The logarithmic extension `F(t)`, `t′ = a′ / a`, is an elementary extension of `F`. -/
theorem isElementaryExtension_log (a : F) (ha : a ≠ 0) :
    letI := ratFuncOfDeriv (C (logDeriv a))
    letI := differentialAlgebra_ratFuncOfDeriv (C (logDeriv a))
    IsElementaryExtension F (RatFunc F) ∧
      (RatFunc.X : RatFunc F)′ = algebraMap F (RatFunc F) (logDeriv a) := by
  let _ : Differential (RatFunc F) := ratFuncOfDeriv (C (logDeriv a))
  have hDA : DifferentialAlgebra F (RatFunc F) := differentialAlgebra_ratFuncOfDeriv _
  have hX : (RatFunc.X : RatFunc F)′ = algebraMap F (RatFunc F) (logDeriv a) := by
    rw [ratFuncOfDeriv_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  refine ⟨?_, hX⟩
  have hlog : IsElementaryOver (⊥ : IntermediateField F (RatFunc F)) RatFunc.X := by
    refine Or.inr (Or.inl ⟨algebraMap F (RatFunc F) a, (⊥ : IntermediateField F _).algebraMap_mem a,
      ?_, ?_⟩)
    · simpa using ha
    · rw [hX, logDeriv_algebraMap]
  have htop : (⊥ : IntermediateField F (RatFunc F)) ⊔ F⟮(RatFunc.X : RatFunc F)⟯ = ⊤ := by
    rw [RatFunc.adjoin_X, bot_sup_eq]
  unfold IsElementaryExtension
  rw [← htop]
  exact IsElementaryTower.adjoin ⊥ RatFunc.X IsElementaryTower.base hlog

/-- `∫ a′ / a = log a` is elementary. -/
theorem hasElementaryIntegral_logDeriv (a : F) (ha : a ≠ 0) :
    HasElementaryIntegral (logDeriv a) := by
  let _ : Differential (RatFunc F) := ratFuncOfDeriv (C (logDeriv a))
  have hDA : DifferentialAlgebra F (RatFunc F) := differentialAlgebra_ratFuncOfDeriv _
  obtain ⟨hE, hX⟩ := isElementaryExtension_log a ha
  exact ⟨RatFunc F, inferInstance, inferInstance, inferInstance, hDA, hE, RatFunc.X, hX⟩

end Differential
