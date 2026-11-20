import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Elementary extensions and elementary integrability: the specification

This file fixes what the rest of the development is *about*. Every soundness theorem
("the output is an antiderivative") and every completeness theorem ("no output means no elementary
antiderivative exists") is a statement in terms of `HasElementaryIntegral` below, so the definitions
follow the literature verbatim: Bronstein, *Symbolic Integration I*, Definitions 5.1.1–5.1.3, which
agree with Rosenlicht and Risch.

Let `K / F` be an extension of differential fields.

* `t ∈ K` is *elementary over* a subfield `E` if it is algebraic over `E`, or a logarithm of an
  element of `E` (`t′ = a′ / a`), or an exponential of one (`t′ / t = a′`).
* `K` is an *elementary extension* of `F` if `K = F(t₁, …, tₙ)` with each `tᵢ` elementary over
  `F(t₁, …, tᵢ₋₁)`.
* `f ∈ F` *has an elementary integral over `F`* if some elementary extension of `F` contains an
  antiderivative of `f`.

No hypothesis on constants is built in: the extension is allowed to enlarge the constant field,
exactly as in the literature (this is what makes `∫ 1/(x²+1)` elementary over `ℚ(x)`).
-/

open Differential IntermediateField

universe u

variable {F : Type u} {K : Type*} [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K]

namespace Differential

/-- `t` is a logarithm over `E`: `t′ = a′ / a` for some nonzero `a ∈ E`. -/
def IsLogarithmOver (E : IntermediateField F K) (t : K) : Prop :=
  ∃ a ∈ E, a ≠ 0 ∧ t′ = logDeriv a

/-- `t` is an exponential over `E`: `t ≠ 0` and `t′ / t = a′` for some `a ∈ E`. -/
def IsExponentialOver (E : IntermediateField F K) (t : K) : Prop :=
  t ≠ 0 ∧ ∃ a ∈ E, logDeriv t = a′

/-- `t` is elementary over `E`: algebraic, a logarithm, or an exponential (Bronstein 5.1.1). -/
def IsElementaryOver (E : IntermediateField F K) (t : K) : Prop :=
  IsAlgebraic E t ∨ IsLogarithmOver E t ∨ IsExponentialOver E t

/-- The intermediate fields of `K / F` reachable from `F` by finitely many adjunctions of
elementary elements (Bronstein 5.1.2). -/
inductive IsElementaryTower : IntermediateField F K → Prop
  | base : IsElementaryTower ⊥
  | adjoin (E : IntermediateField F K) (t : K) :
      IsElementaryTower E → IsElementaryOver E t → IsElementaryTower (E ⊔ F⟮t⟯)

variable (F K) in
/-- `K` is an elementary extension of `F`. -/
def IsElementaryExtension : Prop := IsElementaryTower (⊤ : IntermediateField F K)

/-- `f ∈ F` has an elementary integral over `F` (Bronstein 5.1.3): there are an elementary
extension `K` of `F` and `g ∈ K` with `g′ = f`. -/
def HasElementaryIntegral (f : F) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Differential K) (_ : Algebra F K)
    (_ : DifferentialAlgebra F K),
    IsElementaryExtension F K ∧ ∃ g : K, g′ = algebraMap F K f

/-- Sanity check of the specification: anything with an antiderivative already in `F` has an
elementary integral, witnessed by the trivial tower. -/
theorem hasElementaryIntegral_of_deriv (g : F) : HasElementaryIntegral g′ := by
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, ?_, g, rfl⟩
  have h : (⊥ : IntermediateField F F) = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ IntermediateField.mem_bot.mpr ⟨x, rfl⟩
  unfold IsElementaryExtension
  rw [← h]
  exact IsElementaryTower.base

end Differential
