import RischTragerBronstein.Computable.ExpPolyStrong

/-!
# `∫ p(x) exp (a(x)) dx` is decided

In the concrete differential field `R(x)(t) = RatFunc (RatFunc R)` with `x′ = 1`, `t′ = a′ t`:

**Theorem** (`integrateExpPoly_decides`). For `deg a ≥ 1`,
`p exp a` has an elementary integral **if and only if** `CPoly.integrateExpPoly p a` returns
`some Y` — and then `∫ p exp a = Y exp a`.

Both directions are proved, with no assumption on constants: the executable procedure is a
verified decision procedure for elementary integrability on this class of integrands.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- `R(x)(t)` is generated over `R` by `x` and `t`. -/
lemma adjoin_x_t_eq_top :
    adjoin R {(RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)), RatFunc.X} = ⊤ := by
  set S := adjoin R {(RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)), RatFunc.X}
  have hx : RatFunc.C (RatFunc.X : RatFunc R) ∈ S := subset_adjoin R _ (by simp)
  have ht : (RatFunc.X : RatFunc (RatFunc R)) ∈ S := subset_adjoin R _ (by simp)
  -- constants of `R(x)`
  have h1 : ∀ P : R[X], RatFunc.C (algebraMap R[X] (RatFunc R) P) ∈ S := fun P ↦ by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => rw [map_add, map_add]; exact add_mem hP hQ
    | monomial n r =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X]
      refine mul_mem ?_ (pow_mem hx n)
      have : RatFunc.C (RatFunc.C r) = algebraMap R (RatFunc (RatFunc R)) r := rfl
      rw [this]
      exact S.algebraMap_mem r
  have h2 : ∀ f : RatFunc R, RatFunc.C f ∈ S := fun f ↦ by
    rw [← f.num_div_denom, map_div₀]
    exact div_mem (h1 _) (h1 _)
  have h3 : ∀ P : (RatFunc R)[X], algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) P ∈ S :=
    fun P ↦ by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | monomial n f =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      exact mul_mem (h2 f) (pow_mem ht n)
  refine eq_top_iff.mpr fun z _ ↦ ?_
  rw [← z.num_div_denom]
  exact div_mem (h3 _) (h3 _)

variable [Differential R]

/-- **Decision theorem** for `∫ p exp a`, `deg a ≥ 1`. -/
theorem integrateExpPoly_decides (h0 : ∀ r : R, r′ = 0) (p a : CPoly R)
    (ha : trim (deriv a) ≠ []) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (expEta a) * X)
    (∀ Y, integrateExpPoly p a = some Y →
        (expIntegrand Y)′ = expIntegrand p ∧ HasElementaryIntegral (expIntegrand p)) ∧
    (integrateExpPoly p a = none → ¬HasElementaryIntegral (expIntegrand p)) := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv 1
  have hDA1 : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (C (expEta a) * X)
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (expEta a) * X)
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  refine ⟨fun Y hY ↦ ?_, fun hnone ↦ ?_⟩
  · have hs := integrateExpPoly_sound h0 hY
    exact ⟨hs, hs ▸ hasElementaryIntegral_of_deriv _⟩
  · -- the abstract theorem, with `x = C X`, `t = X`
    have hRconst : ∀ r : R, (algebraMap R (RatFunc (RatFunc R)) r)′ = 0 := fun r ↦ by
      have : algebraMap R (RatFunc (RatFunc R)) r =
          algebraMap (RatFunc R) (RatFunc (RatFunc R)) (algebraMap R (RatFunc R) r) := rfl
      rw [this, deriv_algebraMap, deriv_algebraMap, h0, map_zero, map_zero]
    have hxform : ∀ P : R[X], aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) P =
        RatFunc.C (algebraMap R[X] (RatFunc R) P) := fun P ↦ by
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ => rw [map_add, hP, hQ, map_add, map_add]
      | monomial n r =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow,
          map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
        rfl
    have hx' : (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R))′ = 1 := by
      rw [← RatFunc.algebraMap_eq_C, deriv_algebraMap, ratFuncOfDeriv_X, map_one, map_one]
    have ht' : (RatFunc.X : RatFunc (RatFunc R))′ =
        aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R))
          (derivative (toPoly a)) * RatFunc.X := by
      rw [ratFuncOfDeriv_X, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X, hxform]
      rfl
    have := not_hasElementaryIntegral_of_integrateExpPoly_none (K := RatFunc (RatFunc R)) hRconst
      (RatFunc.C RatFunc.X) RatFunc.X hx' RatFunc.X_ne_zero a p ht' adjoin_x_t_eq_top ha hnone
    rwa [hxform] at this

end CPoly
