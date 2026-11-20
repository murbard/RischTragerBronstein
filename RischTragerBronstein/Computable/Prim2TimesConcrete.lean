import RischTragerBronstein.Computable.Prim2TimesDecision
import RischTragerBronstein.Computable.PrimPolyDecision

/-!
# Height three, concretely: `R(x)(t₁)(t₂) = RatFunc (RatFunc (RatFunc R))`

The decision theorem `integratePrim2Times_decides` instantiated in the concrete tower
`x′ = 1`, `t₁′ = η₁(x)`, `t₂′ = η₂(x)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

/-- The integrand `(∑_{j ≤ d} aⱼ(x) t₁ ^ j) t₂`. -/
noncomputable def prim2Integrand (A D : ℕ → CPoly R) (d : ℕ) :
    RatFunc (RatFunc (RatFunc R)) :=
  RatFunc.C (∑ j ∈ Finset.range (d + 1),
    RatFunc.C (algebraMap R[X] (RatFunc R) (toPoly (A j)) /
      algebraMap R[X] (RatFunc R) (toPoly (D j))) * RatFunc.X ^ j) * RatFunc.X

theorem prim2Times_decides_concrete (h0 : ∀ r : R, r′ = 0) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En₁ Ed₁))
    letI : Differential (RatFunc (RatFunc (RatFunc R))) :=
      ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    HasElementaryIntegral (prim2Integrand A D d) ↔
      integratePrim2Times En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A D d = true := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv 1
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (C (primEta En₁ Ed₁))
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En₁ Ed₁))
  have hDA1 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  let _ : Differential (RatFunc (RatFunc R))[X] :=
    polynomialOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
  let _ : Differential (RatFunc (RatFunc (RatFunc R))) :=
    ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
  have hDA2 : DifferentialAlgebra (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hR : ∀ r : R, (algebraMap R (RatFunc (RatFunc R)) r)′ = 0 := fun r ↦ by
    have : algebraMap R (RatFunc (RatFunc R)) r =
        algebraMap (RatFunc R) (RatFunc (RatFunc R)) (algebraMap R (RatFunc R) r) := rfl
    rw [this, deriv_algebraMap, deriv_algebraMap, h0, map_zero, map_zero]
  have hx₀ : (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R))′ = 1 := by
    rw [← RatFunc.algebraMap_eq_C, deriv_algebraMap, ratFuncOfDeriv_X, map_one, map_one]
  have ht₁ : (RatFunc.X : RatFunc (RatFunc R))′ =
      aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly En₁) /
        aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly Ed₁) := by
    rw [ratFuncOfDeriv_X, RatFunc.algebraMap_C, primEta, map_div₀, aeval_C_X, aeval_C_X]
  have ht : (RatFunc.X : RatFunc (RatFunc (RatFunc R)))′ =
      algebraMap (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R)))
        (aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly En₂) /
          aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly Ed₂)) := by
    rw [ratFuncOfDeriv_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, aeval_C_X, aeval_C_X,
      ← map_div₀, primEta]
  have key := integratePrim2Times_decides (R := R) (F₀ := RatFunc (RatFunc R))
    (K := RatFunc (RatFunc (RatFunc R))) hR (RatFunc.C RatFunc.X) RatFunc.X hx₀ En₁ Ed₁ En₂ Ed₂
    ht₁ adjoin_x_t_eq_top RatFunc.X RatFunc.adjoin_X ht Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep d A D hD0
  have hform : prim2Integrand A D d =
      algebraMap (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R)))
        (∑ j ∈ Finset.range (d + 1),
          aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly (A j)) /
            aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly (D j)) *
              RatFunc.X ^ j) * RatFunc.X := by
    rw [prim2Integrand, RatFunc.algebraMap_eq_C]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [aeval_C_X, aeval_C_X, map_div₀]
  rw [hform]
  exact key

namespace Prim2Example

open PrimPolyExample

local instance : Differential ℚ := ⟨0⟩

/-- `η₂ = 1 / (x + 1)`. -/
def En₂ : CPoly ℚ := [1]
/-- `η₂ = 1 / (x + 1)`. -/
def Ed₂ : CPoly ℚ := [1, 1]
/-- Hermite data of `η₂`. -/
def Iη₂ : RationalIntegral ℚ := integrateRational En₂ Ed₂

/-- The coefficients of `A = t₁`. -/
def A₁ : ℕ → CPoly ℚ := fun j ↦ if j = 1 then [1] else []
/-- All denominators `1`. -/
def D₁ : ℕ → CPoly ℚ := fun _ ↦ [1]

theorem check_η₂ : rationalCheck En₂ Ed₂ Iη₂ = true := by decide +kernel

theorem indep : limitedCrit Iη₂.r Iη₂.s Iη.r Iη.s = none := by decide +kernel

theorem run_log_mul_log :
    integratePrim2Times En Ed Iη En₂ Ed₂ Iη₂ A₁ D₁ 1 = false := by decide +kernel

/-- **`∫ log x · log (x + 1) dx` is not elementary**, in `ℚ(x)(log x)(log (x + 1))`: a verified
decision at tower height three. -/
theorem log_mul_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential (RatFunc (RatFunc (RatFunc ℚ))) :=
      ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    ¬HasElementaryIntegral (prim2Integrand A₁ D₁ 1) := by
  have := prim2Times_decides_concrete (R := ℚ) (fun _ ↦ rfl) En Ed En₂ Ed₂ Iη Iη₂ check_η check_η₂
    η_not_derivative indep 1 A₁ D₁ (fun j _ ↦ by simp [D₁])
  intro h
  have h2 := this.mp h
  rw [run_log_mul_log] at h2
  exact Bool.noConfusion h2

end Prim2Example

end CPoly
