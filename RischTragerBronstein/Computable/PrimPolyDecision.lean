import RischTragerBronstein.Computable.PrimPolyExample
import RischTragerBronstein.Computable.LogTimesDecision

/-!
# Polynomials in a primitive over `R(x)`: decided

In the concrete differential field `R(x)(t) = RatFunc (RatFunc R)` with `x′ = 1`,
`t′ = η = En / Ed ∈ R(x)` (with certified Hermite data `Iη`, `Iη.r ≠ 0`, i.e. `η` has no rational
antiderivative — e.g. `t = log b(x)`): for `fⱼ = Aⱼ / Dⱼ ∈ R(x)`,

  `∑_{j ≤ d} fⱼ t ^ j` has an elementary integral  **iff**  `primLoop` succeeds.

Both directions are proved, with no assumption on constants (`primPoly_decides`), and the example
`∫ log² x / (x + 1) dx` is refuted by kernel computation.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

/-- `η = En / Ed ∈ R(x)`, the derivative of `t`. -/
noncomputable def primEta (En Ed : CPoly R) : RatFunc R :=
  algebraMap R[X] (RatFunc R) (toPoly En) / algebraMap R[X] (RatFunc R) (toPoly Ed)

/-- The integrand `∑_{j ≤ d} fⱼ t ^ j` as an element of `R(x)(t)`. -/
noncomputable def primPolyIntegrand (A D : ℕ → CPoly R) (d : ℕ) : RatFunc (RatFunc R) :=
  ∑ j ∈ Finset.range (d + 1),
    RatFunc.C (algebraMap R[X] (RatFunc R) (toPoly (A j)) /
      algebraMap R[X] (RatFunc R) (toPoly (D j))) * RatFunc.X ^ j

theorem primPoly_decides (h0 : ∀ r : R, r′ = 0) (En Ed : CPoly R) (Iη : RationalIntegral R)
    (hcη : rationalCheck En Ed Iη = true) (hη0 : isZero Iη.r = false)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En Ed))
    ((primLoop En Ed Iη A D d ([], [1])).isSome = true →
      HasElementaryIntegral (primPolyIntegrand A D d)) ∧
    (primLoop En Ed Iη A D d ([], [1]) = none →
      ¬HasElementaryIntegral (primPolyIntegrand A D d)) := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv 1
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (C (primEta En Ed))
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En Ed))
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hRconst : ∀ r : R, (algebraMap R (RatFunc (RatFunc R)) r)′ = 0 := fun r ↦ by
    have : algebraMap R (RatFunc (RatFunc R)) r =
        algebraMap (RatFunc R) (RatFunc (RatFunc R)) (algebraMap R (RatFunc R) r) := rfl
    rw [this, deriv_algebraMap, deriv_algebraMap, h0, map_zero, map_zero]
  have hDAR : DifferentialAlgebra R (RatFunc (RatFunc R)) :=
    ⟨fun r ↦ by rw [hRconst, h0, map_zero]⟩
  have hx' : (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R))′ = 1 := by
    rw [← RatFunc.algebraMap_eq_C, deriv_algebraMap, ratFuncOfDeriv_X, map_one, map_one]
  have ht' : (RatFunc.X : RatFunc (RatFunc R))′ =
      aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly En) /
        aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly Ed) := by
    rw [ratFuncOfDeriv_X, RatFunc.algebraMap_C, primEta, map_div₀, aeval_C_X, aeval_C_X]
  have hform : primPolyIntegrand A D d = ∑ j ∈ Finset.range (d + 1),
      aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly (A j)) /
        aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly (D j)) *
          RatFunc.X ^ j := by
    rw [primPolyIntegrand]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [aeval_C_X, aeval_C_X, map_div₀]
  rw [hform]
  refine ⟨fun hsome ↦ ?_, fun hnone ↦ ?_⟩
  · obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
    exact hasElementaryIntegral_primPoly h0 _ _ hx' En Ed ht' Iη hcη d A D hD0 hL
  · exact not_hasElementaryIntegral_primPoly hRconst _ _ hx' En Ed ht' adjoin_x_t_eq_top Iη hcη
      hη0 d A D (fun j _ hj ↦ hD0 j hj) hnone

namespace PrimPolyExample

local instance : Differential ℚ := ⟨0⟩

/-- **`∫ log² x / (x + 1) dx` is not elementary**, in `ℚ(x)(log x)`. -/
theorem log_sq_div_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    ¬HasElementaryIntegral (primPolyIntegrand A₁ D₂ 2) :=
  (primPoly_decides (fun _ ↦ rfl) En Ed Iη check_η η_not_derivative 2 A₁ D₂ (fun j _ ↦ by
    unfold D₂
    split_ifs
    · intro h
      have := congrArg (fun p : ℚ[X] ↦ p.coeff 1) h
      simp [coeff_one] at this
    · simp)).2 loop_log_sq_div

/-- **`∫ log² x dx` is elementary**, in `ℚ(x)(log x)`. -/
theorem log_sq_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    HasElementaryIntegral (primPolyIntegrand A₁ D₁ 2) :=
  (primPoly_decides (fun _ ↦ rfl) En Ed Iη check_η η_not_derivative 2 A₁ D₁ (fun j _ ↦ by
    simp [D₁])).1 loop_log_sq

end PrimPolyExample

end CPoly
