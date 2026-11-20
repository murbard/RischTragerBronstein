import RischTragerBronstein.Computable.LogTimesPositive
import RischTragerBronstein.Computable.LogTimesStrong
import RischTragerBronstein.Computable.ExpPolyDecision

/-!
# `∫ f(x) log x dx` is decided (on certified Hermite data)

In the concrete differential field `R(x)(t) = RatFunc (RatFunc R)` with `x′ = 1`, `t′ = 1 / x`
(`t = log x`): for `f = A / D ∈ R(x)` with certified decomposition `I` (`rationalCheck A D I`),

  `f log x` has an elementary integral  **iff**  `logCrit I.r I.s = true`.

Both directions are proved, with no assumption on constants (`logTimes_decides`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

/-- `1 / x ∈ R(x)`, the derivative of `t = log x`. -/
noncomputable def logEta : RatFunc R := (RatFunc.X : RatFunc R)⁻¹

/-- The integrand `f log x` as an element of `R(x)(t)`. -/
noncomputable def logIntegrand (A D : CPoly R) : RatFunc (RatFunc R) :=
  RatFunc.C (algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D)) *
    RatFunc.X

lemma aeval_C_X (P : R[X]) :
    aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) P =
      RatFunc.C (algebraMap R[X] (RatFunc R) P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, hP, hQ, map_add, map_add]
  | monomial n r =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow,
      map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rfl

theorem logTimes_decides (h0 : ∀ r : R, r′ = 0) (A D : CPoly R) (I : RationalIntegral R)
    (hc : rationalCheck A D I = true) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (logEta (R := R)))
    (logCrit I.r I.s = true → HasElementaryIntegral (logIntegrand A D)) ∧
    (logCrit I.r I.s = false → ¬HasElementaryIntegral (logIntegrand A D)) := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv 1
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (C (logEta (R := R)))
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (logEta (R := R)))
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
      (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R))⁻¹ := by
    rw [ratFuncOfDeriv_X, RatFunc.algebraMap_C, logEta, map_inv₀]
  have hform : logIntegrand A D =
      aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly A) /
        aeval (RatFunc.C (RatFunc.X : RatFunc R) : RatFunc (RatFunc R)) (toPoly D) *
          RatFunc.X := by
    rw [logIntegrand, aeval_C_X, aeval_C_X, map_div₀]
  rw [hform]
  refine ⟨fun hcrit ↦ ?_, fun hcrit ↦ ?_⟩
  · exact hasElementaryIntegral_logTimes h0 _ _ hx' ht' A D I hc ((logCrit_iff _ _).mp hcrit)
  · exact not_hasElementaryIntegral_logTimes hRconst _ _ hx' ht' adjoin_x_t_eq_top A D I hc
      (fun h ↦ by rw [(logCrit_iff _ _).mpr h] at hcrit; exact Bool.noConfusion hcrit)

end CPoly
