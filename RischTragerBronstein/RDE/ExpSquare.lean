import RischTragerBronstein.RDE.ExpPolynomial
import RischTragerBronstein.Rational.Integrable
import RischTragerBronstein.Liouville.Tower

/-!
# `exp (x²)`: the concrete model

Instantiation of `exp_polynomial_no_liouville_form` in the concrete tower
`C ⊂ C(x) = RatFunc C ⊂ C(x)(t) = RatFunc (RatFunc C)`, with `x′ = 1` and `t′ = 2 x t`, so that
`t = exp (x²)`. This shows that the hypotheses of the abstract theorem are satisfiable, and gives
the statement in its familiar form:

**`exp (x²)` is not of the form `∑ cᵢ uᵢ′ / uᵢ + v′` with `uᵢ, v ∈ C(x, exp (x²))`, `cᵢ ∈ C(x)`.**
-/

open Polynomial Finset

namespace Differential

variable {C' : Type*} [Field C'] [CharZero C'] [Differential C']

/-- `2x ∈ C(x)`, the logarithmic derivative of `exp (x²)`. -/
noncomputable def twoX : RatFunc C' := algebraMap C'[X] (RatFunc C') (derivative (X ^ 2))

theorem exp_sq_no_liouville_form (h0 : ∀ a : C', a′ = 0)
    {ι : Type*} (s : Finset ι) (c : ι → RatFunc C') (u : ι → RatFunc (RatFunc C'))
    (hu : ∀ i ∈ s, u i ≠ 0) (v : RatFunc (RatFunc C')) :
    letI : Differential (RatFunc C') := ratFuncOfDeriv (1 : C'[X])
    letI : Differential (RatFunc (RatFunc C')) := ratFuncOfDeriv (C (twoX (C' := C')) * X)
    (RatFunc.X : RatFunc (RatFunc C')) ≠
      ∑ i ∈ s, RatFunc.C (c i) * logDeriv (u i) + v′ := by
  let _ : Differential C'[X] := polynomialOfDeriv (1 : C'[X])
  let _ : Differential (RatFunc C') := ratFuncOfDeriv (1 : C'[X])
  have hDA1 : DifferentialAlgebra C'[X] (RatFunc C') := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc C')[X] := polynomialOfDeriv (C (twoX (C' := C')) * X)
  let _ : Differential (RatFunc (RatFunc C')) := ratFuncOfDeriv (C (twoX (C' := C')) * X)
  have hDA2 : DifferentialAlgebra (RatFunc C')[X] (RatFunc (RatFunc C')) :=
    differentialAlgebra_ofFractionRing _ _
  have key := exp_polynomial_no_liouville_form (C' := C') (F := RatFunc C')
    (K := RatFunc (RatFunc C')) (fun P ↦ implicitDeriv_one_of_trivial h0 P) (X ^ 2)
    (by rw [natDegree_X_pow]) (fun _ ↦ rfl) s c u hu v
  rw [RatFunc.algebraMap_X] at key
  simpa only [RatFunc.algebraMap_C] using key

/-- **`exp (x²)` has no elementary antiderivative** in any elementary extension of
`C(x, exp (x²))` with the same constants. -/
theorem exp_sq_not_elementary (h0 : ∀ a : C', a′ = 0) :
    letI : Differential (RatFunc C') := ratFuncOfDeriv (1 : C'[X])
    letI : Differential (RatFunc (RatFunc C')) := ratFuncOfDeriv (C (twoX (C' := C')) * X)
    ∀ (E : Type*) [Field E] [Differential E] [Algebra (RatFunc (RatFunc C')) E]
      [DifferentialAlgebra (RatFunc (RatFunc C')) E],
      (∀ x : E, x′ = 0 → x ∈ Set.range (algebraMap (RatFunc (RatFunc C')) E)) →
      IsElementaryExtension (RatFunc (RatFunc C')) E →
      ∀ g : E, g′ ≠ algebraMap (RatFunc (RatFunc C')) E RatFunc.X := by
  let _ : Differential C'[X] := polynomialOfDeriv (1 : C'[X])
  let _ : Differential (RatFunc C') := ratFuncOfDeriv (1 : C'[X])
  have hDA1 : DifferentialAlgebra C'[X] (RatFunc C') := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc C')[X] := polynomialOfDeriv (C (twoX (C' := C')) * X)
  let _ : Differential (RatFunc (RatFunc C')) := ratFuncOfDeriv (C (twoX (C' := C')) * X)
  have hDA2 : DifferentialAlgebra (RatFunc C')[X] (RatFunc (RatFunc C')) :=
    differentialAlgebra_ofFractionRing _ _
  intro E _ _ _ _ hconst hE g hg
  obtain ⟨ι, s, c, u, v, hdata, heq⟩ := liouville_of_isElementaryExtension hconst hE _ g hg
  -- the constants of `C(x, exp x²)` lie in `C(x)`
  have hpoly := exp_polynomial_no_new_constants (C' := C') (F := RatFunc C')
    (fun P ↦ implicitDeriv_one_of_trivial h0 P) (X ^ 2) (by rw [natDegree_X_pow]; norm_num)
    (fun _ ↦ rfl)
  choose! e he using fun i (hi : i ∈ s) ↦
    constant_of_exponential (K := RatFunc (RatFunc C')) (twoX (C' := C')) (fun _ ↦ rfl) hpoly
      (c i) (hdata i hi).1
  refine exp_sq_no_liouville_form h0 s e u (fun i hi ↦ (hdata i hi).2) v ?_
  rw [heq]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [he i hi, RatFunc.algebraMap_C]

end Differential
