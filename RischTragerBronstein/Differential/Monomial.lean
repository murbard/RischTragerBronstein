import RischTragerBronstein.Differential.FractionField
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Derivative

open Polynomial

namespace Differential

variable {F : Type*} [Field F] [Differential F]

/-- The differential structure on `F[t]` with `t′ = v`. -/
@[reducible] noncomputable def polynomialOfDeriv (v : F[X]) : Differential F[X] := ⟨implicitDeriv v⟩

/-- The differential structure on `F(t)` with `t′ = v`: the monomial extension. -/
@[reducible] noncomputable def ratFuncOfDeriv (v : F[X]) : Differential (RatFunc F) :=
  letI := polynomialOfDeriv v
  ofFractionRing F[X] (RatFunc F)

lemma ratFuncOfDeriv_algebraMap (v p : F[X]) :
    letI := ratFuncOfDeriv v
    (algebraMap F[X] (RatFunc F) p)′ = algebraMap F[X] (RatFunc F) (implicitDeriv v p) :=
  letI := polynomialOfDeriv v
  ofFractionRing_deriv_algebraMap F[X] (RatFunc F) p

lemma ratFuncOfDeriv_X (v : F[X]) :
    letI := ratFuncOfDeriv v
    (RatFunc.X : RatFunc F)′ = algebraMap F[X] (RatFunc F) v := by
  rw [← RatFunc.algebraMap_X, ratFuncOfDeriv_algebraMap, implicitDeriv_X]

/-- `F → F(t)` is a morphism of differential fields. -/
lemma differentialAlgebra_ratFuncOfDeriv (v : F[X]) :
    letI := ratFuncOfDeriv v
    DifferentialAlgebra F (RatFunc F) :=
  letI := ratFuncOfDeriv v
  ⟨fun a ↦ by
    rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ratFuncOfDeriv_algebraMap,
      implicitDeriv_C, RatFunc.algebraMap_C]⟩

section Base

/-- With the trivial derivation on `F` and `t′ = 1`, the derivation of `F[t]` is `d/dt`. -/
lemma implicitDeriv_one_of_trivial (h : ∀ a : F, a′ = 0) (p : F[X]) :
    implicitDeriv 1 p = derivative p := by
  have : mapCoeffs p = 0 := by ext i; simp [h]
  simp [implicitDeriv, this]

variable [CharZero F]

/-- **Constants of `K(x)`.** If `F` has the trivial derivation and characteristic zero, the
constants of `(F(x), d/dx)` are exactly `F`. -/
theorem ratFunc_constants (h : ∀ a : F, a′ = 0) (f : RatFunc F) :
    letI := ratFuncOfDeriv (1 : F[X])
    f′ = 0 ↔ f ∈ Set.range (algebraMap F (RatFunc F)) := by
  let _ := ratFuncOfDeriv (1 : F[X])
  have := differentialAlgebra_ratFuncOfDeriv (1 : F[X])
  constructor
  · intro hf
    set p := f.num with hp
    set q := f.denom with hq
    have hq0 : q ≠ 0 := f.denom_ne_zero
    have hq0' : algebraMap F[X] (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero hq0
    have hcop : IsCoprime p q := f.isCoprime_num_denom
    -- the quotient rule, cleared of denominators
    have key : derivative p * q = p * derivative q := by
      rw [← f.num_div_denom] at hf
      have := (letI := polynomialOfDeriv (1 : F[X])
        ofFractionRing_deriv_div_eq_zero_iff F[X] (RatFunc F) p q hq0).mp hf
      change implicitDeriv 1 p * q = p * implicitDeriv 1 q at this
      rwa [implicitDeriv_one_of_trivial h, implicitDeriv_one_of_trivial h] at this
    -- `q ∣ q′`, hence `q′ = 0`, hence `q` is constant, hence `q = 1`
    have hdq : q ∣ derivative q :=
      hcop.symm.dvd_of_dvd_mul_left ⟨derivative p, by rw [← key]; ring⟩
    have hq' : derivative q = 0 := by
      by_contra hne
      have hdeg := natDegree_le_of_dvd hdq hne
      have hpos : q.natDegree ≠ 0 := by
        intro h0
        rw [eq_C_of_natDegree_eq_zero h0] at hne
        simp at hne
      exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr hdeg)
    have hq1 : q = 1 := by
      have h0 := derivative_eq_zero.mp hq'
      have hm : q.Monic := f.monic_denom
      exact hm.natDegree_eq_zero.mp h0
    have hp' : derivative p = 0 := by
      have := key
      rw [hq1] at this
      simpa using this
    have hpC := eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hp')
    refine ⟨p.coeff 0, ?_⟩
    rw [← f.num_div_denom, ← hp, ← hq, hq1, hpC]
    simp [RatFunc.algebraMap_eq_C]
  · rintro ⟨a, rfl⟩
    rw [deriv_algebraMap, h, map_zero]

end Base

end Differential

/-!
# Monomial extensions `F(t)` of a differential field `F`, with `t′ = v ∈ F[t]` (Bronstein, §3.4),
and the base case `K(x)`, `d/dx`, whose field of constants is `K`.
-/
