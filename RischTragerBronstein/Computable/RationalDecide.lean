import RischTragerBronstein.Computable.Rational
import RischTragerBronstein.Rational.RationalPart

/-!
# Deciding whether `∫ A / D` is a rational function

`rationalCheck_rational_iff`: if the certificate of the rational integrator passes, then `A / D` has
an antiderivative **in `R(x)`** if and only if the logarithmic numerator `r` of the output is zero.
Both directions are proved, so on certified outputs the integrator decides rationality of the
integral, and its logarithmic part is never spurious.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

/-- `(a - b)′ = a′ - b′`, for use at types with a non-canonical `ℤ`-algebra structure. -/
lemma deriv_sub' {S : Type*} [CommRing S] [Differential S] (a b : S) : (a - b)′ = a′ - b′ :=
  map_sub _ _ _

theorem rationalCheck_rational_iff (h0 : ∀ a : R, a′ = 0) (A D : CPoly R)
    (I : RationalIntegral R) (hc : rationalCheck A D I = true) :
    letI := ratFuncOfDeriv (1 : R[X])
    (∃ y : RatFunc R, y′ =
      algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D)) ↔
    isZero I.r = true := by
  let _ := polynomialOfDeriv (1 : R[X])
  let _ := ratFuncOfDeriv (1 : R[X])
  have hDAP : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  obtain ⟨hmain, hsq, hdeg, -⟩ := rationalCheck_sound h0 A D I hc
  rw [isZero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine eq_zero_of_deriv_eq_proper_fraction (K := RatFunc R)
      (fun P ↦ implicitDeriv_one_of_trivial h0 P) _ _ hsq hdeg
      (y - (algebraMap R[X] (RatFunc R) (toPoly I.gn) / algebraMap R[X] (RatFunc R) (toPoly I.gd) +
        algebraMap R[X] (RatFunc R) (toPoly I.Q))) ?_
    rw [deriv_sub', hy, hmain]
    ring
  · intro hr
    refine ⟨algebraMap R[X] (RatFunc R) (toPoly I.gn) / algebraMap R[X] (RatFunc R) (toPoly I.gd) +
      algebraMap R[X] (RatFunc R) (toPoly I.Q), ?_⟩
    rw [hmain, hr, map_zero, zero_div, add_zero]

end CPoly
