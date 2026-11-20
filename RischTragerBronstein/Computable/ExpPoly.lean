import RischTragerBronstein.Computable.RDEPoly
import RischTragerBronstein.RDE.ExpPolynomial
import RischTragerBronstein.Liouville.Tower

/-!
# A verified decision procedure for `∫ p(x) exp (a(x)) dx`

For polynomials `p, a` over a computable field `R` of characteristic zero (constants), with
`deg a ≥ 1`, the function `CPoly.integrateExpPoly p a` either returns a polynomial `Y` or `none`.

The differential field is the concrete tower `R(x)(t) = RatFunc (RatFunc R)`, `x′ = 1`,
`t′ = a′ t`, so `t = exp a`, and the integrand `p exp a` is the element `C p * X`.

* `integrateExpPoly_sound`: if the answer is `some Y`, then `(Y t)′ = p t`:
  `∫ p exp a = Y exp a`.
* `integrateExpPoly_none`: if the answer is `none`, then `p exp a` has **no antiderivative in any
  elementary extension of `R(x, exp a)` with the same constants**.

This is the exponential case of the Risch algorithm for this class of integrands, with both
outcomes carrying proofs. The negative branch combines: Liouville's theorem along the tower
(`liouville_of_isElementaryExtension`), the structure of Liouville identities in exponential
extensions (`exists_poly_rde_solution_of_liouville`), and completeness of the solver
(`rdeSolve_complete`).
-/

open Polynomial Finset

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- Integrate `p exp a`: solve `Y′ + a′ Y = p`. -/
def integrateExpPoly (p a : CPoly R) : Option (CPoly R) := rdeSolve (deriv a) p

variable [CharZero R] [Differential R]

open Differential

/-- `a′ ∈ R(x)`, the logarithmic derivative of `t = exp a`. -/
noncomputable def expEta (a : CPoly R) : RatFunc R :=
  algebraMap R[X] (RatFunc R) (derivative (toPoly a))

/-- The integrand `p exp a` as an element of `R(x)(t)`. -/
noncomputable def expIntegrand (p : CPoly R) : RatFunc (RatFunc R) :=
  RatFunc.C (algebraMap R[X] (RatFunc R) (toPoly p)) * RatFunc.X

theorem integrateExpPoly_sound (h0 : ∀ r : R, r′ = 0) {p a Y : CPoly R}
    (h : integrateExpPoly p a = some Y) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (expEta a) * X)
    (expIntegrand Y)′ = expIntegrand p := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA1 : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (C (expEta a) * X)
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (expEta a) * X)
  have hDA2 : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have hsol := rdeSolve_sound h
  rw [toPoly_deriv] at hsol
  set φ₁ := algebraMap R[X] (RatFunc R)
  have hform : ∀ q : CPoly R, expIntegrand q =
      algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (C (φ₁ (toPoly q)) * X) := fun q ↦ by
    rw [expIntegrand, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hY' : (φ₁ (toPoly Y))′ = φ₁ (derivative (toPoly Y)) := by
    rw [deriv_algebraMap (A := R[X]) (B := RatFunc R)]
    change φ₁ (implicitDeriv 1 (toPoly Y)) = _
    rw [implicitDeriv_one_of_trivial h0]
  rw [hform, hform, deriv_algebraMap (A := (RatFunc R)[X]) (B := RatFunc (RatFunc R))]
  have hkey : implicitDeriv (C (expEta a) * X) (C (φ₁ (toPoly Y)) * X) =
      C (φ₁ (toPoly p)) * X := by
    rw [implicitDeriv_C_mul_X, hY', ← hsol, expEta]
    simp only [map_add, map_mul]
    rfl
  exact congrArg (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R))) hkey

theorem integrateExpPoly_none (h0 : ∀ r : R, r′ = 0) {p a : CPoly R}
    (ha : trim (deriv a) ≠ []) (h : integrateExpPoly p a = none) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (expEta a) * X)
    ∀ (E : Type*) [Field E] [Differential E] [Algebra (RatFunc (RatFunc R)) E]
      [DifferentialAlgebra (RatFunc (RatFunc R)) E],
      (∀ x : E, x′ = 0 → x ∈ Set.range (algebraMap (RatFunc (RatFunc R)) E)) →
      IsElementaryExtension (RatFunc (RatFunc R)) E →
      ∀ g : E, g′ ≠ algebraMap (RatFunc (RatFunc R)) E (expIntegrand p) := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA1 : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (C (expEta a) * X)
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (expEta a) * X)
  have hDA2 : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  intro E _ _ _ _ hconst hE g hg
  -- `deg a ≥ 1`
  have hdeg : 1 ≤ (toPoly a).natDegree := by
    obtain ⟨-, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil ha
    by_contra hlt
    have h0' : (toPoly a).natDegree = 0 := by omega
    rw [toPoly_deriv, derivative_eq_zero.mpr h0', coeff_zero] at hlc
    exact hlc0 hlc.symm
  have hDC : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  -- Liouville's theorem along the tower
  obtain ⟨ι, s, c, u, v, hdata, heq⟩ := liouville_of_isElementaryExtension hconst hE _ g hg
  have hpoly := exp_polynomial_no_new_constants (C' := R) (F := RatFunc R) hDC (toPoly a) hdeg
    (fun _ ↦ rfl)
  choose! e he using fun i (hi : i ∈ s) ↦
    constant_of_exponential (K := RatFunc (RatFunc R)) (expEta a) (fun _ ↦ rfl) hpoly
      (c i) (hdata i hi).1
  -- a Liouville form yields a polynomial solution of the Risch differential equation
  obtain ⟨Ys, hYs⟩ := exists_poly_rde_solution_of_liouville (C' := R) (F := RatFunc R)
    (K := RatFunc (RatFunc R)) hDC (toPoly a) (toPoly p) hdeg (fun _ ↦ rfl) s e u
    (fun i hi ↦ (hdata i hi).2) v (by
      rw [map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      change expIntegrand p = _
      rw [heq]
      congr 1
      exact Finset.sum_congr rfl fun i hi ↦ by rw [he i hi])
  -- but the solver proved there is none
  exact rdeSolve_complete ha h ⟨Ys, by rw [toPoly_deriv]; exact hYs⟩

end CPoly

-- ∫ (2x² + 1) exp(x²) dx = x exp(x²)
#eval CPoly.integrateExpPoly ([1, 0, 2] : CPoly ℚ) [0, 0, 1]
-- ∫ exp(x²) dx: not elementary (`integrateExpPoly_none` applies)
#eval CPoly.integrateExpPoly ([1] : CPoly ℚ) [0, 0, 1]
-- ∫ x exp(x³) dx: not elementary;   ∫ 3x² exp(x³) dx = exp(x³)
#eval CPoly.integrateExpPoly ([0, 1] : CPoly ℚ) [0, 0, 0, 1]
#eval CPoly.integrateExpPoly ([0, 0, 3] : CPoly ℚ) [0, 0, 0, 1]
