import RischTragerBronstein.RDE.NoSolution
import RischTragerBronstein.Liouville.ExponentialCore

/-!
# `exp (a(x))` has no integral of Liouville form, for `deg a ≥ 2`

Let `F = C(x)` with `d/dx`, `a ∈ C[x]` of degree at least two, and `K = F(t)` with `t′ = a′ t`, i.e.
`t = exp a`. Then

* adjoining `t` creates no new constants (`exp_polynomial_no_new_constants`), and
* `t` is **not** of the form `∑ cᵢ uᵢ′ / uᵢ + v′` with `uᵢ, v ∈ K` and `cᵢ ∈ F`
  (`exp_polynomial_no_liouville_form`).

By Liouville's theorem this is the heart of the statement that `∫ exp (x²) dx` is not elementary.
It is proved exactly as the Risch algorithm decides it: a Liouville form would produce a solution
`y ∈ C(x)` of the Risch differential equation `y′ + a′ y = 1`
(`exists_rde_solution_of_liouville`), and there is none (`rde_no_solution`).

The fields are kept abstract (`F = Frac C[x]`, `K = Frac F[t]`), so the statement applies to
`RatFunc (RatFunc C)` and to any other model.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset

namespace Differential

variable {C' F K : Type*} [Field C'] [CharZero C'] [Differential C'[X]]
variable [Field F] [CharZero F] [Algebra C'[X] F] [IsFractionRing C'[X] F] [Differential F]
variable [DifferentialAlgebra C'[X] F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

/-- Adjoining `exp a`, `deg a ≥ 2`, to `C(x)` creates no new constants. -/
theorem exp_polynomial_no_new_constants (hDC : ∀ P : C'[X], P′ = derivative P) (a : C'[X])
    (ha : 1 ≤ a.natDegree)
    (hDF : ∀ P : F[X], P′ = implicitDeriv (C (algebraMap C'[X] F (derivative a)) * X) P)
    (P : F[X]) (n : ℕ) (h : P′ * X ^ n = P * (X ^ n)′) : ∃ e : F, P = C e * X ^ n := by
  set η := algebraMap C'[X] F (derivative a) with hη
  refine ⟨P.coeff n, ?_⟩
  have hP : implicitDeriv (C η * X) P = C (n * η) * P := by
    rw [hDF, hDF, deriv_X_pow] at h
    have hX : (X : F[X]) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_right_cancel₀ hX
    rw [h]; ring
  ext j
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hjn
  · rw [hjn, mul_one]
  rw [mul_zero]
  have hc := congrArg (fun Q : F[X] ↦ Q.coeff j) hP
  simp only [coeff_implicitDeriv_C_mul_X, coeff_C_mul] at hc
  -- `P_j` solves a homogeneous equation with coefficient `(j - n) a′`
  refine rde_homogeneous' hDC (C ((j : C') - n) * derivative a) ?_ (P.coeff j) ?_
  · have hne : ((j : C') - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjn)
    refine mul_ne_zero (C_ne_zero.mpr hne) fun h0 ↦ ?_
    have := derivative_eq_zero.mp h0
    omega
  · rw [map_mul, ← hη]
    have hcast : algebraMap C'[X] F (C ((j : C') - n)) = (j : F) - n := by
      rw [C_sub, map_sub, map_natCast C, map_natCast C, map_natCast, map_natCast]
    rw [hcast]
    linear_combination hc

/-- `exp a`, `deg a ≥ 2`, has no integral of Liouville form in `C(x, exp a)`. -/
theorem exp_polynomial_no_liouville_form (hDC : ∀ P : C'[X], P′ = derivative P) (a : C'[X])
    (ha : 2 ≤ a.natDegree)
    (hDF : ∀ P : F[X], P′ = implicitDeriv (C (algebraMap C'[X] F (derivative a)) * X) P)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) :
    algebraMap F[X] K X ≠ ∑ i ∈ s, algebraMap F[X] K (C (c i)) * logDeriv (u i) + v′ := by
  intro h
  obtain ⟨y, hy⟩ := exists_rde_solution_of_liouville
    (algebraMap C'[X] F (derivative a)) hDF
    (exp_polynomial_no_new_constants hDC a (by omega) hDF) s c u hu v 1 (by simpa using h)
  refine rde_no_solution hDC (derivative a) 1 one_ne_zero ?_ y (by rw [map_one]; exact hy)
  rw [natDegree_one, natDegree_derivative]
  omega

/-- **Decision criterion for `∫ p(x) exp (a(x)) dx`.** If `p exp a` (`p, a ∈ C[x]`, `deg a ≥ 1`) has
an integral of Liouville form in `C(x, exp a)`, then the polynomial Risch differential equation
`Y′ + a′ Y = p` has a solution `Y ∈ C[x]`. -/
theorem exists_poly_rde_solution_of_liouville (hDC : ∀ P : C'[X], P′ = derivative P)
    (a p : C'[X]) (ha : 1 ≤ a.natDegree)
    (hDF : ∀ P : F[X], P′ = implicitDeriv (C (algebraMap C'[X] F (derivative a)) * X) P)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K)
    (h : algebraMap F[X] K (C (algebraMap C'[X] F p) * X) =
      ∑ i ∈ s, algebraMap F[X] K (C (c i)) * logDeriv (u i) + v′) :
    ∃ Y : C'[X], derivative Y + derivative a * Y = p := by
  obtain ⟨y, hy⟩ := exists_rde_solution_of_liouville
    (algebraMap C'[X] F (derivative a)) hDF
    (exp_polynomial_no_new_constants hDC a ha hDF) s c u hu v (algebraMap C'[X] F p) h
  obtain ⟨Y, -, hY⟩ := rde_polynomial_solution hDC (derivative a) p y hy
  exact ⟨Y, hY⟩

end Differential
