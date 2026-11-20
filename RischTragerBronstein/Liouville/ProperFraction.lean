import RischTragerBronstein.Rational.RationalPart

/-!
# Proper fractions are not derivatives, in any monomial extension with normal primes

Let `F[t]` carry a derivation for which every irreducible polynomial is normal (e.g. a primitive
monomial without new constants). If `y′ = r / s` in `F(t)` with `s` squarefree and `deg r < deg s`,
then `r = 0`. This is the fact that makes **limited integration inside `F(t)`** decidable level by
level: after Hermite reduction, the proper part of an integrand must vanish for an antiderivative
to exist inside the field.
-/

open Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F[X]] [Field K] [Algebra F[X] K]
variable [IsFractionRing F[X] K] [Differential K] [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

theorem eq_zero_of_deriv_eq_proper_fraction_of_normal
    (hnorm : ∀ p : F[X], Irreducible p → ¬p ∣ p′) (r s : F[X]) (hs : Squarefree s)
    (hdeg : r.degree < s.degree) (y : K) (h : y′ = φ r / φ s) : r = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hs0 : s ≠ 0 := hs.ne_zero
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  -- `y` is a polynomial
  obtain ⟨Y, rfl⟩ : ∃ Y : F[X], y = φ Y := by
    refine exists_polynomial_of_regularAt y fun p _ hp ↦ ?_
    refine mem_regularAt_of_deriv_simple_pole hp.prime (hnorm p hp)
      (not_dvd_natCast_polynomial hp.prime) ?_
    rw [h]
    exact simple_pole_mem_regularAt hs hp
  -- so `Y′ s = r`, impossible by degrees unless `r = 0`
  have hpoly : Y′ * s = r := by
    apply hinj
    rw [map_mul, ← deriv_algebraMap, h]
    field_simp
  by_contra hr0
  have hY' : Y′ ≠ 0 := fun h0 ↦ hr0 (by rw [← hpoly, h0, zero_mul])
  have : s.degree ≤ r.degree := by
    rw [← hpoly, degree_mul]
    exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hY')
  exact absurd hdeg (not_lt.mpr this)

/-- **Antiderivatives inside the field.** If `z′ = A + b / s` with `A` a polynomial, `s` squarefree
and `deg b < deg s`, then `b = 0` and `z` is a polynomial `P` with `P′ = A`: integration inside
`F(t)` of a Hermite-reduced element is a polynomial problem. -/
theorem deriv_eq_poly_add_proper (hnorm : ∀ p : F[X], Irreducible p → ¬p ∣ p′)
    (A b s : F[X]) (hs : Squarefree s) (hdeg : b.degree < s.degree) (z : K)
    (h : z′ = φ A + φ b / φ s) : b = 0 ∧ ∃ P : F[X], z = φ P ∧ P′ = A := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hs0 : s ≠ 0 := hs.ne_zero
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  obtain ⟨P, rfl⟩ : ∃ P : F[X], z = φ P := by
    refine exists_polynomial_of_regularAt z fun p _ hp ↦ ?_
    refine mem_regularAt_of_deriv_simple_pole hp.prime (hnorm p hp)
      (not_dvd_natCast_polynomial hp.prime) ?_
    rw [h, add_mul]
    exact add_mem (mul_mem (algebraMap_mem_regularAt _ A) (algebraMap_mem_regularAt _ p))
      (simple_pole_mem_regularAt hs hp)
  have hpoly : (P′ - A) * s = b := by
    apply hinj
    rw [map_mul, map_sub, ← deriv_algebraMap, h]
    field_simp
    ring
  have hQ : P′ - A = 0 := by
    by_contra hQ0
    have : s.degree ≤ b.degree := by
      rw [← hpoly, degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hQ0)
    exact absurd hdeg (not_lt.mpr this)
  exact ⟨by rw [← hpoly, hQ, zero_mul], P, rfl, sub_eq_zero.mp hQ⟩

end Differential
