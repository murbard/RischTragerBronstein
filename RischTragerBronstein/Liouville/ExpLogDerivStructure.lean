import RischTragerBronstein.Liouville.ExponentialLaurentPart
import RischTragerBronstein.Liouville.PoleOrder
import RischTragerBronstein.Liouville.MonicPrimes
import RischTragerBronstein.Liouville.Reduce

/-!
# Derivatives which are logarithmic derivatives, in an exponential extension

Let `K = F(t)`, `t′ = b t`, with no new constants. If `Z′ = u′ / u` (`Z, u ∈ K`, `u ≠ 0`), then
`Z ∈ F` and `Z′ = e′ / e + n b` for some `e ∈ F ∖ {0}`, `n ∈ ℤ` (`exp_deriv_eq_logDeriv`):
the Laurent part of `Z` reduces to its constant term (no new constants), and the normal part of
`Z` has a derivative which is a logarithmic derivative, hence no poles at the normal primes
(`mem_regularAt_of_liouville_eq'`), hence vanishes.

This is the inductive step of the structure theorem for towers of exponentials: `exp Z ∈ F(t)`
forces `Z ∈ F` and `exp (Z - n a) ∈ F` (`t = exp a`).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
variable (hconst : ∀ (P : F[X]) (n : ℕ),
  implicitDeriv (C b * X) P * X ^ n = P * implicitDeriv (C b * X) (X ^ n) → ∃ e : F, P = C e * X ^ n)

include hDe hconst in
/-- A normal proper fraction whose derivative is a polynomial plus a logarithmic derivative
vanishes. -/
lemma nproper_eq_zero_of_deriv_eq (P : K) (hP : IsNProperFrac F P) (β : F) (u : K) (hu : u ≠ 0)
    (h : P′ = logDeriv u - φ (C β)) : P = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hreg : ∀ (p : F[X]) (_ : p.Monic) (hp : Irreducible p), P ∈ regularAt K p hp.prime := by
    intro p hm hp
    by_cases hX : p = X
    · subst hX
      obtain ⟨a, s, hs, hsX, -, rfl⟩ := hP
      refine ⟨a, s, hsX, ?_⟩
      have : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs
      field_simp
    · have hnorm : ¬p ∣ p′ := by
        rw [hDe]
        exact not_dvd_deriv_of_monic_ne_X b hconst hm hp hX
      have := mem_regularAt_of_liouville_eq' hp.prime hnorm
        (not_dvd_natCast_polynomial hp.prime) ({()} : Finset Unit) (fun _ ↦ 1) (fun _ ↦ u) (-P)
        (φ (C β)) (fun _ _ ↦ one_mem _) (fun _ _ ↦ hu)
        (mul_mem (algebraMap_mem_regularAt _ p) (algebraMap_mem_regularAt _ _)) (by
          rw [Finset.sum_singleton, one_mul, map_neg, h]; ring)
      simpa using neg_mem this
  obtain ⟨Q, rfl⟩ := exists_polynomial_of_regularAt P hreg
  have hQ : Q = 0 := eq_zero_of_isNProperFrac_laurent (K := K) (N := 0) (by
    rw [pow_zero, map_one, div_one]; exact hP)
  rw [hQ, map_zero]

include hDe hconst in
/-- **`Z′ = u′ / u` in `F(t)` forces `Z ∈ F` and `Z′ = e′ / e + n b`.** -/
theorem exp_deriv_eq_logDeriv (Z u : K) (hu : u ≠ 0) (h : Z′ = logDeriv u) :
    ∃ (Z0 e : F) (n : ℤ), e ≠ 0 ∧ Z = φ (C Z0) ∧ Z0′ = logDeriv e + (n : F) * b := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨V, k, hP⟩ := exists_laurent_add_nproper (F := F) (K := K) Z
  set P := Z - φ V / φ (X ^ k) with hPdef
  obtain ⟨e, he, n, hR⟩ := logDeriv_sub_isNProperFrac hDe u hu
  set β := logDeriv e + (n : F) * b with hβ
  have hXk : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hZ : Z = φ V / φ (X ^ k) + P := by rw [hPdef]; ring
  -- the Laurent parts
  have hL : implicitDeriv (C b * X) V - C ((k : F) * b) * V - C β * X ^ k = 0 := by
    refine eq_zero_of_isNProperFrac_laurent (K := K) (N := k) ?_
    have e1 : φ (implicitDeriv (C b * X) V - C ((k : F) * b) * V - C β * X ^ k) / φ (X ^ k) =
        (logDeriv u - φ (C β)) - P′ := by
      rw [← h, hZ, show (φ V / φ (X ^ k) + P)′ = (φ V / φ (X ^ k))′ + P′ from map_add _ _ _,
        deriv_laurent hDe]
      simp only [map_sub, map_mul]
      field_simp
      ring
    rw [e1]
    exact isNProperFrac_sub hR (isNProperFrac_deriv hDe hP)
  have hV : V = C (V.coeff k) * X ^ k :=
    eq_monomial_of_deriv b hconst (by rw [← sub_eq_zero]; exact hL)
  have hZ0 : (V.coeff k)′ = β := by
    have hc := congrArg (fun Q : F[X] ↦ Q.coeff k) hL
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_zero] at hc
    rw [coeff_implicitDeriv_C_mul_X] at hc
    linear_combination hc
  -- the normal part vanishes
  have hP0 : P = 0 := by
    refine nproper_eq_zero_of_deriv_eq hDe hconst P hP β u hu ?_
    have e2 : P′ = Z′ - (φ V / φ (X ^ k))′ := by rw [hPdef, map_sub]
    rw [e2, h, deriv_laurent hDe]
    have : implicitDeriv (C b * X) V - C ((k : F) * b) * V = C β * X ^ k := by
      rw [← sub_eq_zero]; exact hL
    rw [this, map_mul]
    field_simp
  refine ⟨V.coeff k, e, n, he, ?_, hZ0⟩
  rw [hZ, hP0, add_zero]
  conv_lhs => rw [hV]
  rw [map_mul]
  field_simp
