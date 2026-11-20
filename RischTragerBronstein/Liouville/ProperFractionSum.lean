import RischTragerBronstein.Liouville.ProperFraction

/-!
# Sums of proper fractions are not derivatives

The list version of `deriv_eq_poly_add_proper`: if `z′ = A + ∑ bᵢ / sᵢ` in `F(t)` (every prime
normal) with each `sᵢ` squarefree and `deg bᵢ < deg sᵢ`, then `∑ bᵢ / sᵢ = 0` and `z` is a
polynomial `P` with `P′ = A`. This is what parametric limited integration needs: the fractions
`bᵢ / sᵢ` come from the Hermite reductions of several integrands, with different denominators.
-/

open Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F[X]] [Field K] [Algebra F[X] K]
variable [IsFractionRing F[X] K] [Differential K] [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- A sum of proper fractions is a proper fraction. -/
lemma sum_proper (l : List (F[X] × F[X])) (hs : ∀ p ∈ l, p.2 ≠ 0)
    (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) :
    ∃ N D : F[X], D ≠ 0 ∧ N.degree < D.degree ∧
      (l.map fun p ↦ φ p.1 / φ p.2).sum = φ N / φ D := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  induction l with
  | nil => exact ⟨0, 1, one_ne_zero, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨N, D, hD, hND, hsum⟩ := ih (fun q hq ↦ hs q (List.mem_cons_of_mem _ hq))
      (fun q hq ↦ hdeg q (List.mem_cons_of_mem _ hq))
    have hp := hs p List.mem_cons_self
    have hpd := hdeg p List.mem_cons_self
    refine ⟨p.1 * D + N * p.2, p.2 * D, mul_ne_zero hp hD, ?_, ?_⟩
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · rw [degree_mul, degree_mul]
        exact WithBot.add_lt_add_right (degree_ne_bot.mpr hD) hpd
      · rw [degree_mul, degree_mul, add_comm N.degree]
        exact WithBot.add_lt_add_left (degree_ne_bot.mpr hp) hND
    · have hφp : φ p.2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp
      have hφD : φ D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
      rw [List.map_cons, List.sum_cons, hsum, map_add, map_mul, map_mul, map_mul]
      field_simp

/-- **Antiderivatives inside the field, several fractions.** -/
theorem deriv_eq_poly_add_sum_proper (hnorm : ∀ p : F[X], Irreducible p → ¬p ∣ p′)
    (A : F[X]) (l : List (F[X] × F[X])) (hsq : ∀ p ∈ l, Squarefree p.2)
    (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) (z : K)
    (h : z′ = φ A + (l.map fun p ↦ φ p.1 / φ p.2).sum) :
    (l.map fun p ↦ φ p.1 / φ p.2).sum = 0 ∧ ∃ P : F[X], z = φ P ∧ P′ = A := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨P, rfl⟩ : ∃ P : F[X], z = φ P := by
    refine exists_polynomial_of_regularAt z fun p _ hp ↦ ?_
    refine mem_regularAt_of_deriv_simple_pole hp.prime (hnorm p hp)
      (not_dvd_natCast_polynomial hp.prime) ?_
    rw [h, add_mul, ← List.sum_map_mul_right]
    refine add_mem (mul_mem (algebraMap_mem_regularAt _ A) (algebraMap_mem_regularAt _ p)) ?_
    refine Subring.list_sum_mem _ fun y hy ↦ ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    exact simple_pole_mem_regularAt (hsq q hq) hp
  obtain ⟨N, D, hD, hND, hsum⟩ := sum_proper (K := K) l (fun p hp ↦ (hsq p hp).ne_zero) hdeg
  have hφD : φ D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hpoly : (P′ - A) * D = N := by
    apply hinj
    rw [map_mul, map_sub, ← deriv_algebraMap, h, hsum]
    field_simp
    ring
  have hQ : P′ - A = 0 := by
    by_contra hQ0
    have : D.degree ≤ N.degree := by
      rw [← hpoly, degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hQ0)
    exact absurd hND (not_lt.mpr this)
  refine ⟨?_, P, rfl, sub_eq_zero.mp hQ⟩
  rw [hsum, ← hpoly, hQ, zero_mul, map_zero, zero_div]

end Differential
