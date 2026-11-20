import RischTragerBronstein.Liouville.PoleOrder

/-!
# Residues in a Liouville identity cancel

Continuing `Liouville/PoleOrder.lean`. Suppose `α = ∑ cᵢ uᵢ′ / uᵢ + v′` in `K = Frac A`, where
`α` is regular at the normal prime `p`, the `cᵢ = φ γᵢ` come from `A`, and `uᵢ = p ^ mᵢ * gᵢ` with
`gᵢ` a unit of `O_p`. Then the "residue" of the right-hand side at `p` vanishes modulo `p`:

  `p ∣ ∑ γᵢ * mᵢ`.

In `F[t]` with the `γᵢ ∈ F`, the sum lies in `F`, so it is divisible by `p` only if it is zero:
the normal irreducible factors of the `uᵢ` contribute nothing and can be discarded.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Differential

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] {p : A} (hp : Prime p)

local notation "φ" => algebraMap A K

include hp in
/-- If `φ x ∈ p O_p` for `x ∈ A`, then `p ∣ x`. -/
lemma dvd_of_algebraMap_eq_mul {x : A} {r : K} (hr : r ∈ regularAt K p hp)
    (h : φ x = φ p * r) : p ∣ x := by
  obtain ⟨a, b, hb, hab⟩ := hr
  have : φ (x * b) = φ (p * a) := by
    rw [map_mul, map_mul, h, ← hab]; ring
  have h2 := IsFractionRing.injective A K this
  exact (hp.dvd_or_dvd ⟨a, h2⟩).resolve_right hb

variable [Differential A] [Differential K] [DifferentialAlgebra A K]

include hp in
lemma logDeriv_algebraMap_zpow (n : ℤ) : logDeriv (φ p ^ n) = n * (φ p′ / φ p) := by
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, logDeriv_pow, logDeriv, deriv_algebraMap]; simp
  · rw [zpow_neg, zpow_natCast, ← one_div, logDeriv_div _ _ one_ne_zero (pow_ne_zero _ hp0),
      logDeriv_one, logDeriv_pow, logDeriv, deriv_algebraMap]
    simp

include hp in
/-- **Residues cancel** at a normal prime. -/
theorem dvd_sum_residues_of_liouville_eq (hnorm : ¬p ∣ p′)
    (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    {ι : Type*} (s : Finset ι) (γ : ι → A) (u g : ι → K) (m : ι → ℤ) (v α : K)
    (hg : ∀ i ∈ s, IsUnitAt K p (g i)) (hu : ∀ i ∈ s, u i = φ p ^ m i * g i)
    (hα : α ∈ regularAt K p hp) (h : α = ∑ i ∈ s, φ (γ i) * logDeriv (u i) + v′) :
    p ∣ ∑ i ∈ s, γ i * (m i : A) := by
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hg0 : ∀ i ∈ s, g i ≠ 0 := fun i hi h0 ↦ by
    obtain ⟨a, b, ha, -, hab⟩ := hg i hi
    rw [h0, zero_mul] at hab
    exact map_ne_zero_of_not_dvd (K := K) hp ha hab.symm
  have hu0 : ∀ i ∈ s, u i ≠ 0 := fun i hi ↦ by
    rw [hu i hi]; exact mul_ne_zero (zpow_ne_zero _ hp0) (hg0 i hi)
  -- `v`, hence `v′`, is regular at `p`
  have hv : v ∈ regularAt K p hp :=
    mem_regularAt_of_liouville_eq hp hnorm hnat s (fun i ↦ φ (γ i)) u v α
      (fun i _ ↦ algebraMap_mem_regularAt hp _) hu0 hα h
  have hv' := deriv_mem_regularAt hp hv
  -- split each logarithmic derivative
  have hsplit : ∑ i ∈ s, φ (γ i) * logDeriv (u i) =
      φ (∑ i ∈ s, γ i * (m i : A)) * (φ p′ / φ p) + ∑ i ∈ s, φ (γ i) * logDeriv (g i) := by
    rw [map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hu i hi, logDeriv_mul _ _ (zpow_ne_zero _ hp0) (hg0 i hi), logDeriv_algebraMap_zpow hp,
      map_mul, map_intCast]
    ring
  have hreg : ∑ i ∈ s, φ (γ i) * logDeriv (g i) ∈ regularAt K p hp :=
    sum_mem fun i hi ↦ mul_mem (algebraMap_mem_regularAt hp _)
      ((hg i hi).logDeriv_mem_regularAt hp)
  -- hence `N p′ = p * (regular)`
  set N := ∑ i ∈ s, γ i * (m i : A) with hN
  have hNp : p ∣ N * p′ := by
    refine dvd_of_algebraMap_eq_mul hp
      (r := α - v′ - ∑ i ∈ s, φ (γ i) * logDeriv (g i)) (sub_mem (sub_mem hα hv') hreg) ?_
    rw [h, hsplit, map_mul]
    field_simp
    ring
  exact (hp.dvd_or_dvd hNp).resolve_right hnorm

end Differential
