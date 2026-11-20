import RischTragerBronstein.Liouville.LocalRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.BigOperators.Field

/-!
# Poles in a Liouville identity

With `A`, `K = Frac A` and a prime `p ∈ A` as in `Liouville/LocalRing.lean`:

* `exists_zpow_mul_isUnitAt`: every nonzero `f ∈ K` is `p ^ n * g` with `n ∈ ℤ`, `g ∈ O_p^×`;
* `logDeriv_sub_mem_regularAt`: `u′ / u - n * p′ / p ∈ O_p` — a logarithmic derivative has at worst
  a simple pole at `p`, with integer "residue" `n = ord_p u`;
* `mem_regularAt_of_liouville_eq`: if `α = ∑ cᵢ uᵢ′ / uᵢ + v′` with `α` and the `cᵢ` regular at a
  **normal** prime `p`, then `v` is regular at `p`.

The last statement is the first half of the proof of Liouville's theorem in a transcendental
extension `F(t)`: applied to every normal irreducible `p ∈ F[t]`, it shows that `v` has no poles
outside the special polynomials.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Differential

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] {p : A} (hp : Prime p)

local notation "φ" => algebraMap A K

include hp in
/-- Every nonzero element of `A` is a power of `p` times an element prime to `p`. -/
lemma exists_pow_mul_not_dvd {a : A} (ha : a ≠ 0) : ∃ (i : ℕ) (a₁ : A), ¬p ∣ a₁ ∧ a = p ^ i * a₁ := by
  have hfin : FiniteMultiplicity p a := FiniteMultiplicity.of_not_isUnit hp.not_isUnit ha
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hpc, hc⟩

include hp in
/-- Every nonzero `f ∈ K` is `p ^ n * g` with `g` a unit of `O_p`. -/
theorem exists_zpow_mul_isUnitAt {f : K} (hf : f ≠ 0) :
    ∃ (n : ℤ) (g : K), IsUnitAt K p g ∧ f = φ p ^ n * g := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨i, a₁, ha₁, rfl⟩ := exists_pow_mul_not_dvd hp ha0
  obtain ⟨j, b₁, hb₁, rfl⟩ := exists_pow_mul_not_dvd hp hb0
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hb₁0 : φ b₁ ≠ 0 := map_ne_zero_of_not_dvd hp hb₁
  refine ⟨(i : ℤ) - j, φ a₁ / φ b₁, ⟨a₁, b₁, ha₁, hb₁, by field_simp⟩, ?_⟩
  rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
  field_simp

variable [Differential A] [Differential K] [DifferentialAlgebra A K]

include hp in
/-- The logarithmic derivative of a unit of `O_p` is regular at `p`. -/
lemma IsUnitAt.logDeriv_mem_regularAt {g : K} (hg : IsUnitAt K p g) :
    logDeriv g ∈ regularAt K p hp := by
  rw [logDeriv, div_eq_mul_inv]
  exact mul_mem (deriv_mem_regularAt hp (hg.mem_regularAt hp)) (hg.inv_mem_regularAt hp)

include hp in
/-- A logarithmic derivative has at worst a simple pole at `p`, with integer residue. -/
theorem logDeriv_sub_mem_regularAt {u : K} (hu : u ≠ 0) :
    ∃ n : ℤ, logDeriv u - n * (φ p′ / φ p) ∈ regularAt K p hp := by
  obtain ⟨n, g, hg, rfl⟩ := exists_zpow_mul_isUnitAt hp hu
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hu
  refine ⟨n, ?_⟩
  have hz : logDeriv (φ p ^ n) = n * (φ p′ / φ p) := by
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast, logDeriv_pow, logDeriv, deriv_algebraMap]; simp
    · rw [zpow_neg, zpow_natCast, ← one_div, logDeriv_div _ _ one_ne_zero (pow_ne_zero _ hp0),
        logDeriv_one, logDeriv_pow, logDeriv, deriv_algebraMap]
      simp
  rw [logDeriv_mul _ _ (zpow_ne_zero _ hp0) hg0, hz, add_sub_cancel_left]
  exact hg.logDeriv_mem_regularAt hp

include hp in
/-- **No poles at normal primes.** In an identity `α = ∑ cᵢ uᵢ′ / uᵢ + v′` where `α` and the `cᵢ`
are regular at the normal prime `p`, the element `v` is regular at `p`. -/
theorem mem_regularAt_of_liouville_eq (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    {ι : Type*} (s : Finset ι) (c u : ι → K) (v α : K)
    (hc : ∀ i ∈ s, c i ∈ regularAt K p hp) (hu : ∀ i ∈ s, u i ≠ 0)
    (hα : α ∈ regularAt K p hp) (h : α = ∑ i ∈ s, c i * logDeriv (u i) + v′) :
    v ∈ regularAt K p hp := by
  classical
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  by_cases hv0 : v = 0
  · rw [hv0]; exact zero_mem _
  obtain ⟨n, g, hg, hv⟩ := exists_zpow_mul_isUnitAt hp hv0
  -- if `n ≥ 0` there is nothing to do
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hv, zpow_natCast]
    exact mul_mem (pow_mem hpm m) (hg.mem_regularAt hp)
  -- otherwise `v = g / p ^ k` with `k ≥ 1`
  exfalso
  obtain ⟨k, hk1, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) :=
    ⟨n.natAbs, by omega, by omega⟩
  have hv' : v = g / φ p ^ k := by rw [hv, zpow_neg, zpow_natCast]; field_simp
  have hunit := isUnitAt_deriv_pole hp hnorm hg k (hnat k hk1)
  rw [← hv'] at hunit
  -- residues of the logarithmic derivatives
  choose! m hm using fun i (hi : i ∈ s) ↦ logDeriv_sub_mem_regularAt hp (hu i hi)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine hunit.ne_mul hp (f := φ p ^ j * (φ p * α) - φ p ^ j * (∑ i ∈ s, c i * m i) * φ p′
    - φ p ^ j * (φ p * ∑ i ∈ s, c i * (logDeriv (u i) - m i * (φ p′ / φ p)))) ?_ ?_
  · have hpj : φ p ^ j ∈ regularAt K p hp := pow_mem hpm j
    refine sub_mem (sub_mem (mul_mem hpj (mul_mem hpm hα)) (mul_mem (mul_mem hpj ?_)
      (algebraMap_mem_regularAt hp _))) (mul_mem hpj (mul_mem hpm ?_))
    · exact sum_mem fun i hi ↦ mul_mem (hc i hi) (intCast_mem _ _)
    · exact sum_mem fun i hi ↦ mul_mem (hc i hi) (hm i hi)
  · have hv'' : v′ = α - ∑ i ∈ s, c i * logDeriv (u i) := by rw [h]; ring
    have hsum : ∑ i ∈ s, c i * (logDeriv (u i) - m i * (φ p′ / φ p)) =
        ∑ i ∈ s, c i * logDeriv (u i) - (∑ i ∈ s, c i * m i) * (φ p′ / φ p) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hv'', hsum]
    generalize ∑ i ∈ s, c i * logDeriv (u i) = S₁
    generalize ∑ i ∈ s, c i * (m i : K) = S₂
    field_simp
    ring

include hp in
/-- Generalisation of `mem_regularAt_of_liouville_eq`: it suffices that `α` has **at most a simple
pole** at the normal prime `p` (`p α ∈ O_p`). -/
theorem mem_regularAt_of_liouville_eq' (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    {ι : Type*} (s : Finset ι) (c u : ι → K) (v α : K)
    (hc : ∀ i ∈ s, c i ∈ regularAt K p hp) (hu : ∀ i ∈ s, u i ≠ 0)
    (hα : φ p * α ∈ regularAt K p hp) (h : α = ∑ i ∈ s, c i * logDeriv (u i) + v′) :
    v ∈ regularAt K p hp := by
  classical
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  by_cases hv0 : v = 0
  · rw [hv0]; exact zero_mem _
  obtain ⟨n, g, hg, hv⟩ := exists_zpow_mul_isUnitAt hp hv0
  -- if `n ≥ 0` there is nothing to do
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hv, zpow_natCast]
    exact mul_mem (pow_mem hpm m) (hg.mem_regularAt hp)
  -- otherwise `v = g / p ^ k` with `k ≥ 1`
  exfalso
  obtain ⟨k, hk1, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) :=
    ⟨n.natAbs, by omega, by omega⟩
  have hv' : v = g / φ p ^ k := by rw [hv, zpow_neg, zpow_natCast]; field_simp
  have hunit := isUnitAt_deriv_pole hp hnorm hg k (hnat k hk1)
  rw [← hv'] at hunit
  -- residues of the logarithmic derivatives
  choose! m hm using fun i (hi : i ∈ s) ↦ logDeriv_sub_mem_regularAt hp (hu i hi)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine hunit.ne_mul hp (f := φ p ^ j * (φ p * α) - φ p ^ j * (∑ i ∈ s, c i * m i) * φ p′
    - φ p ^ j * (φ p * ∑ i ∈ s, c i * (logDeriv (u i) - m i * (φ p′ / φ p)))) ?_ ?_
  · have hpj : φ p ^ j ∈ regularAt K p hp := pow_mem hpm j
    refine sub_mem (sub_mem (mul_mem hpj hα) (mul_mem (mul_mem hpj ?_)
      (algebraMap_mem_regularAt hp _))) (mul_mem hpj (mul_mem hpm ?_))
    · exact sum_mem fun i hi ↦ mul_mem (hc i hi) (intCast_mem _ _)
    · exact sum_mem fun i hi ↦ mul_mem (hc i hi) (hm i hi)
  · have hv'' : v′ = α - ∑ i ∈ s, c i * logDeriv (u i) := by rw [h]; ring
    have hsum : ∑ i ∈ s, c i * (logDeriv (u i) - m i * (φ p′ / φ p)) =
        ∑ i ∈ s, c i * logDeriv (u i) - (∑ i ∈ s, c i * m i) * (φ p′ / φ p) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hv'', hsum]
    generalize ∑ i ∈ s, c i * logDeriv (u i) = S₁
    generalize ∑ i ∈ s, c i * (m i : K) = S₂
    field_simp
    ring


end Differential
