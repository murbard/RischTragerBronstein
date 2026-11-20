import RischTragerBronstein.Liouville.Residue
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Stripping normal primes from the logarithms of a Liouville identity

Let `F` be a field of characteristic zero, `F[t]` a differential ring with fraction field `K`, and
`S` a set of **normal** primes of `F[t]`. Suppose

  `α = ∑ cᵢ * (aᵢ / bᵢ)′ / (aᵢ / bᵢ) + v′`,   `cᵢ ∈ F`, `aᵢ, bᵢ ∈ F[t] ∖ {0}`,

with `α` regular at every `p ∈ S`. Then the `aᵢ, bᵢ` can be replaced by polynomials with no factor
in `S` without changing the sum (`exists_reduced_logs`).

For a logarithmic extension `S` is the set of all monic irreducibles and the new `aᵢ, bᵢ` lie in
`F`; for an exponential extension `S` omits only `t`, and they are monomials `e t ^ k`.

The proof is by induction on `∑ (deg aᵢ + deg bᵢ)`: a factor `p ∈ S` of some `aᵢ` or `bᵢ` is divided
out of all of them at once, which is legitimate because the residues at `p` cancel
(`dvd_sum_residues_of_liouville_eq`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F[X]] [Field K] [Algebra F[X] K]
variable [IsFractionRing F[X] K] [Differential K] [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

lemma not_dvd_natCast_polynomial {p : F[X]} (hp : Prime p) (k : ℕ) (hk : k ≠ 0) :
    ¬p ∣ (k : F[X]) := fun h ↦ hp.not_isUnit (isUnit_of_dvd_unit h (by
  rw [← C_eq_natCast, isUnit_C, isUnit_iff_ne_zero]; exact Nat.cast_ne_zero.mpr hk))

lemma eq_zero_of_prime_dvd_C {p : F[X]} (hp : Prime p) {x : F} (h : p ∣ C x) : x = 0 := by
  by_contra hx
  exact hp.not_isUnit (isUnit_of_dvd_unit h (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx)))

theorem exists_reduced_logs (S : Set F[X]) (hS : ∀ p ∈ S, Prime p ∧ ¬p ∣ p′)
    {ι : Type*} (s : Finset ι) (c : ι → F) (v α : K)
    (hα : ∀ p (hp : p ∈ S), α ∈ regularAt K p (hS p hp).1) (N : ℕ) :
    ∀ a b : ι → F[X], (∀ i ∈ s, a i ≠ 0 ∧ b i ≠ 0) →
      ∑ i ∈ s, ((a i).natDegree + (b i).natDegree) ≤ N →
      α = ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a i) / φ (b i)) + v′ →
      ∃ a' b' : ι → F[X], (∀ i ∈ s, a' i ≠ 0 ∧ b' i ≠ 0) ∧
        (∀ i ∈ s, ∀ p ∈ S, ¬p ∣ a' i ∧ ¬p ∣ b' i) ∧
        ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a i) / φ (b i)) =
          ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a' i) / φ (b' i)) := by
  classical
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a b hab hN h
  by_cases hred : ∀ i ∈ s, ∀ p ∈ S, ¬p ∣ a i ∧ ¬p ∣ b i
  · exact ⟨a, b, hab, hred, rfl⟩
  -- a prime `p ∈ S` dividing some `a j` or `b j`
  obtain ⟨j, hj, p, hpS, hpj⟩ : ∃ j ∈ s, ∃ p ∈ S, p ∣ a j ∨ p ∣ b j := by
    by_contra hcon
    exact hred fun i hi p hp ↦ ⟨fun hd ↦ hcon ⟨i, hi, p, hp, Or.inl hd⟩,
      fun hd ↦ hcon ⟨i, hi, p, hp, Or.inr hd⟩⟩
  obtain ⟨hp, hnorm⟩ := hS p hpS
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective F[X] K)]; exact hp.ne_zero
  have hpdeg : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
    · rw [eq_C_of_natDegree_eq_zero h0] at hp
      exact absurd (isUnit_C.mpr (isUnit_iff_ne_zero.mpr fun hc ↦ hp.ne_zero (by rw [hc, C_0])))
        hp.not_isUnit
    · exact h0
  -- divide `p` out of every `a i` and `b i`
  have hdec : ∀ x : F[X], ∃ (k : ℕ) (x' : F[X]), (x ≠ 0 → ¬p ∣ x' ∧ x = p ^ k * x') := fun x ↦ by
    by_cases hx : x = 0
    · exact ⟨0, 0, fun h ↦ absurd hx h⟩
    · obtain ⟨k, x', h1, h2⟩ := exists_pow_mul_not_dvd hp hx
      exact ⟨k, x', fun _ ↦ ⟨h1, h2⟩⟩
  choose ka a' ha' using fun i ↦ hdec (a i)
  choose kb b' hb' using fun i ↦ hdec (b i)
  have hne : ∀ i ∈ s, a' i ≠ 0 ∧ b' i ≠ 0 := fun i hi ↦
    ⟨fun h0 ↦ (ha' i (hab i hi).1).1 (h0 ▸ dvd_zero p),
     fun h0 ↦ (hb' i (hab i hi).2).1 (h0 ▸ dvd_zero p)⟩
  have hφne : ∀ i ∈ s, φ (a' i) ≠ 0 ∧ φ (b' i) ≠ 0 := fun i hi ↦
    ⟨(map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr (hne i hi).1,
     (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr (hne i hi).2⟩
  let m : ι → ℤ := fun i ↦ (ka i : ℤ) - kb i
  let g : ι → K := fun i ↦ φ (a' i) / φ (b' i)
  have hg : ∀ i ∈ s, IsUnitAt K p (g i) := fun i hi ↦
    ⟨a' i, b' i, (ha' i (hab i hi).1).1, (hb' i (hab i hi).2).1, by
      have := (hφne i hi).2
      simp only [g]; field_simp⟩
  have hu : ∀ i ∈ s, φ (a i) / φ (b i) = φ p ^ m i * g i := fun i hi ↦ by
    have h1 := (hφne i hi).2
    conv_lhs => rw [(ha' i (hab i hi).1).2, (hb' i (hab i hi).2).2]
    simp only [m, g, map_mul, map_pow, zpow_sub₀ hp0, zpow_natCast]
    field_simp
  -- residues cancel
  have hres := dvd_sum_residues_of_liouville_eq hp hnorm (not_dvd_natCast_polynomial hp) s
    (fun i ↦ C (c i)) (fun i ↦ φ (a i) / φ (b i)) g m v α hg hu (hα p hpS) h
  have hres0 : ∑ i ∈ s, c i * (m i : F) = 0 := by
    apply eq_zero_of_prime_dvd_C hp
    convert hres using 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_intCast]
  have hg0 : ∀ i ∈ s, g i ≠ 0 := fun i hi ↦ div_ne_zero (hφne i hi).1 (hφne i hi).2
  have hsum : ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a i) / φ (b i)) =
      ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a' i) / φ (b' i)) := by
    have : ∀ i ∈ s, φ (C (c i)) * logDeriv (φ (a i) / φ (b i)) =
        φ (C (c i * (m i : F))) * (φ p′ / φ p) + φ (C (c i)) * logDeriv (g i) := fun i hi ↦ by
      rw [hu i hi, logDeriv_mul _ _ (zpow_ne_zero _ hp0) (hg0 i hi), logDeriv_algebraMap_zpow hp,
        map_mul, map_mul, map_intCast, map_intCast]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum, ← map_sum,
      hres0, map_zero, map_zero, zero_mul, zero_add]
  -- the measure decreases
  have hdegle : ∀ i ∈ s, (a' i).natDegree + (b' i).natDegree ≤ (a i).natDegree + (b i).natDegree :=
    fun i hi ↦ by
      have h1 := (ha' i (hab i hi).1).2
      have h2 := (hb' i (hab i hi).2).2
      have e1 : (a i).natDegree = ka i * p.natDegree + (a' i).natDegree := by
        conv_lhs => rw [h1]
        rw [natDegree_mul (pow_ne_zero _ hp.ne_zero) (hne i hi).1, natDegree_pow]
      have e2 : (b i).natDegree = kb i * p.natDegree + (b' i).natDegree := by
        conv_lhs => rw [h2]
        rw [natDegree_mul (pow_ne_zero _ hp.ne_zero) (hne i hi).2, natDegree_pow]
      omega
  have hdeglt : (a' j).natDegree + (b' j).natDegree < (a j).natDegree + (b j).natDegree := by
    have h1 := (ha' j (hab j hj).1)
    have h2 := (hb' j (hab j hj).2)
    have e1 : (a j).natDegree = ka j * p.natDegree + (a' j).natDegree := by
      conv_lhs => rw [h1.2]
      rw [natDegree_mul (pow_ne_zero _ hp.ne_zero) (hne j hj).1, natDegree_pow]
    have e2 : (b j).natDegree = kb j * p.natDegree + (b' j).natDegree := by
      conv_lhs => rw [h2.2]
      rw [natDegree_mul (pow_ne_zero _ hp.ne_zero) (hne j hj).2, natDegree_pow]
    have hk : 1 ≤ ka j ∨ 1 ≤ kb j := by
      rcases hpj with hd | hd
      · left
        by_contra hk0
        have : ka j = 0 := by omega
        rw [h1.2, this, pow_zero, one_mul] at hd
        exact h1.1 hd
      · right
        by_contra hk0
        have : kb j = 0 := by omega
        rw [h2.2, this, pow_zero, one_mul] at hd
        exact h2.1 hd
    rcases hk with hk | hk <;> nlinarith
  have hlt : ∑ i ∈ s, ((a' i).natDegree + (b' i).natDegree) < N :=
    lt_of_lt_of_le (Finset.sum_lt_sum hdegle ⟨j, hj, hdeglt⟩) hN
  obtain ⟨a'', b'', h1, h2, h3⟩ := ih _ hlt a' b' hne le_rfl (by rw [← hsum]; exact h)
  exact ⟨a'', b'', h1, h2, hsum.trans h3⟩

end Differential
