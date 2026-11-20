import RischTragerBronstein.RDE.ValInf
import RischTragerBronstein.Liouville.Residue
import RischTragerBronstein.Liouville.Reduce
import RischTragerBronstein.Liouville.MonicPrimes

/-!
# Denominator bounds for `y′ + (h′ + ∑ cᵢ wᵢ′ / wᵢ) y = g`

The Risch equations of mixed towers have coefficients `f = h′ + ∑ cᵢ wᵢ′ / wᵢ` with constant
`cᵢ`. At a normal prime `p`, the logarithmic part has at worst a simple pole with residue
`ρ = ∑ cᵢ ordₚ wᵢ`, so `y` has a pole of order at most that of `g` minus one, **or** of order
exactly `k` with `ρ = k` (`rde_pole_bound_res`, `rde_log_normal`). `rde_log_denominator` turns this
into the normal denominator bound `gcd(e, e′) · Lᴺ`.

At the special prime `t` of an exponential extension, the logarithmic part is regular, with value
`∑ cᵢ (ordₜ wᵢ · b + wᵢ₀′ / wᵢ₀)` (`logDeriv_val_X`); `rde_special_bound_reg_R` and
`rde_special_bound_pole_R` are the special bounds with this extra regular term.
-/

open Polynomial

namespace Differential

section Generic

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] {p : A} (hp : Prime p)
variable [Differential A] [Differential K] [DifferentialAlgebra A K]

local notation "φ" => algebraMap A K

omit [WfDvdMonoid A] [Differential A] [Differential K] [DifferentialAlgebra A K] in
include hp in
lemma isUnitAt_algebraMap {a : A} (ha : ¬p ∣ a) : IsUnitAt K p (φ a) :=
  ⟨a, 1, ha, hp.not_dvd_one, by simp⟩

omit [WfDvdMonoid A] in
lemma deriv_div_pow_mul (u : K) (k : ℕ) (hp0 : φ p ≠ 0) :
    (u / φ p ^ k)′ * φ p ^ (k + 1) = u′ * φ p - k * u * φ p′ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Derivation.leibniz_div, deriv_pow_succ, deriv_algebraMap]
  simp only [smul_eq_mul]
  field_simp
  push_cast
  ring

include hp in
/-- **The pole bound with a residue**: `y′ + (h′ + ρ p′ / p + R₀) y = g`, `R₀` regular at the
normal prime `p`. Either `y` has a pole of order `≤ E` (when `g pᴱ⁺¹` is regular), or of order
exactly `k > E` with `ρ = k`. -/
theorem rde_pole_bound_res (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    (ρ : A) (hρ : ∀ k : ℕ, ρ ≠ (k : A) → ¬p ∣ (ρ - k)) (h y g R0 : K)
    (hR0 : R0 ∈ regularAt K p hp) (E : ℕ) (hg : g * φ p ^ (E + 1) ∈ regularAt K p hp)
    (hrde : y′ + (h′ + φ ρ * (φ p′ / φ p) + R0) * y = g) :
    y * φ p ^ E ∈ regularAt K p hp ∨
      ∃ k : ℕ, E < k ∧ ρ = (k : A) ∧ y * φ p ^ k ∈ regularAt K p hp := by
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  by_cases hy0 : y = 0
  · left; rw [hy0, zero_mul]; exact zero_mem _
  obtain ⟨n, u, hu, rfl⟩ := exists_zpow_mul_isUnitAt hp hy0
  by_cases hn : -(E : ℤ) ≤ n
  · left
    obtain ⟨j, hj⟩ : ∃ j : ℕ, n + E = j := ⟨(n + E).toNat, by omega⟩
    have : φ p ^ n * u * φ p ^ E = φ p ^ j * u := by
      rw [← zpow_natCast, ← zpow_natCast, ← hj, zpow_add₀ hp0, zpow_natCast]; ring
    rw [this]; exact mul_mem (pow_mem hpm _) (hu.mem_regularAt hp)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
  have hkE : E + 1 ≤ k := by omega
  have hyk : φ p ^ n * u = u / φ p ^ k := by rw [hk, zpow_neg, zpow_natCast]; field_simp
  rw [hyk] at hrde ⊢
  have hU := deriv_div_pow_mul u k hp0
  obtain ⟨r, hr⟩ : ∃ r, k = E + 1 + r := ⟨k - (E + 1), by omega⟩
  have hreg1 : g * φ p ^ (E + 1) * φ p ^ r ∈ regularAt K p hp := mul_mem hg (pow_mem hpm _)
  have hgk : g * φ p ^ (k + 1) = φ p * (g * φ p ^ (E + 1) * φ p ^ r) := by
    rw [hr]; ring
  have hpk : φ p ^ k ≠ 0 := pow_ne_zero _ hp0
  by_cases hh : h ∈ regularAt K p hp
  · have hf := deriv_mem_regularAt hp hh
    have e : g * φ p ^ (k + 1) = φ (ρ - k) * φ p′ * u + φ p * (u′ + h′ * u + R0 * u) := by
      rw [← hrde, add_mul, hU]
      simp only [map_sub, map_natCast]
      field_simp
      ring
    by_cases hρk : ρ = (k : A)
    · right
      refine ⟨k, by omega, hρk, ?_⟩
      rw [div_mul_cancel₀ _ hpk]
      exact hu.mem_regularAt hp
    · exfalso
      have hunit : IsUnitAt K p (φ (ρ - k) * φ p′ * u) :=
        ((isUnitAt_algebraMap hp (hρ k hρk)).mul' hp (isUnitAt_algebraMap hp hnorm)).mul' hp hu
      refine hunit.ne_mul hp (f := g * φ p ^ (E + 1) * φ p ^ r - (u′ + h′ * u + R0 * u))
        (sub_mem hreg1 (add_mem (add_mem (deriv_mem_regularAt hp (hu.mem_regularAt hp))
          (mul_mem hf (hu.mem_regularAt hp))) (mul_mem hR0 (hu.mem_regularAt hp)))) ?_
      linear_combination e.symm.trans hgk
  · exfalso
    have hh0 : h ≠ 0 := fun h0 ↦ hh (h0 ▸ zero_mem _)
    obtain ⟨n', v, hv, rfl⟩ := exists_zpow_mul_isUnitAt hp hh0
    have hn' : n' < 0 := by
      by_contra hn'
      obtain ⟨j, hj⟩ : ∃ j : ℕ, n' = j := ⟨n'.toNat, by omega⟩
      refine hh ?_
      rw [hj, zpow_natCast]
      exact mul_mem (pow_mem hpm _) (hv.mem_regularAt hp)
    obtain ⟨l, hl⟩ : ∃ l : ℕ, n' = -((l + 1 : ℕ) : ℤ) := ⟨(-n').toNat - 1, by omega⟩
    have hhv : φ p ^ n' * v = v / φ p ^ (l + 1) := by
      rw [hl, zpow_neg, zpow_natCast]; field_simp
    rw [hhv] at hrde
    set V := (v / φ p ^ (l + 1))′ * φ p ^ (l + 1 + 1) with hV
    have hVv : IsUnitAt K p V := isUnitAt_deriv_pole hp hnorm hv (l + 1) (hnat _ (by omega))
    set U := (u / φ p ^ k)′ * φ p ^ (k + 1) with hUd
    have hUr : U ∈ regularAt K p hp := by
      rw [hU]
      exact sub_mem (mul_mem (deriv_mem_regularAt hp (hu.mem_regularAt hp)) hpm)
        (mul_mem (mul_mem (natCast_mem _ _) (hu.mem_regularAt hp)) (algebraMap_mem_regularAt hp _))
    have hY : u / φ p ^ k * φ p ^ k = u := div_mul_cancel₀ _ hpk
    have e : g * φ p ^ (k + 1) * φ p ^ (l + 1) = U * φ p ^ (l + 1) + V * u +
        (φ ρ * φ p′ + φ p * R0) * u * φ p ^ (l + 1) := by
      rw [← hrde, hUd, hV]
      field_simp
      ring
    refine (hVv.mul' hp hu).ne_mul hp (f := g * φ p ^ (E + 1) * φ p ^ r * φ p ^ (l + 1) -
      U * φ p ^ l - (φ ρ * φ p′ + φ p * R0) * u * φ p ^ l) (sub_mem (sub_mem
        (mul_mem hreg1 (pow_mem hpm _)) (mul_mem hUr (pow_mem hpm _)))
        (mul_mem (mul_mem (add_mem (mul_mem (algebraMap_mem_regularAt hp _)
          (algebraMap_mem_regularAt hp _)) (mul_mem hpm hR0)) (hu.mem_regularAt hp))
          (pow_mem hpm _))) ?_
    rw [hgk] at e
    linear_combination -e

end Generic

lemma pow_dvd_deriv_pow_succ_mul {R : Type*} [CommRing R] (D : Derivation ℤ R R) (q e1 : R)
    (E : ℕ) : q ^ E ∣ D (q ^ (E + 1) * e1) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
  simp only [smul_eq_mul, nsmul_eq_mul]
  exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow q (Nat.le_succ E)) _)
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _)

section Poly

variable {F K : Type*} [Field F] [CharZero F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

omit [CharZero F] [Differential F[X]] [Differential K] [DifferentialAlgebra F[X] K] in
lemma le_natDegree_of_pow_dvd {p N : F[X]} (hp : Irreducible p) (hN : N ≠ 0) {a : ℕ}
    (h : p ^ a ∣ N) : a ≤ N.natDegree := by
  have h1 : (p ^ a).natDegree ≤ N.natDegree := natDegree_le_of_dvd h hN
  rw [natDegree_pow] at h1
  have h2 : 0 < p.natDegree := Irreducible.natDegree_pos hp
  nlinarith

omit [CharZero F] in
/-- The logarithmic derivative of `N / D` at an irreducible `p`: `n p′ / p` plus a regular
element, `|n| ≤ deg N + deg D`, and `n = 0` unless `p ∣ N D`. -/
lemma logDeriv_frac_decomp {p : F[X]} (hp : Irreducible p) (N D : F[X]) (hN : N ≠ 0)
    (hD : D ≠ 0) : ∃ n : ℤ, |n| ≤ ((N.natDegree + D.natDegree : ℕ) : ℤ) ∧
      (n ≠ 0 → p ∣ N * D) ∧
      logDeriv (φ N / φ D) - n * (φ p′ / φ p) ∈ regularAt K p hp.prime := by
  have hpp := hp.prime
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective F[X] K)]; exact hpp.ne_zero
  obtain ⟨a, N1, hN1, rfl⟩ := exists_pow_mul_not_dvd hpp hN
  obtain ⟨b, D1, hD1, rfl⟩ := exists_pow_mul_not_dvd hpp hD
  have hφN1 : φ N1 ≠ 0 := map_ne_zero_of_not_dvd hpp hN1
  have hφD1 : φ D1 ≠ 0 := map_ne_zero_of_not_dvd hpp hD1
  refine ⟨(a : ℤ) - b, ?_, ?_, ?_⟩
  · have ha := le_natDegree_of_pow_dvd hp hN (dvd_mul_right _ _)
    have hb := le_natDegree_of_pow_dvd hp hD (dvd_mul_right _ _)
    rw [abs_le]; constructor <;> push_cast <;> omega
  · intro hn
    rcases Nat.eq_zero_or_pos a with ha | ha
    · have hb : b ≠ 0 := by omega
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self p hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _) _
  · have hsplit : φ (p ^ a * N1) / φ (p ^ b * D1) = φ p ^ ((a : ℤ) - b) * (φ N1 / φ D1) := by
      rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
      field_simp
    have hunit : IsUnitAt K p (φ N1 / φ D1) := ⟨N1, D1, hN1, hD1, by field_simp⟩
    rw [hsplit, logDeriv_mul _ _ (zpow_ne_zero _ hp0) (div_ne_zero hφN1 hφD1),
      logDeriv_algebraMap_zpow hpp]
    push_cast
    rw [add_sub_cancel_left]
    exact hunit.logDeriv_mem_regularAt hpp

omit [CharZero F] in
/-- The logarithmic part at an irreducible `p`: `∑ cᵢ (Nᵢ / Dᵢ)′ / (Nᵢ / Dᵢ) = ρ p′ / p + R₀`. -/
lemma logSum_decomp {p : F[X]} (hp : Irreducible p) {ι : Type*} (s : Finset ι) (c : ι → F)
    (Nw Dw : ι → F[X]) (hND : ∀ i ∈ s, Nw i ≠ 0 ∧ Dw i ≠ 0) :
    ∃ n : ι → ℤ, (∀ i ∈ s, |n i| ≤ (((Nw i).natDegree + (Dw i).natDegree : ℕ) : ℤ) ∧
      (n i ≠ 0 → p ∣ Nw i * Dw i)) ∧
      ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)) -
        φ (C (∑ i ∈ s, c i * n i)) * (φ p′ / φ p) ∈ regularAt K p hp.prime := by
  classical
  have hdec : ∀ i ∈ s, ∃ n : ℤ, |n| ≤ (((Nw i).natDegree + (Dw i).natDegree : ℕ) : ℤ) ∧
      (n ≠ 0 → p ∣ Nw i * Dw i) ∧
      logDeriv (φ (Nw i) / φ (Dw i)) - n * (φ p′ / φ p) ∈ regularAt K p hp.prime :=
    fun i hi ↦ logDeriv_frac_decomp hp _ _ (hND i hi).1 (hND i hi).2
  choose! n hn using hdec
  refine ⟨n, fun i hi ↦ ⟨(hn i hi).1, (hn i hi).2.1⟩, ?_⟩
  have e : ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)) -
      φ (C (∑ i ∈ s, c i * n i)) * (φ p′ / φ p) = ∑ i ∈ s, φ (C (c i)) *
        (logDeriv (φ (Nw i) / φ (Dw i)) - n i * (φ p′ / φ p)) := by
    rw [map_sum, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_mul, map_intCast]
    ring
  rw [e]
  exact Subring.sum_mem _ fun i hi ↦ mul_mem (algebraMap_mem_regularAt _ _) (hn i hi).2.2

/-- **The pole bound at a normal prime, with a logarithmic part.** -/
theorem rde_log_normal {p : F[X]} (hp : Irreducible p) (hnorm : ¬p ∣ p′) (h y g : K)
    {ι : Type*} (s : Finset ι) (c : ι → F) (Nw Dw : ι → F[X])
    (hND : ∀ i ∈ s, Nw i ≠ 0 ∧ Dw i ≠ 0) (E : ℕ)
    (hg : g * φ p ^ (E + 1) ∈ regularAt K p hp.prime)
    (hrde : y′ + (h′ + ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i))) * y = g) :
    y * φ p ^ E ∈ regularAt K p hp.prime ∨ ∃ (k : ℕ) (n : ι → ℤ), E < k ∧
      y * φ p ^ k ∈ regularAt K p hp.prime ∧
      (∀ i ∈ s, |n i| ≤ (((Nw i).natDegree + (Dw i).natDegree : ℕ) : ℤ) ∧
        (n i ≠ 0 → p ∣ Nw i * Dw i)) ∧ (k : F) = ∑ i ∈ s, c i * n i := by
  obtain ⟨n, hn, hR⟩ := logSum_decomp (K := K) hp s c Nw Dw hND
  set ρ := ∑ i ∈ s, c i * (n i : F) with hρ
  have hrde' : y′ + (h′ + φ (C ρ) * (φ p′ / φ p) +
      (∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)) -
        φ (C ρ) * (φ p′ / φ p))) * y = g := by
    rw [← hrde]; ring
  rcases rde_pole_bound_res hp.prime hnorm (not_dvd_natCast_polynomial hp.prime) (C ρ)
      (fun k hk hdvd ↦ hk (by
        rw [← C_eq_natCast, ← C_sub] at hdvd
        rw [← C_eq_natCast, eq_zero_of_prime_dvd_C hp.prime hdvd |> sub_eq_zero.mp]))
      h y g _ hR E hg hrde' with h1 | ⟨k, hk, hρk, hyk⟩
  · exact Or.inl h1
  · refine Or.inr ⟨k, n, hk, hyk, hn, ?_⟩
    rw [← C_eq_natCast] at hρk
    exact (C_inj.mp hρk).symm

/-- **The normal denominator bound with a logarithmic part.** For a normal irreducible `p`,
`y · gcd(e, e′) · Lᴺ` is regular at `p`, where `g e` is regular at `p`, `G = s₁ e + t₁ e′`,
`p ∣ L` whenever `p` divides some `Nᵢ Dᵢ`, and `N` bounds every positive integer of the form
`∑ cᵢ nᵢ` with `|nᵢ| ≤ deg Nᵢ + deg Dᵢ`. -/
theorem rde_log_denominator {p : F[X]} (hp : Irreducible p) (hnorm : ¬p ∣ p′) (h y g : K)
    {ι : Type*} (s : Finset ι) (c : ι → F) (Nw Dw : ι → F[X])
    (hND : ∀ i ∈ s, Nw i ≠ 0 ∧ Dw i ≠ 0) (e : F[X]) (he : e ≠ 0)
    (hge : g * φ e ∈ regularAt K p hp.prime) (G s1 t1 : F[X]) (hG : s1 * e + t1 * e′ = G)
    (L : F[X]) (hL : ∀ i ∈ s, p ∣ Nw i * Dw i → p ∣ L) (N : ℕ)
    (hN : ∀ (k : ℕ) (n : ι → ℤ), 0 < k →
      (∀ i ∈ s, |n i| ≤ (((Nw i).natDegree + (Dw i).natDegree : ℕ) : ℤ)) →
      (k : F) = ∑ i ∈ s, c i * n i → k ≤ N)
    (hrde : y′ + (h′ + ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i))) * y = g) :
    y * φ (G * L ^ N) ∈ regularAt K p hp.prime := by
  have hpp := hp.prime
  obtain ⟨j, e1, he1, hej⟩ := exists_pow_mul_not_dvd hpp he
  have hunit : IsUnitAt K p (φ e1) := isUnitAt_algebraMap hpp he1
  have hgj : g * φ p ^ j ∈ regularAt K p hpp := by
    have h1 := mul_mem hge (hunit.inv_mem_regularAt hpp)
    have hne : φ e1 ≠ 0 := map_ne_zero_of_not_dvd hpp he1
    rw [hej, map_mul, map_pow] at h1
    rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hne, mul_one] at h1
  -- the `k`-case
  have hkcase : ∀ E : ℕ, (∃ (k : ℕ) (n : ι → ℤ), E < k ∧ y * φ p ^ k ∈ regularAt K p hpp ∧
      (∀ i ∈ s, |n i| ≤ (((Nw i).natDegree + (Dw i).natDegree : ℕ) : ℤ) ∧
        (n i ≠ 0 → p ∣ Nw i * Dw i)) ∧ (k : F) = ∑ i ∈ s, c i * n i) →
      y * φ (G * L ^ N) ∈ regularAt K p hpp := by
    rintro E ⟨k, n, hk, hyk, hn, hkn⟩
    have hkN := hN k n (by omega) (fun i hi ↦ (hn i hi).1) hkn
    have hpL : p ∣ L := by
      by_contra hpL
      have : (k : F) = 0 := by
        rw [hkn]
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        by_cases hni : n i = 0
        · simp [hni]
        · exact absurd (hL i hi ((hn i hi).2 hni)) hpL
      exact absurd this (Nat.cast_ne_zero.mpr (by omega))
    obtain ⟨q, hq⟩ : p ^ k ∣ G * L ^ N :=
      dvd_mul_of_dvd_right ((pow_dvd_pow p hkN).trans (pow_dvd_pow_of_dvd hpL N)) _
    rw [hq, map_mul, map_pow, ← mul_assoc]
    exact mul_mem hyk (algebraMap_mem_regularAt _ _)
  cases j with
  | zero =>
    rcases rde_log_normal hp hnorm h y g s c Nw Dw hND 0 (by
        rw [zero_add, pow_one]
        have h2 := mul_mem hgj (algebraMap_mem_regularAt hpp p)
        rwa [pow_zero, mul_one] at h2) hrde with h1 | h1
    · rw [pow_zero, mul_one] at h1
      exact mul_mem h1 (algebraMap_mem_regularAt _ _)
    · exact hkcase 0 h1
  | succ E =>
    rcases rde_log_normal hp hnorm h y g s c Nw Dw hND E hgj hrde with h1 | h1
    · have hpe : p ^ E ∣ e := ⟨p * e1, by rw [hej]; ring⟩
      have hpe' : p ^ E ∣ e′ := by
        rw [hej]
        have := pow_dvd_deriv_pow_succ_mul (Derivation.restrictScalars ℤ
          (Differential.deriv : Derivation ℤ F[X] F[X])) p e1 E
        simpa using this
      have hpG : p ^ E ∣ G := hG ▸ dvd_add (dvd_mul_of_dvd_right hpe _) (dvd_mul_of_dvd_right hpe' _)
      obtain ⟨q, hq⟩ : p ^ E ∣ G * L ^ N := dvd_mul_of_dvd_left hpG _
      rw [hq, map_mul, map_pow, ← mul_assoc]
      exact mul_mem h1 (algebraMap_mem_regularAt _ _)
    · exact hkcase E h1

end Poly

section Exp

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K
local notation "RX" => regularAt K (X : F[X]) prime_X

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
include hDe

/-- **The special bound, `h` regular at `t`, with an extra regular term `R ≡ r₀`.** -/
theorem rde_special_bound_reg_R (h y g R : K) (ε ε' : ℕ) (hεε : ε ≤ ε')
    (hg : g * φ (X ^ ε) ∈ RX) (h0 : F) (rh : K) (hrh : rh ∈ RX) (hh : h = φ (C h0) + φ X * rh)
    (r0 : F) (rR : K) (hrR : rR ∈ RX) (hR : R = φ (C r0) + φ X * rR)
    (hno : ∀ k : ℕ, ε' < k → ∀ e : F, e ≠ 0 → e′ + (h0′ + r0 - k * b) * e ≠ 0)
    (hrde : y′ + (h′ + R) * y = g) : y * φ (X ^ ε') ∈ RX := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact zero_mem _
  rcases mem_X_pow_regular_or (F := F) (K := K) hy0 ε' with hreg | ⟨k, u, hk, hu, rfl⟩
  · exact hreg
  exfalso
  obtain ⟨u0, ru, hru, hu'⟩ := exists_val_of_mem_regularAt (hu.mem_regularAt prime_X)
  have hu0 := val_ne_zero_of_isUnitAt hru hu' hu
  obtain ⟨r1, hr1, hu1⟩ := deriv_val hDe hru hu'
  obtain ⟨r2, hr2, hh1⟩ := deriv_val hDe hrh hh
  have hgk : g * φ (X ^ k) = φ (C (u0′ + (h0′ + r0 - k * b) * u0)) +
      φ X * (r1 - φ (C ((k : F) * b)) * ru + φ (C h0′) * ru + r2 * u + rR * u +
        φ (C r0) * ru) := by
    rw [← hrde, add_mul, deriv_div_X_pow hDe]
    have hX0 : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
    have e1 : (h′ + R) * (u / φ (X ^ k)) * φ (X ^ k) = (h′ + R) * u := by field_simp
    rw [e1, hu1, hh1, hR, hu']
    simp only [map_add, map_mul, map_sub, C_add, C_mul, C_sub]
    ring
  have hunit := isUnitAt_of_val (add_mem (add_mem (add_mem (add_mem (sub_mem hr1 (mul_mem
    (algebraMap_mem_regularAt _ _) hru)) (mul_mem (algebraMap_mem_regularAt _ _) hru))
    (mul_mem hr2 (hu.mem_regularAt prime_X))) (mul_mem hrR (hu.mem_regularAt prime_X)))
    (mul_mem (algebraMap_mem_regularAt _ _) hru)) hgk (hno k hk u0 hu0)
  obtain ⟨j, rfl⟩ : ∃ j, k = ε + 1 + j := ⟨k - (ε + 1), by omega⟩
  refine hunit.ne_mul prime_X (f := g * φ (X ^ ε) * φ (X ^ j))
    (mul_mem hg (algebraMap_mem_regularAt _ _)) ?_
  simp only [map_pow]
  ring

/-- **The special bound, `h` with a pole at `t`, with an extra regular term `R`.** -/
theorem rde_special_bound_pole_R (hhom : ∀ l : ℕ, l ≠ 0 → ∀ e : F, e ≠ 0 → e′ ≠ l * b * e)
    (h y g R : K) (ε : ℕ) (hg : g * φ (X ^ ε) ∈ RX) (hh : h ∉ RX) (hR : R ∈ RX)
    (hrde : y′ + (h′ + R) * y = g) : y * φ (X ^ ε) ∈ RX := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact zero_mem _
  rcases mem_X_pow_regular_or (F := F) (K := K) hy0 ε with hreg | ⟨k, u, hk, hu, rfl⟩
  · exact hreg
  exfalso
  have hh0 : h ≠ 0 := fun h0 ↦ hh (h0 ▸ zero_mem _)
  rcases mem_X_pow_regular_or (F := F) (K := K) hh0 0 with hreg | ⟨l, v, hl, hv, rfl⟩
  · exact hh (by simpa using hreg)
  obtain ⟨v0, rv, hrv, hv'⟩ := exists_val_of_mem_regularAt (hv.mem_regularAt prime_X)
  have hv0 := val_ne_zero_of_isUnitAt hrv hv' hv
  obtain ⟨r1, hr1, hv1⟩ := deriv_val hDe hrv hv'
  have hV : (v / φ (X ^ l))′ * φ (X ^ l) = φ (C (v0′ - l * b * v0)) +
      φ X * (r1 - φ (C ((l : F) * b)) * rv) := by
    rw [deriv_div_X_pow hDe, hv1, hv']
    simp only [map_add, map_mul, map_sub, C_add, C_mul, C_sub]
    ring
  have hVu := isUnitAt_of_val (sub_mem hr1 (mul_mem (algebraMap_mem_regularAt _ _) hrv)) hV
    (sub_ne_zero.mpr (hhom l (by omega) v0 hv0))
  have hgk : g * φ (X ^ k) * φ (X ^ l) =
      ((u / φ (X ^ k))′ * φ (X ^ k)) * φ (X ^ l) + ((v / φ (X ^ l))′ * φ (X ^ l)) * u +
        R * u * φ (X ^ l) := by
    rw [← hrde]
    have hX0 : ∀ n, φ (X ^ n : F[X]) ≠ 0 := fun n ↦
      (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
    have := hX0 k
    have := hX0 l
    field_simp
    ring
  obtain ⟨j, rfl⟩ : ∃ j, k = ε + 1 + j := ⟨k - (ε + 1), by omega⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  refine (hVu.mul' prime_X hu).ne_mul prime_X (f := g * φ (X ^ ε) * φ (X ^ j) * φ (X ^ (l' + 1)) -
    ((u / φ (X ^ (ε + 1 + j)))′ * φ (X ^ (ε + 1 + j))) * φ (X ^ l') - R * u * φ (X ^ l'))
    (sub_mem (sub_mem (mul_mem (mul_mem hg (algebraMap_mem_regularAt _ _))
      (algebraMap_mem_regularAt _ _))
      (mul_mem (by rw [deriv_div_X_pow hDe]; exact sub_mem (deriv_mem_regularAt _
        (hu.mem_regularAt _)) (mul_mem (algebraMap_mem_regularAt _ _) (hu.mem_regularAt _)))
        (algebraMap_mem_regularAt _ _)))
      (mul_mem (mul_mem hR (hu.mem_regularAt _)) (algebraMap_mem_regularAt _ _))) ?_
  simp only [map_pow] at hgk ⊢
  linear_combination -hgk

/-- The value at `t = 0` of `(tᵃ N₁)′ / (tᵃ N₁)`, `t ∤ N₁`: `a b + N₁(0)′ / N₁(0)`. -/
lemma logDeriv_val_X (N N1 : F[X]) (a : ℕ) (hN : N = X ^ a * N1) (hX : ¬X ∣ N1) :
    ∃ r : K, r ∈ RX ∧
      logDeriv (φ N) = φ (C (a * b + (N1.coeff 0)′ / N1.coeff 0)) + φ X * r := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hN10 : N1 ≠ 0 := fun h0 ↦ hX (h0 ▸ dvd_zero _)
  have hn0 : N1.coeff 0 ≠ 0 := fun h0 ↦ hX (X_dvd_iff.mpr h0)
  have hφX : φ (X : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hφN1 : φ N1 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hN10
  obtain ⟨Q1, hQ1⟩ : X ∣ N1 - C (N1.coeff 0) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, sub_self]
  have hN1v : φ N1 = φ (C (N1.coeff 0)) + φ X * φ Q1 := by
    rw [← map_mul, ← hQ1, ← map_add]; ring_nf
  obtain ⟨r1, hr1, hd1⟩ := deriv_val hDe (algebraMap_mem_regularAt prime_X Q1) hN1v
  have hunit : IsUnitAt K (X : F[X]) (φ N1) := isUnitAt_algebraMap prime_X hX
  have hlX : logDeriv (φ (X : F[X])) = φ (C b) := by
    rw [logDeriv, deriv_algebraMap, hDe, implicitDeriv_X, map_mul]
    field_simp
  refine ⟨(r1 - φ (C ((N1.coeff 0)′ / N1.coeff 0)) * φ Q1) * (φ N1)⁻¹, mul_mem (sub_mem hr1
    (mul_mem (algebraMap_mem_regularAt _ _) (algebraMap_mem_regularAt _ _)))
    (hunit.inv_mem_regularAt prime_X), ?_⟩
  rw [hN, map_mul, map_pow, logDeriv_mul _ _ (pow_ne_zero _ hφX) hφN1, logDeriv_pow, hlX]
  have hl1 : logDeriv (φ N1) = (φ (C ((N1.coeff 0)′)) + φ X * r1) / φ N1 := by
    rw [logDeriv, hd1]
  rw [hl1]
  have hc : φ (C ((N1.coeff 0)′ / N1.coeff 0)) * φ (C (N1.coeff 0)) = φ (C ((N1.coeff 0)′)) := by
    rw [← map_mul, ← C_mul, div_mul_cancel₀ _ hn0]
  simp only [C_add, C_mul, map_add, map_mul, map_natCast]
  rw [add_assoc]
  congr 1
  rw [div_eq_iff hφN1, add_mul, mul_assoc (φ X), mul_assoc, inv_mul_cancel₀ hφN1, mul_one]
  rw [hN1v]
  linear_combination -hc

/-- The value at `t = 0` of a logarithmic part `∑ cᵢ (Nᵢ / Dᵢ)′ / (Nᵢ / Dᵢ)`. -/
lemma logSum_val_X {ι : Type*} (s : Finset ι) (c : ι → F) (Nw Dw N1 D1 : ι → F[X]) (a d : ι → ℕ)
    (hN : ∀ i ∈ s, Nw i = X ^ a i * N1 i ∧ ¬X ∣ N1 i)
    (hD : ∀ i ∈ s, Dw i = X ^ d i * D1 i ∧ ¬X ∣ D1 i) :
    ∃ r : K, r ∈ RX ∧ ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)) =
      φ (C (∑ i ∈ s, c i * (((a i : F) - d i) * b + ((N1 i).coeff 0)′ / (N1 i).coeff 0 -
        ((D1 i).coeff 0)′ / (D1 i).coeff 0))) + φ X * r := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hv : ∀ i ∈ s, ∃ r : K, r ∈ RX ∧ logDeriv (φ (Nw i) / φ (Dw i)) =
      φ (C (((a i : F) - d i) * b + ((N1 i).coeff 0)′ / (N1 i).coeff 0 -
        ((D1 i).coeff 0)′ / (D1 i).coeff 0)) + φ X * r := by
    intro i hi
    obtain ⟨rN, hrN, hlN⟩ := logDeriv_val_X hDe (K := K) _ _ _ (hN i hi).1 (hN i hi).2
    obtain ⟨rD, hrD, hlD⟩ := logDeriv_val_X hDe (K := K) _ _ _ (hD i hi).1 (hD i hi).2
    have hN0 : φ (Nw i) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ hinj, (hN i hi).1]
      exact mul_ne_zero (pow_ne_zero _ X_ne_zero) fun h0 ↦ (hN i hi).2 (h0 ▸ dvd_zero _)
    have hD0 : φ (Dw i) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ hinj, (hD i hi).1]
      exact mul_ne_zero (pow_ne_zero _ X_ne_zero) fun h0 ↦ (hD i hi).2 (h0 ▸ dvd_zero _)
    refine ⟨rN - rD, sub_mem hrN hrD, ?_⟩
    rw [logDeriv_div _ _ hN0 hD0, hlN, hlD]
    simp only [map_add, map_sub, map_mul, map_div₀, map_natCast, C_add, C_sub, C_mul]
    ring
  choose! r hr using hv
  refine ⟨∑ i ∈ s, φ (C (c i)) * r i, Subring.sum_mem _ fun i hi ↦
    mul_mem (algebraMap_mem_regularAt _ _) (hr i hi).1, ?_⟩
  rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [(hr i hi).2]
  simp only [map_mul]
  ring

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
omit hDe in
lemma infVal_C_mul {z : K} {v : F} (hz : InfVal z v) (c : F) : InfVal (φ (C c) * z) (c * v) := by
  obtain ⟨P, R, hR, hPR, rfl, hc⟩ := hz
  refine ⟨C c * P, R, hR, (natDegree_C_mul_le _ _).trans hPR, by rw [map_mul]; ring, ?_⟩
  rw [coeff_C_mul, hc]; ring

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
omit hDe in
lemma infVal_zero : InfVal (0 : K) (0 : F) :=
  ⟨0, 1, one_ne_zero, by simp, by simp, by simp⟩

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
omit hDe in
lemma infVal_sum {ι : Type*} (s : Finset ι) (z : ι → K) (v : ι → F)
    (hz : ∀ i ∈ s, InfVal (z i) (v i)) : InfVal (∑ i ∈ s, z i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using infVal_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact infVal_add (hz j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ hz i (Finset.mem_insert_of_mem hi))

omit [CharZero F] in
/-- The value at infinity of a logarithmic part:
`∑ cᵢ ((deg Nᵢ - deg Dᵢ) b + lc(Nᵢ)′ / lc(Nᵢ) - lc(Dᵢ)′ / lc(Dᵢ))`. -/
lemma infVal_logSum {ι : Type*} (s : Finset ι) (c : ι → F) (Nw Dw : ι → F[X])
    (hND : ∀ i ∈ s, Nw i ≠ 0 ∧ Dw i ≠ 0) :
    InfVal (∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)))
      (∑ i ∈ s, c i * ((((Nw i).natDegree : F) - (Dw i).natDegree) * b +
        (Nw i).leadingCoeff′ / (Nw i).leadingCoeff - (Dw i).leadingCoeff′ / (Dw i).leadingCoeff)) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  refine infVal_sum _ _ _ fun i hi ↦ infVal_C_mul ?_ _
  have hN0 : φ (Nw i) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hND i hi).1
  have hD0 : φ (Dw i) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hND i hi).2
  rw [logDeriv_div _ _ hN0 hD0, logDeriv, logDeriv]
  have := infVal_sub (infVal_logDeriv hDe (K := K) _ (hND i hi).1)
    (infVal_logDeriv hDe (K := K) _ (hND i hi).2)
  convert this using 1
  ring

end Exp

end Differential
