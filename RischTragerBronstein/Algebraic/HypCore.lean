import RischTragerBronstein.RDE.LogBounds
import RischTragerBronstein.RDE.RationalCoeffW

/-!
# Hyperelliptic integrals without logarithmic part: the core argument in `C(x)`

Let `K = C(x)(y)`, `y² = p`, `p ∈ C[x]` squarefree of odd degree. Taking the `y`-component of a
Liouville identity `B₀ / y = v′ + ∑ cᵢ uᵢ′ / uᵢ` (`v = α + e y`, `uᵢ = λᵢ (aᵢ + bᵢ y)` with
`aᵢ, bᵢ ∈ C[x]` coprime) gives, in `C(x)`,

  `2 B₀ = 2 p e′ + p′ e + ∑ cᵢ Mᵢ / Nᵢ`,  `Nᵢ = aᵢ² - bᵢ² p`,  `Mᵢ = 2p(aᵢbᵢ′ - aᵢ′bᵢ) + aᵢbᵢp′`.

`hyp_core`: if the `cᵢ` are `ℚ`-linearly independent and `deg B₀ ≤ deg p - 2`, then `B₀ = 0`.
The logarithmic terms have at most simple poles (`q_mul_MN_mem`), `e` has no pole outside `p`
(`not_mem_eterm_of_pole`), the residues at `q ∤ p` are `∓ mᵢ √p` and cancel only if every
`mᵢ = 0` (`not_dvd_N_of_regular`, by `ℚ`-independence), so every `Nᵢ` divides `p`, which by
parity forces `aᵢ = 0` or `bᵢ = 0`, i.e. `Mᵢ = 0` (`M_eq_zero`); finally `2B₀ = 2pe′ + p′e` has no
polynomial solution but `e = 0` in the degree range (`e_eq_zero`).
-/

open Polynomial

namespace Differential

section Core

variable {F K : Type*} [Field F] [CharZero F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- `N = a² - b² p`. -/
noncomputable def hN (p a b : F[X]) : F[X] := a ^ 2 - b ^ 2 * p

/-- `M = 2p(ab′ - a′b) + abp′`. -/
noncomputable def hM (p a b : F[X]) : F[X] :=
  2 * p * (a * derivative b - derivative a * b) + a * b * derivative p

omit [CharZero F] [Differential F[X]] in
lemma hyp_bM (p a b : F[X]) :
    b * hM p a b = 2 * derivative a * hN p a b - a * derivative (hN p a b) := by
  simp only [hN, hM, derivative_sub, derivative_pow, derivative_mul]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, map_ofNat C 2]
  ring

omit [CharZero F] [Differential F[X]] in
lemma hyp_aM (p a b : F[X]) :
    a * hM p a b = hN p a b * (2 * p * derivative b + b * derivative p) -
      p * b * derivative (hN p a b) := by
  simp only [hN, hM, derivative_sub, derivative_pow, derivative_mul]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, map_ofNat C 2]
  ring

variable (hder : ∀ P : F[X], P′ = derivative P)
include hder

omit [CharZero F] in
/-- `q · (N′ / N)` is regular at `q`. -/
lemma q_mul_logDeriv_mem {q : F[X]} (hq : Prime q) {N : F[X]} (hN0 : N ≠ 0) :
    φ q * (φ (derivative N) / φ N) ∈ regularAt K q hq := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hφN : φ N ≠ 0 := (map_ne_zero_iff _ hinj).mpr hN0
  obtain ⟨n, hn⟩ := logDeriv_sub_mem_regularAt (K := K) hq hφN
  have hq0 : φ q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq.ne_zero
  have e : φ q * (φ (derivative N) / φ N) = φ q * (logDeriv (φ N) - n * (φ q′ / φ q)) +
      n * φ q′ := by
    rw [logDeriv, deriv_algebraMap, hder]
    field_simp
    ring
  rw [e]
  exact add_mem (mul_mem (algebraMap_mem_regularAt _ _) hn)
    (mul_mem (intCast_mem _ _) (algebraMap_mem_regularAt _ _))

omit [CharZero F] in
/-- **The logarithmic terms have at most simple poles.** -/
lemma q_mul_MN_mem {q : F[X]} (hq : Prime q) (p a b : F[X]) (hab : IsCoprime a b)
    (hN0 : hN p a b ≠ 0) : φ q * (φ (hM p a b) / φ (hN p a b)) ∈ regularAt K q hq := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hφN : φ (hN p a b) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hN0
  have hL := q_mul_logDeriv_mem (K := K) hder hq hN0
  by_cases hqb : q ∣ b
  · have hqa : ¬q ∣ a := fun hqa ↦ hq.not_isUnit (hab.isUnit_of_dvd' hqa hqb)
    have hua := (isUnitAt_algebraMap (K := K) hq hqa)
    have hφa : φ a ≠ 0 := map_ne_zero_of_not_dvd hq hqa
    have e : φ q * (φ (hM p a b) / φ (hN p a b)) = (φ a)⁻¹ * (φ q * φ (2 * p * derivative b +
        b * derivative p) - φ (p * b) * (φ q * (φ (derivative (hN p a b)) / φ (hN p a b)))) := by
      have h1 : φ a * φ (hM p a b) = φ (hN p a b) * φ (2 * p * derivative b + b * derivative p) -
          φ (p * b) * φ (derivative (hN p a b)) := by
        rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, hyp_aM]
      field_simp
      linear_combination (φ q) * h1
    rw [e]
    exact mul_mem (hua.inv_mem_regularAt hq) (sub_mem (mul_mem (algebraMap_mem_regularAt _ _)
      (algebraMap_mem_regularAt _ _)) (mul_mem (algebraMap_mem_regularAt _ _) hL))
  · have hub := (isUnitAt_algebraMap (K := K) hq hqb)
    have hφb : φ b ≠ 0 := map_ne_zero_of_not_dvd hq hqb
    have e : φ q * (φ (hM p a b) / φ (hN p a b)) = (φ b)⁻¹ * (φ q * φ (2 * derivative a) -
        φ a * (φ q * (φ (derivative (hN p a b)) / φ (hN p a b)))) := by
      have h1 : φ b * φ (hM p a b) = φ (2 * derivative a) * φ (hN p a b) -
          φ a * φ (derivative (hN p a b)) := by
        rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, hyp_bM]
      field_simp
      linear_combination (φ q) * h1
    rw [e]
    exact mul_mem (hub.inv_mem_regularAt hq) (sub_mem (mul_mem (algebraMap_mem_regularAt _ _)
      (algebraMap_mem_regularAt _ _)) (mul_mem (algebraMap_mem_regularAt _ _) hL))

omit [CharZero F] in
/-- **The residue at a simple zero structure**: if `N = qᵐ N₁` (`q ∤ N₁`) and `q ∤ b`, then
`b M / N + m a q′ / q` is regular at `q`. -/
lemma residue_MN {q : F[X]} (hq : Prime q) (p a b : F[X]) (hqb : ¬q ∣ b) (m : ℕ) (N1 : F[X])
    (hN1 : ¬q ∣ N1) (hNq : hN p a b = q ^ m * N1) :
    φ b * (φ (hM p a b) / φ (hN p a b)) + (m : K) * φ a * (φ (derivative q) / φ q) ∈
      regularAt K q hq := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hq0 : φ q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq.ne_zero
  have hN10 : φ N1 ≠ 0 := map_ne_zero_of_not_dvd hq hN1
  have hφN : φ (hN p a b) ≠ 0 := by rw [hNq, map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero _ hq0) hN10
  have hu := isUnitAt_algebraMap (K := K) hq hN1
  have hreg1 : φ (derivative N1) / φ N1 ∈ regularAt K q hq := by
    rw [div_eq_mul_inv]
    have := deriv_mem_regularAt hq (algebraMap_mem_regularAt (K := K) hq N1)
    rw [deriv_algebraMap, hder] at this
    exact mul_mem this (hu.inv_mem_regularAt hq)
  have e : φ b * (φ (hM p a b) / φ (hN p a b)) + (m : K) * φ a * (φ (derivative q) / φ q) =
      φ (2 * derivative a) - φ a * (φ (derivative N1) / φ N1) := by
    have h1 : φ b * φ (hM p a b) = φ (2 * derivative a) * φ (hN p a b) -
        φ a * φ (derivative (hN p a b)) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, hyp_bM]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [pow_zero, one_mul] at hNq
      rw [← mul_div_assoc, h1, hNq]
      field_simp
      simp only [Nat.cast_zero, zero_mul, add_zero, map_mul]
      ring
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hd : φ (derivative (hN p a b)) = ((m' + 1 : ℕ) : K) * φ q ^ m' * φ (derivative q) *
          φ N1 + φ q ^ (m' + 1) * φ (derivative N1) := by
        rw [hNq, derivative_mul, derivative_pow]
        simp only [map_add, map_mul, map_pow, map_natCast, Nat.add_sub_cancel]
      have hNv : φ (hN p a b) = φ q ^ (m' + 1) * φ N1 := by rw [hNq, map_mul, map_pow]
      rw [← mul_div_assoc, h1, hd, hNv, map_mul]
      field_simp
      ring
  rw [e]
  exact sub_mem (algebraMap_mem_regularAt _ _) (mul_mem (algebraMap_mem_regularAt _ _) hreg1)

omit [CharZero F] in
lemma pole_form {q : F[X]} (hq : Prime q) {e : K} (he : e ∉ regularAt K q hq) :
    ∃ (k : ℕ) (u : K), 1 ≤ k ∧ IsUnitAt K q u ∧ e = u / φ q ^ k := by
  have hpm : φ q ∈ regularAt K q hq := algebraMap_mem_regularAt hq q
  have he0 : e ≠ 0 := fun h0 ↦ he (h0 ▸ zero_mem _)
  obtain ⟨n, u, hu, rfl⟩ := exists_zpow_mul_isUnitAt hq he0
  have hn : n < 0 := by
    by_contra hn
    obtain ⟨j, hj⟩ : ∃ j : ℕ, n = j := ⟨n.toNat, by omega⟩
    refine he ?_
    rw [hj, zpow_natCast]
    exact mul_mem (pow_mem hpm _) (hu.mem_regularAt hq)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
  refine ⟨k, u, by omega, hu, ?_⟩
  rw [hk, zpow_neg, zpow_natCast]
  field_simp

/-- **`e` has no pole at a prime `q ∤ p`**: otherwise `2pe′ + p′e` has a pole of order `≥ 2`. -/
lemma not_mem_eterm_of_pole {q : F[X]} (hq : Prime q) (hnorm : ¬q ∣ derivative q) (p : F[X])
    (hqp : ¬q ∣ p) {e : K} (he : e ∉ regularAt K q hq) :
    φ q * (φ (2 * p) * e′ + φ (derivative p) * e) ∉ regularAt K q hq := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hq0 : φ q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq.ne_zero
  have hpm : φ q ∈ regularAt K q hq := algebraMap_mem_regularAt hq q
  obtain ⟨k, u, hk, hu, rfl⟩ := pole_form hder hq he
  have hnorm' : ¬q ∣ q′ := by rw [hder]; exact hnorm
  have hU := isUnitAt_deriv_pole hq hnorm' hu k (not_dvd_natCast_polynomial hq k (by omega))
  have h2p : ¬q ∣ 2 * p := fun h ↦ (hq.dvd_or_dvd h).elim
    (fun h2 ↦ not_dvd_natCast_polynomial hq 2 (by norm_num) (by exact_mod_cast h2)) hqp
  have hunit := (isUnitAt_algebraMap (K := K) hq h2p).mul' hq hU
  intro hX
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine hunit.ne_mul hq (f := φ q * (φ (2 * p) * (u / φ q ^ (j + 1))′ +
      φ (derivative p) * (u / φ q ^ (j + 1))) * φ q ^ j - φ (derivative p) * u)
    (sub_mem (mul_mem hX (pow_mem hpm _)) (mul_mem (algebraMap_mem_regularAt _ _)
      (hu.mem_regularAt hq))) ?_
  have hqj : φ q ^ (j + 1) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  ring

/-- **`e` has at most a simple pole at a prime `q ∣ p`** (`p = q p₁`, `q ∤ p₁`): otherwise
`2pe′ + p′e` has a pole of the same order `k ≥ 1` (coefficient `(1 - 2k) p₁ q′ ≠ 0`). Here in the
form: a pole of `e` makes `2pe′ + p′e` non-regular. -/
lemma not_mem_eterm_of_pole_ram {q : F[X]} (hq : Prime q) (hnorm : ¬q ∣ derivative q)
    (p1 : F[X]) (hqp1 : ¬q ∣ p1) {e : K} (he : e ∉ regularAt K q hq) :
    φ (2 * (q * p1)) * e′ + φ (derivative (q * p1)) * e ∉ regularAt K q hq := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hq0 : φ q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq.ne_zero
  have hpm : φ q ∈ regularAt K q hq := algebraMap_mem_regularAt hq q
  obtain ⟨k, u, hk, hu, rfl⟩ := pole_form hder hq he
  have hc : ¬q ∣ C ((1 : F) - 2 * k) := by
    intro h
    have := eq_zero_of_prime_dvd_C hq h
    have h2 : (2 * k : F) = 1 := by linear_combination -this
    have h3 : ((2 * k : ℕ) : F) = ((1 : ℕ) : F) := by push_cast; exact h2
    have := Nat.cast_injective h3
    omega
  have hunit : IsUnitAt K q (φ (C ((1 : F) - 2 * k)) * φ p1 * φ (derivative q) * u) :=
    (((isUnitAt_algebraMap (K := K) hq hc).mul' hq (isUnitAt_algebraMap hq hqp1)).mul' hq
      (isUnitAt_algebraMap hq hnorm)).mul' hq hu
  intro hX
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hU := deriv_div_pow_mul u (j + 1) hq0
  rw [hder] at hU
  refine hunit.ne_mul hq (f := (φ (2 * (q * p1)) * (u / φ q ^ (j + 1))′ +
      φ (derivative (q * p1)) * (u / φ q ^ (j + 1))) * φ q ^ j - φ (2 * p1) * u′ -
      φ (derivative p1) * u)
    (sub_mem (sub_mem (mul_mem hX (pow_mem hpm _)) (mul_mem (algebraMap_mem_regularAt _ _)
      (deriv_mem_regularAt hq (hu.mem_regularAt hq)))) (mul_mem (algebraMap_mem_regularAt _ _)
      (hu.mem_regularAt hq))) ?_
  have hqj : φ q ^ (j + 1) ≠ 0 := pow_ne_zero _ hq0
  have e1 : (u / φ q ^ (j + 1))′ = (u′ * φ q - ((j + 1 : ℕ) : K) * u * φ (derivative q)) /
      φ q ^ (j + 1 + 1) := by
    rw [← hU]; field_simp
  rw [e1, derivative_mul]
  simp only [map_mul, map_add, map_sub, map_natCast, map_ofNat, C_sub, C_mul, C_1, map_one]
  field_simp
  push_cast
  ring

omit [Differential K] [DifferentialAlgebra F[X] K] in
omit hder in
/-- In the residue field `F[X]/(q)`: if the square of `a/b` is `p` for every `i` and
`∑ cᵢ mᵢ aᵢ Pᵢ ≡ 0` with `bᵢ Pᵢ = P`, then `∑ cᵢ mᵢ εᵢ = 0` for signs `εᵢ`. -/
lemma residue_field_signs {q : F[X]} (hq : Irreducible q) (p : F[X]) (hqp : ¬q ∣ p)
    {ι : Type*} (s' : Finset ι) (c : ι → F) (m : ι → ℕ) (a b Pi : ι → F[X]) (P : F[X])
    (hqb : ∀ i ∈ s', ¬q ∣ b i) (hbP : ∀ i ∈ s', b i * Pi i = P) (hqP : ¬q ∣ P)
    (hN : ∀ i ∈ s', q ∣ a i ^ 2 - b i ^ 2 * p)
    (hsum : q ∣ ∑ i ∈ s', C (c i * m i) * Pi i * a i) :
    ∃ ε : ι → ℤ, (∀ i ∈ s', ε i = 1 ∨ ε i = -1) ∧ ∑ i ∈ s', c i * ((m i : ℤ) * ε i : ℤ) = 0 := by
  classical
  haveI : Fact (Irreducible q) := ⟨hq⟩
  set π := AdjoinRoot.mk q with hπ
  have hz : ∀ f : F[X], π f = 0 ↔ q ∣ f := fun f ↦ AdjoinRoot.mk_eq_zero
  have hbn : ∀ i ∈ s', π (b i) ≠ 0 := fun i hi h0 ↦ hqb i hi ((hz _).mp h0)
  have hsq : ∀ i ∈ s', (π (a i) / π (b i)) ^ 2 = π p := by
    intro i hi
    have := (hz _).mpr (hN i hi)
    rw [map_sub, map_mul, map_pow, map_pow, sub_eq_zero] at this
    rw [div_pow, this]
    field_simp [hbn i hi]
  by_cases hs : s'.Nonempty
  swap
  · refine ⟨fun _ ↦ 1, fun i hi ↦ absurd ⟨i, hi⟩ hs, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
  obtain ⟨i0, hi0⟩ := hs
  set t := π (a i0) / π (b i0) with ht
  have htp : t ^ 2 = π p := hsq i0 hi0
  have ht0 : t ≠ 0 := fun h0 ↦ hqp ((hz _).mp (by rw [← htp, h0]; ring))
  have hsign : ∀ i ∈ s', π (a i) / π (b i) = t ∨ π (a i) / π (b i) = -t := by
    intro i hi
    exact sq_eq_sq_iff_eq_or_eq_neg.mp ((hsq i hi).trans htp.symm)
  refine ⟨fun i ↦ if π (a i) / π (b i) = t then 1 else -1, fun i _ ↦ by beta_reduce; split_ifs <;> simp, ?_⟩
  have hπsum := (hz _).mpr hsum
  -- rewrite each term with `aᵢ = εᵢ t bᵢ`
  have hterm : ∀ i ∈ s', π (C (c i * m i) * Pi i * a i) =
      t * π P * algebraMap F (AdjoinRoot q) (c i * ((m i : ℤ) *
        (if π (a i) / π (b i) = t then 1 else -1 : ℤ) : ℤ)) := by
    intro i hi
    obtain ⟨σ, hσ1, hai⟩ : ∃ σ : ℤ, (if π (a i) / π (b i) = t then (1 : ℤ) else -1) = σ ∧
        π (a i) = (σ : AdjoinRoot q) * t * π (b i) := by
      refine ⟨_, rfl, ?_⟩
      split_ifs with h
      · rw [div_eq_iff (hbn i hi)] at h; rw [h]; push_cast; ring
      · have h' := (hsign i hi).resolve_left h
        rw [div_eq_iff (hbn i hi)] at h'; rw [h']; push_cast; ring
    rw [hσ1, map_mul, map_mul, hai, ← hbP i hi]
    simp only [map_mul, hπ, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq, map_natCast, map_intCast]
    push_cast
    ring
  rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum] at hπsum
  have hP0 : π P ≠ 0 := fun h0 ↦ hqP ((hz _).mp h0)
  have := (mul_eq_zero.mp hπsum).resolve_left (mul_ne_zero ht0 hP0)
  exact (map_eq_zero_iff _ (algebraMap F (AdjoinRoot q)).injective).mp this

/-- **The residues vanish**: if the logarithmic part `∑ cᵢ Mᵢ / Nᵢ` is regular at an irreducible
`q ∤ p` and the `cᵢ` are `ℚ`-independent, then `q` divides no `Nᵢ`. -/
lemma not_dvd_N_of_regular {q : F[X]} (hq : Irreducible q) (hnorm : ¬q ∣ derivative q)
    (p : F[X]) (hqp : ¬q ∣ p) {ι : Type*} (s : Finset ι) (c : ι → F)
    (hc : ∀ g : ι → ℚ, ∑ i ∈ s, (g i : F) * c i = 0 → ∀ i ∈ s, g i = 0)
    (a b : ι → F[X]) (hab : ∀ i ∈ s, IsCoprime (a i) (b i))
    (hN0 : ∀ i ∈ s, hN p (a i) (b i) ≠ 0)
    (hreg : ∑ i ∈ s, φ (C (c i)) * (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) ∈
      regularAt K q hq.prime) :
    ∀ i ∈ s, ¬q ∣ hN p (a i) (b i) := by
  classical
  have hqp' := hq.prime
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hq0 : φ q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hqp'.ne_zero
  set s' := s.filter fun i ↦ q ∣ hN p (a i) (b i) with hs'
  -- on `s'`, `q ∤ bᵢ`
  have hqb : ∀ i ∈ s', ¬q ∣ b i := by
    intro i hi hdb
    obtain ⟨his, hdN⟩ := Finset.mem_filter.mp hi
    have hda : ¬q ∣ a i := fun hda ↦ hqp'.not_isUnit ((hab i his).isUnit_of_dvd' hda hdb)
    apply hda
    have : q ∣ a i ^ 2 := by
      have h1 : q ∣ b i ^ 2 * p := dvd_mul_of_dvd_left (dvd_pow hdb two_ne_zero) _
      have := dvd_add hdN h1
      simpa [hN] using this
    exact hqp'.dvd_of_dvd_pow this
  -- multiplicities
  have hmult : ∀ i ∈ s', ∃ (m : ℕ) (N1 : F[X]), 1 ≤ m ∧ ¬q ∣ N1 ∧
      hN p (a i) (b i) = q ^ m * N1 := by
    intro i hi
    obtain ⟨his, hdN⟩ := Finset.mem_filter.mp hi
    obtain ⟨m, N1, hN1, heq⟩ := exists_pow_mul_not_dvd hqp' (hN0 i his)
    refine ⟨m, N1, ?_, hN1, heq⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero, one_mul] at heq; rw [heq] at hdN; exact absurd hdN hN1
    · exact h0
  choose! m N1 hm1 hN1 hmN using hmult
  -- the regular rest
  have hrest : ∑ i ∈ s.filter (fun i ↦ ¬q ∣ hN p (a i) (b i)),
      φ (C (c i)) * (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) ∈ regularAt K q hqp' := by
    refine Subring.sum_mem _ fun i hi ↦ ?_
    obtain ⟨-, hnd⟩ := Finset.mem_filter.mp hi
    refine mul_mem (algebraMap_mem_regularAt _ _) ?_
    rw [div_eq_mul_inv]
    exact mul_mem (algebraMap_mem_regularAt _ _)
      ((isUnitAt_algebraMap (K := K) hqp' hnd).inv_mem_regularAt hqp')
  have hs'reg : ∑ i ∈ s', φ (C (c i)) * (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) ∈
      regularAt K q hqp' := by
    have := sub_mem hreg hrest
    rwa [← Finset.sum_filter_add_sum_filter_not s (fun i ↦ q ∣ hN p (a i) (b i)),
      add_sub_cancel_right] at this
  -- clear the `bᵢ`
  set P := ∏ i ∈ s', b i with hP
  set Pi : ι → F[X] := fun i ↦ ∏ j ∈ s'.erase i, b j with hPi
  have hbP : ∀ i ∈ s', b i * Pi i = P := fun i hi ↦ Finset.mul_prod_erase s' b hi
  have hqP : ¬q ∣ P := by
    rw [hP]
    intro h
    obtain ⟨i, hi, hd⟩ := (Prime.dvd_finset_prod_iff hqp' _).mp h
    exact hqb i hi hd
  have hres : ∀ i ∈ s', φ (b i) * (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) +
      (m i : K) * φ (a i) * (φ (derivative q) / φ q) ∈ regularAt K q hqp' :=
    fun i hi ↦ residue_MN hder hqp' p (a i) (b i) (hqb i hi) (m i) (N1 i) (hN1 i hi) (hmN i hi)
  have hsum_reg : φ (∑ i ∈ s', C (c i * m i) * Pi i * a i * derivative q) / φ q ∈
      regularAt K q hqp' := by
    have h1 := mul_mem (algebraMap_mem_regularAt (K := K) hqp' P) hs'reg
    have h2 : ∑ i ∈ s', φ (C (c i)) * φ (Pi i) * (φ (b i) *
        (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) + (m i : K) * φ (a i) *
          (φ (derivative q) / φ q)) ∈ regularAt K q hqp' :=
      Subring.sum_mem _ fun i hi ↦ mul_mem (mul_mem (algebraMap_mem_regularAt _ _)
        (algebraMap_mem_regularAt _ _)) (hres i hi)
    have e : φ (∑ i ∈ s', C (c i * m i) * Pi i * a i * derivative q) / φ q =
        ∑ i ∈ s', φ (C (c i)) * φ (Pi i) * (φ (b i) *
          (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) + (m i : K) * φ (a i) *
            (φ (derivative q) / φ q)) -
        φ P * ∑ i ∈ s', φ (C (c i)) * (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hbP i hi]
      simp only [map_mul, C_mul, map_natCast]
      ring
    rw [e]
    exact sub_mem h2 h1
  have hdvd : q ∣ ∑ i ∈ s', C (c i * m i) * Pi i * a i * derivative q :=
    dvd_of_algebraMap_eq_mul hqp' hsum_reg (by field_simp)
  have hdvd' : q ∣ ∑ i ∈ s', C (c i * m i) * Pi i * a i := by
    rw [← Finset.sum_mul] at hdvd
    exact (hqp'.dvd_or_dvd hdvd).resolve_right hnorm
  obtain ⟨ε, hε, hsum0⟩ := residue_field_signs hq p hqp s' c m a b Pi P hqb hbP hqP
    (fun i hi ↦ by simpa [hN] using (Finset.mem_filter.mp hi).2) hdvd'
  -- `ℚ`-independence
  have hg := hc (fun i ↦ if i ∈ s' then ((m i : ℤ) * ε i : ℚ) else 0) (by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i ↦ q ∣ hN p (a i) (b i))]
    rw [Finset.sum_eq_zero (s := s.filter fun i ↦ ¬q ∣ hN p (a i) (b i)) fun i hi ↦ by
      rw [if_neg (by rw [hs', Finset.mem_filter]; exact fun h ↦ (Finset.mem_filter.mp hi).2 h.2)]
      simp, add_zero]
    rw [← hs', ← hsum0]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [if_pos hi]
    push_cast
    ring)
  intro i his hdi
  have hi : i ∈ s' := Finset.mem_filter.mpr ⟨his, hdi⟩
  have := hg i his
  rw [if_pos hi] at this
  have hmε : (m i : ℤ) * ε i = 0 := by exact_mod_cast this
  rcases hε i hi with h | h <;> rw [h] at hmε <;> have := hm1 i hi <;> omega

omit [CharZero F] [Differential F[X]] [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]
  [Differential K] [DifferentialAlgebra F[X] K] in
omit hder in
/-- **A logarithmic term whose norm has all its primes in `p` vanishes** (parity of degrees). -/
lemma M_eq_zero (p : F[X]) (hp : Squarefree p) (hodd : Odd p.natDegree) (a b : F[X])
    (hab : IsCoprime a b) (hN0 : hN p a b ≠ 0)
    (hdiv : ∀ q : F[X], Irreducible q → ¬q ∣ p → ¬q ∣ hN p a b) : hM p a b = 0 := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  -- every prime of `N` divides `p`, and `N` is squarefree
  have h1 : ∀ q : F[X], Irreducible q → q ∣ hN p a b → q ∣ p := fun q hq hd ↦ by
    by_contra h; exact hdiv q hq h hd
  have h2 : ∀ q : F[X], Irreducible q → ¬q * q ∣ hN p a b := by
    intro q hq hqq
    have hqN : q ∣ hN p a b := dvd_trans (dvd_mul_right q q) hqq
    have hqp := h1 q hq hqN
    by_cases hqa : q ∣ a
    · have hqb : ¬q ∣ b := fun hqb ↦ hq.not_isUnit (hab.isUnit_of_dvd' hqa hqb)
      have hcop : IsCoprime (q * q) (b ^ 2) := by
        have := (Irreducible.coprime_iff_not_dvd hq).mpr hqb
        have := this.pow (m := 2) (n := 2)
        simpa [sq] using this
      have : q * q ∣ b ^ 2 * p := by
        have ha2 : q * q ∣ a ^ 2 := by rw [sq]; exact mul_dvd_mul hqa hqa
        have := dvd_sub ha2 hqq
        simpa [hN] using this
      have hqqp := hcop.dvd_of_dvd_mul_left this
      exact hq.not_isUnit (hp q hqqp)
    · apply hqa
      have : q ∣ a ^ 2 := by
        have := dvd_add hqN (dvd_mul_of_dvd_right hqp (b ^ 2))
        simpa [hN] using this
      exact hq.prime.dvd_of_dvd_pow this
  -- hence `N ∣ p`
  have hNp : hN p a b ∣ p := by
    obtain ⟨h, hh⟩ := gcd_dvd_left (hN p a b) p
    have hunit : IsUnit h := by
      by_contra hu
      have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hN0 hh
      obtain ⟨q, hq, hqh⟩ := WfDvdMonoid.exists_irreducible_factor hu hh0
      have hqN : q ∣ hN p a b := hh ▸ dvd_mul_of_dvd_right hqh _
      have hqg : q ∣ gcd (hN p a b) p := dvd_gcd hqN (h1 q hq hqN)
      exact h2 q hq (hh ▸ mul_dvd_mul hqg hqh)
    rw [hh]
    exact (IsUnit.mul_right_dvd hunit).mpr (gcd_dvd_right _ _)
  -- the degree argument
  by_cases ha : a = 0
  · simp [hM, ha]
  by_cases hb : b = 0
  · have hua : IsUnit a := isCoprime_zero_right.mp (hb ▸ hab)
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hua
    simp [hM, hb]
  exfalso
  set n := p.natDegree with hn
  have hdA : (a ^ 2).natDegree = 2 * a.natDegree := by rw [natDegree_pow]
  have hdB : (b ^ 2 * p).natDegree = 2 * b.natDegree + n := by
    rw [natDegree_mul (pow_ne_zero _ hb) hp0, natDegree_pow]
  have hne : 2 * a.natDegree ≠ 2 * b.natDegree + n := by
    obtain ⟨k, hk⟩ := hodd; omega
  have hdN : (hN p a b).natDegree = max (2 * a.natDegree) (2 * b.natDegree + n) := by
    unfold hN
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [natDegree_sub_eq_right_of_natDegree_lt (by rw [hdA, hdB]; exact hlt), hdB,
        max_eq_right hlt.le]
    · rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hdA, hdB]; exact hgt), hdA,
        max_eq_left hgt.le]
  have hle := natDegree_le_of_dvd hNp hp0
  rw [hdN] at hle
  have hdb : b.natDegree = 0 := by omega
  have hda : 2 * a.natDegree < n := by
    have := le_of_max_le_left hle; obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨k, hk⟩ := hNp
  have hNdeg : (hN p a b).natDegree = n := by rw [hdN]; omega
  have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hp0 hk
  have hkdeg : k.natDegree = 0 := by
    have := congrArg natDegree hk
    rw [natDegree_mul hN0 hk0, hNdeg] at this
    omega
  rw [natDegree_eq_zero] at hkdeg hdb
  obtain ⟨κ, rfl⟩ := hkdeg
  obtain ⟨β, rfl⟩ := hdb
  -- `a² = N + β² κ N`
  have ha2 : a ^ 2 = C (1 + β ^ 2 * κ) * hN p a (C β) := by
    have : hN p a (C β) = a ^ 2 - C β ^ 2 * p := rfl
    rw [C_add, C_1, C_mul, C_pow]
    linear_combination (C β ^ 2) * hk - this
  by_cases hc : 1 + β ^ 2 * κ = 0
  · rw [hc, C_0, zero_mul, pow_eq_zero_iff two_ne_zero] at ha2
    exact ha ha2
  · have := congrArg natDegree ha2
    rw [natDegree_C_mul hc, hNdeg, natDegree_pow] at this
    obtain ⟨j, hj⟩ := hodd
    omega

omit [Differential F[X]] [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]
  [Differential K] [DifferentialAlgebra F[X] K] in
omit hder in
/-- The top coefficient of `2 p E′ + p′ E`: degree `deg E + deg p - 1`, coefficient
`(2 deg E + deg p) lc(p) lc(E) ≠ 0`. -/
lemma coeff_top_eterm (p E : F[X]) (hp0 : 1 ≤ p.natDegree) (hE : E ≠ 0) :
    (2 * p * derivative E + derivative p * E).coeff (E.natDegree + (p.natDegree - 1)) =
      (2 * E.natDegree + p.natDegree : F) * p.leadingCoeff * E.leadingCoeff := by
  set n := p.natDegree
  set d := E.natDegree
  have h2 : (derivative p * E).coeff ((n - 1) + d) = (derivative p).coeff (n - 1) * E.coeff d :=
    coeff_mul_add_eq_of_natDegree_le (by
      have := natDegree_derivative_le p; omega) le_rfl
  have hdp : (derivative p).coeff (n - 1) = p.leadingCoeff * n := by
    rw [coeff_derivative, Nat.sub_add_cancel hp0, Nat.cast_sub hp0]
    simp only [Nat.cast_one, sub_add_cancel]
    rfl
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have hE' : derivative E = 0 := by
      rw [natDegree_eq_zero] at hd; obtain ⟨x, rfl⟩ := hd; simp
    rw [hE', mul_zero, zero_add, add_comm, h2, hdp, show E.coeff d = E.leadingCoeff from rfl,
      show (d : F) = 0 by simp [hd]]
    ring
  · have h1 : (2 * p * derivative E).coeff (n + (d - 1)) =
        (2 * p).coeff n * (derivative E).coeff (d - 1) :=
      coeff_mul_add_eq_of_natDegree_le (natDegree_mul_le.trans (by simp [n]))
        (by have := natDegree_derivative_le E; omega)
    have hdE : (derivative E).coeff (d - 1) = E.leadingCoeff * d := by
      rw [coeff_derivative, Nat.sub_add_cancel hd, Nat.cast_sub hd]
      simp only [Nat.cast_one, sub_add_cancel]
      rfl
    rw [coeff_add, show d + (n - 1) = n + (d - 1) by omega, h1, show n + (d - 1) = (n - 1) + d by
      omega, h2, hdp, hdE]
    have h2p : (2 * p).coeff n = 2 * p.leadingCoeff := by
      rw [show (2 : F[X]) = C 2 by rw [map_ofNat C 2], coeff_C_mul]; rfl
    rw [h2p, show E.coeff d = E.leadingCoeff from rfl]
    ring

/-- **The remaining equation `2B₀ = 2pe′ + p′e` forces `B₀ = 0`** in the degree range. -/
lemma e_eq_zero (p : F[X]) (hp : Squarefree p) (hodd : Odd p.natDegree) (B0 : F[X])
    (hB : B0 = 0 ∨ B0.natDegree + 2 ≤ p.natDegree) (e : K)
    (hid : φ (2 * B0) = φ (2 * p) * e′ + φ (derivative p) * e) : B0 = 0 := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hp0 : p ≠ 0 := hp.ne_zero
  have hn1 : 1 ≤ p.natDegree := by obtain ⟨k, hk⟩ := hodd; omega
  -- `e` is a polynomial
  have hreg : ∀ (q : F[X]) (_ : q.Monic) (hq : Irreducible q), e ∈ regularAt K q hq.prime := by
    intro q _ hq
    have hnorm := not_dvd_derivative_self hq
    by_contra he
    by_cases hqp : q ∣ p
    · obtain ⟨p1, rfl⟩ := hqp
      have hqp1 : ¬q ∣ p1 := fun h ↦ hq.not_isUnit (hp q (mul_dvd_mul_left q h))
      exact not_mem_eterm_of_pole_ram hder hq.prime hnorm p1 hqp1 he
        (hid ▸ algebraMap_mem_regularAt _ _)
    · exact not_mem_eterm_of_pole hder hq.prime hnorm p hqp he
        (hid ▸ mul_mem (algebraMap_mem_regularAt _ _) (algebraMap_mem_regularAt _ _))
  obtain ⟨E, rfl⟩ := exists_polynomial_of_regularAt e hreg
  rw [deriv_algebraMap, hder, ← map_mul, ← map_mul, ← map_add] at hid
  have hE := hinj hid
  by_contra hB0
  by_cases hE0 : E = 0
  · rw [hE0] at hE; simp at hE; exact hB0 hE
  have htop := coeff_top_eterm p E hn1 hE0
  rw [← hE] at htop
  have hlt : B0.natDegree < E.natDegree + (p.natDegree - 1) := by
    rcases hB with h | h
    · exact absurd h hB0
    · omega
  rw [show (2 : F[X]) * B0 = C 2 * B0 by rw [map_ofNat C 2], coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt hlt, mul_zero] at htop
  have hc : (2 * E.natDegree + p.natDegree : F) ≠ 0 := by
    have : ((2 * E.natDegree + p.natDegree : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact_mod_cast this
  exact mul_ne_zero (mul_ne_zero hc (leadingCoeff_ne_zero.mpr hp0))
    (leadingCoeff_ne_zero.mpr hE0) htop.symm

/-- **The core theorem**: a `y`-component identity `2B₀ = 2pe′ + p′e + ∑ cᵢ Mᵢ/Nᵢ` with
`ℚ`-independent constants and `deg B₀ ≤ deg p - 2` forces `B₀ = 0`. -/
theorem hyp_core (p : F[X]) (hp : Squarefree p) (hodd : Odd p.natDegree) (B0 : F[X])
    (hB : B0 = 0 ∨ B0.natDegree + 2 ≤ p.natDegree) (e : K) {ι : Type*} (s : Finset ι)
    (c : ι → F) (hc : ∀ g : ι → ℚ, ∑ i ∈ s, (g i : F) * c i = 0 → ∀ i ∈ s, g i = 0)
    (a b : ι → F[X]) (hab : ∀ i ∈ s, IsCoprime (a i) (b i))
    (hN0 : ∀ i ∈ s, hN p (a i) (b i) ≠ 0)
    (hid : φ (2 * B0) = φ (2 * p) * e′ + φ (derivative p) * e +
      ∑ i ∈ s, φ (C (c i)) * (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i)))) : B0 = 0 := by
  classical
  set L := ∑ i ∈ s, φ (C (c i)) * (φ (hM p (a i) (b i)) / φ (hN p (a i) (b i))) with hL
  -- at every irreducible `q ∤ p`: `e` regular, then the residues vanish
  have hqall : ∀ q : F[X], Irreducible q → ¬q ∣ p → ∀ i ∈ s, ¬q ∣ hN p (a i) (b i) := by
    intro q hq hqp
    have hnorm := not_dvd_derivative_self hq
    have hLq : φ q * L ∈ regularAt K q hq.prime := by
      rw [hL, Finset.mul_sum]
      refine Subring.sum_mem _ fun i hi ↦ ?_
      rw [mul_left_comm]
      exact mul_mem (algebraMap_mem_regularAt _ _)
        (q_mul_MN_mem hder hq.prime p _ _ (hab i hi) (hN0 i hi))
    have he : e ∈ regularAt K q hq.prime := by
      by_contra he
      refine not_mem_eterm_of_pole hder hq.prime hnorm p hqp he ?_
      have : φ q * (φ (2 * p) * e′ + φ (derivative p) * e) = φ q * φ (2 * B0) - φ q * L := by
        rw [hid]; ring
      rw [this]
      exact sub_mem (mul_mem (algebraMap_mem_regularAt _ _) (algebraMap_mem_regularAt _ _)) hLq
    have hLreg : L ∈ regularAt K q hq.prime := by
      have : L = φ (2 * B0) - (φ (2 * p) * e′ + φ (derivative p) * e) := by rw [hid]; ring
      rw [this]
      exact sub_mem (algebraMap_mem_regularAt _ _) (add_mem (mul_mem
        (algebraMap_mem_regularAt _ _) (deriv_mem_regularAt _ he))
        (mul_mem (algebraMap_mem_regularAt _ _) he))
    exact not_dvd_N_of_regular hder hq hnorm p hqp s c hc a b hab hN0 hLreg
  -- all logarithmic terms vanish
  have hM0 : ∀ i ∈ s, hM p (a i) (b i) = 0 := fun i hi ↦
    M_eq_zero p hp hodd (a i) (b i) (hab i hi) (hN0 i hi) fun q hq hqp ↦ hqall q hq hqp i hi
  have hL0 : L = 0 := Finset.sum_eq_zero fun i hi ↦ by rw [hM0 i hi]; simp
  rw [hL0, add_zero] at hid
  exact e_eq_zero hder p hp hodd B0 hB e hid

end Core

end Differential
