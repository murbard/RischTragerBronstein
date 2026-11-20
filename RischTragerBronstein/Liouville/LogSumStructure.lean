import RischTragerBronstein.Liouville.PrimitivePolyPart
import RischTragerBronstein.Liouville.ExpProperSum
import RischTragerBronstein.Liouville.PoleOrder
import RischTragerBronstein.Liouville.MonicPrimes
import RischTragerBronstein.Liouville.PrimitivePoly

/-!
# Elements whose derivative is a combination of logarithmic derivatives

The one-level steps of the structure theorem for towers of logarithms and exponentials. Let
`Z′ = ∑ cᵢ uᵢ′ / uᵢ` in `K = F(t)` (`cᵢ ∈ F`).

* `prim_logsum_structure` (`t′ = η`, `η` not a derivative in `F`): `Z = d t + z₀` with `d′ = 0`
  and `z₀′ + d η = ∑ cᵢ eᵢ′ / eᵢ` for some `eᵢ ∈ F`.
* `exp_logsum_structure` (`t′ = b t`, no `e′ + j b e = 0`, `j ≠ 0`): `Z = z₀ ∈ F` and
  `z₀′ = ∑ cᵢ (eᵢ′ / eᵢ + nᵢ b)` for some `eᵢ ∈ F`, `nᵢ ∈ ℤ`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- If `Z′ = ∑ cᵢ uᵢ′ / uᵢ`, `Z` is regular at every normal prime. -/
lemma logsum_regular {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0)
    (Z : K) (h : Z′ = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i)) (p : F[X]) (hp : Irreducible p)
    (hnorm : ¬p ∣ p′) : Z ∈ regularAt K p hp.prime := by
  have := mem_regularAt_of_liouville_eq hp.prime hnorm (not_dvd_natCast_polynomial hp.prime) s
    (fun i ↦ φ (C (c i))) u (-Z) 0 (fun i _ ↦ algebraMap_mem_regularAt _ _) hu (zero_mem _)
    (by rw [map_neg, h]; ring)
  simpa using neg_mem this

section Prim

variable {η : F} (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
include hD

/-- **The primitive step.** -/
theorem prim_logsum_structure (hnorm : ∀ p : F[X], Irreducible p → ¬p ∣ p′)
    (hη : ∀ y : F, y′ ≠ η) {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K)
    (hu : ∀ i ∈ s, u i ≠ 0) (Z : K) (h : Z′ = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i)) :
    ∃ (d z0 : F) (e : ι → F), d′ = 0 ∧ (∀ i ∈ s, e i ≠ 0) ∧ Z = φ (C d * X + C z0) ∧
      z0′ + d * η = ∑ i ∈ s, c i * logDeriv (e i) := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  -- `Z` is a polynomial
  obtain ⟨P, rfl⟩ : ∃ P : F[X], Z = φ P := exists_polynomial_of_regularAt Z fun p _ hp ↦
    logsum_regular s c u hu Z h p hp (hnorm p hp)
  -- `P′` is the constant `∑ cᵢ eᵢ′ / eᵢ`
  have he : ∀ i, ∃ e : F, (u i ≠ 0 → e ≠ 0 ∧ IsProperFrac F (logDeriv (u i) - φ (C (logDeriv e)))) :=
    fun i ↦ by
      by_cases hi : u i = 0
      · exact ⟨1, fun h ↦ absurd hi h⟩
      · obtain ⟨e, he0, hp⟩ := logDeriv_sub_isProperFrac hD (u i) hi
        exact ⟨e, fun _ ↦ ⟨he0, hp⟩⟩
  choose e he using he
  set σ := ∑ i ∈ s, c i * logDeriv (e i) with hσ
  have hsum := isProperFrac_sum s
    (fun i ↦ φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i)))))
    (fun i hi ↦ isProperFrac_C_mul (c i) (he i (hu i hi)).2)
  have hDP : implicitDeriv (C η) P = C σ := by
    have key : φ (implicitDeriv (C η) P - C σ) =
        ∑ i ∈ s, φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i)))) := by
      rw [map_sub, ← deriv_phi hD, h, hσ]
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib]
    have h0 := eq_zero_of_isProperFrac_poly (key ▸ hsum) hinj
    exact sub_eq_zero.mp h0
  have hc : ∀ n : ℕ, (P.coeff n)′ + η * (P.coeff (n + 1) * (n + 1)) = if n = 0 then σ else 0 :=
    fun n ↦ by rw [← coeff_implicitDeriv_C, hDP, coeff_C]
  -- `deg P ≤ 1`
  have hdeg : P.natDegree ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    set n := P.natDegree with hn
    have h1 := hc n
    rw [if_neg (by omega), coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 1),
      zero_mul, mul_zero, add_zero] at h1
    have h2 := hc (n - 1)
    rw [if_neg (by omega), show n - 1 + 1 = n by omega] at h2
    have hnF : (n : F) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hcast : ((n - 1 : ℕ) : F) + 1 = n := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at h2
    have hd : ((n : F) * P.coeff n)′ = 0 := by
      rw [Derivation.leibniz, h1, Derivation.map_natCast]; simp
    have hPn : P.coeff n ≠ 0 := leadingCoeff_ne_zero.mpr fun h0 ↦ by
      have : P.natDegree = 0 := by rw [h0, natDegree_zero]
      omega
    refine hη (-(P.coeff (n - 1)) / ((n : F) * P.coeff n)) ?_
    rw [Derivation.leibniz_div, hd, smul_zero, sub_zero, smul_eq_mul, Derivation.map_neg]
    field_simp
    linear_combination (-(n : F) * P.coeff n) * h2
  refine ⟨P.coeff 1, P.coeff 0, e, ?_, fun i hi ↦ (he i (hu i hi)).1, ?_, ?_⟩
  · have := hc 1
    rw [if_neg one_ne_zero, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 1 + 1),
      zero_mul, mul_zero, add_zero] at this
    exact this
  · congr 1
    exact (eq_X_add_C_of_natDegree_le_one hdeg).trans (by ring)
  · have := hc 0
    rw [if_pos rfl] at this
    push_cast at this
    linear_combination this

end Prim

section Exp

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
include hDe

/-- **The exponential step.** -/
theorem exp_logsum_structure (hnorm : ∀ p : F[X], Irreducible p → ¬X ∣ p → ¬p ∣ p′)
    (hhom : ∀ j : ℤ, j ≠ 0 → ∀ e : F, e ≠ 0 → e′ + (j : F) * b * e ≠ 0)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K)
    (hu : ∀ i ∈ s, u i ≠ 0) (Z : K) (h : Z′ = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i)) :
    ∃ (z0 : F) (e : ι → F) (n : ι → ℤ), (∀ i ∈ s, e i ≠ 0) ∧ Z = φ (C z0) ∧
      z0′ = ∑ i ∈ s, c i * (logDeriv (e i) + (n i : F) * b) := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hXp : ∀ k : ℕ, φ (X ^ k : F[X]) ≠ 0 := fun k ↦
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  -- `Z` is a Laurent polynomial
  obtain ⟨V, kv, hz1⟩ := exists_laurent_add_nproper (F := F) Z
  obtain ⟨z1, hz1d⟩ : ∃ z1, z1 = Z - φ V / φ (X ^ kv) := ⟨_, rfl⟩
  rw [← hz1d] at hz1
  have hreg : ∀ (p : F[X]) (_ : p.Monic) (hp : Irreducible p), z1 ∈ regularAt K p hp.prime := by
    intro p _ hp
    by_cases hXp' : X ∣ p
    · obtain ⟨a, s', hs, hsX, -, hz⟩ := hz1
      refine ⟨a, s', fun hps ↦ hsX (hXp'.trans hps), ?_⟩
      rw [hz]; exact div_mul_cancel₀ _ ((map_ne_zero_iff _ hinj).mpr hs)
    · rw [hz1d]
      refine sub_mem (logsum_regular s c u hu Z h p hp (hnorm p hp hXp')) ⟨V, X ^ kv, ?_, ?_⟩
      · exact fun hd ↦ hXp' (hp.dvd_symm irreducible_X (hp.prime.dvd_of_dvd_pow hd))
      · exact div_mul_cancel₀ _ (hXp kv)
  obtain ⟨P, hP⟩ := exists_polynomial_of_regularAt z1 hreg
  have hP0 : P = 0 := eq_zero_of_isNProperFrac_laurent (N := 0) (K := K)
    (by rw [pow_zero, map_one, div_one, ← hP]; exact hz1)
  have hZ : Z = φ V / φ (X ^ kv) := by
    have : z1 = 0 := by rw [hP, hP0, map_zero]
    rw [hz1d, sub_eq_zero] at this
    exact this
  -- the logarithmic derivatives
  have he : ∀ i, ∃ e : F, ∃ n : ℤ, (u i ≠ 0 → e ≠ 0 ∧
      IsNProperFrac F (logDeriv (u i) - φ (C (logDeriv e + (n : F) * b)))) := fun i ↦ by
    by_cases hi : u i = 0
    · exact ⟨1, 0, fun h ↦ absurd hi h⟩
    · obtain ⟨e, he0, n, hp⟩ := logDeriv_sub_isNProperFrac hDe (u i) hi
      exact ⟨e, n, fun _ ↦ ⟨he0, hp⟩⟩
  choose e n he using he
  set σ := ∑ i ∈ s, c i * (logDeriv (e i) + (n i : F) * b) with hσ
  have hsum := isNProperFrac_sum s
    (fun i ↦ φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i) + (n i : F) * b))))
    (fun i hi ↦ isNProperFrac_C_mul (c i) (he i (hu i hi)).2)
  have hQ : implicitDeriv (C b * X) V - C ((kv : F) * b) * V - C σ * X ^ kv = 0 := by
    refine eq_zero_of_isNProperFrac_laurent (N := kv) (K := K) ?_
    have key : φ (implicitDeriv (C b * X) V - C ((kv : F) * b) * V - C σ * X ^ kv) / φ (X ^ kv) =
        ∑ i ∈ s, φ (C (c i)) * (logDeriv (u i) - φ (C (logDeriv (e i) + (n i : F) * b))) := by
      have h1 : Z′ = φ (implicitDeriv (C b * X) V - C ((kv : F) * b) * V) / φ (X ^ kv) := by
        rw [hZ, deriv_laurent hDe V kv]
      have h2 : φ (implicitDeriv (C b * X) V - C ((kv : F) * b) * V - C σ * X ^ kv) / φ (X ^ kv) =
          Z′ - φ (C σ) := by
        rw [h1, map_sub φ, sub_div, show φ (C σ * X ^ kv) / φ (X ^ kv) = φ (C σ) by
          rw [map_mul, mul_div_assoc, div_self (hXp kv), mul_one]]
      rw [h2, h, hσ]
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib]
    rw [key]
    exact hsum
  have hcoef : ∀ d, (V.coeff d)′ + ((d : F) - kv) * b * V.coeff d = if d = kv then σ else 0 := by
    intro d
    have := congrArg (fun Q : F[X] ↦ Q.coeff d) hQ
    simp only [coeff_sub, coeff_C_mul, coeff_implicitDeriv_C_mul_X, coeff_X_pow,
      coeff_zero] at this
    split_ifs at this ⊢ with hd
    · linear_combination this
    · linear_combination this
  have hV : V = C (V.coeff kv) * X ^ kv := by
    ext d
    rw [coeff_C_mul_X_pow]
    split_ifs with hd
    · rw [hd]
    · by_contra hVd
      have := hcoef d
      rw [if_neg hd] at this
      refine hhom ((d : ℤ) - kv) (by omega) (V.coeff d) hVd ?_
      push_cast
      linear_combination this
  refine ⟨V.coeff kv, e, n, fun i hi ↦ (he i (hu i hi)).1, ?_, ?_⟩
  · rw [hZ]
    conv_lhs => rw [hV]
    rw [map_mul, mul_div_assoc, div_self (hXp kv), mul_one]
  · have := hcoef kv
    rw [if_pos rfl, sub_self, zero_mul, zero_mul, add_zero] at this
    exact this

end Exp

end Differential
