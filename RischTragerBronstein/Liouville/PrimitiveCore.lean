import RischTragerBronstein.Liouville.Reduce
import RischTragerBronstein.Liouville.MonicPrimes
import RischTragerBronstein.Liouville.PrimitivePoly

/-!
# Liouville's theorem for a primitive monomial: the core

Let `t` be a primitive monomial over `F` (`t′ = η ∈ F`) introducing no new constants, and let
`K = F(t)`. If `α ∈ F` satisfies

  `α = ∑ cᵢ uᵢ′ / uᵢ + v′`   with `cᵢ ∈ F`, `uᵢ ∈ K ∖ {0}`, `v ∈ K`,

then already

  `α = ∑ cᵢ eᵢ′ / eᵢ + c₀ η + d′`   with `eᵢ ∈ F ∖ {0}`, `c₀, d ∈ F`, `c₀′ = 0`.

In the logarithmic case `η = a′ / a`, the term `c₀ η` is one more logarithmic derivative with
constant coefficient, and this is Liouville's theorem for `F(log a) / F`.

Proof (Rosenlicht). Every monic irreducible `p ∈ F[t]` is normal. Hence `v` has no pole at any `p`
(`mem_regularAt_of_liouville_eq`), so `v ∈ F[t]`; the residues of the logarithmic derivatives
cancel, so the `uᵢ` may be replaced by elements of `F` (`exists_reduced_logs`); then `v′ ∈ F`,
which forces `v = c₀ t + d` with `c₀` constant (`eq_linear_of_deriv_eq_C`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- **Structure of a Liouville identity in a primitive extension.** If `A ∈ F[t]` satisfies
`A = ∑ cᵢ uᵢ′ / uᵢ + v′` in `K = F(t)`, then `v = P` is a polynomial and the logarithmic derivatives
sum to an element `β₀ = ∑ cᵢ eᵢ′ / eᵢ` of `F`: `P′ = A - β₀`. -/
theorem liouville_primitive_structure (η : F) (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hconst : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (A : F[X])
    (h : φ A = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (P : F[X]), (∀ i ∈ s, e i ≠ 0) ∧ v = φ P ∧
      implicitDeriv (C η) P = A - C (∑ i ∈ s, c i * logDeriv (e i)) := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hconst' : ∀ P : F[X], implicitDeriv (C η) P = 0 → ∃ e : F, P = C e :=
    fun P hP ↦ hconst P (by rw [hD, hP])
  -- `ψ : F → K` commutes with the derivations
  have hψ : ∀ x : F, (φ (C x))′ = φ (C x′) := fun x ↦ by
    rw [deriv_algebraMap, hD, implicitDeriv_C]
  let ψ : F →+* K := (algebraMap F[X] K).comp C
  have hψlog : ∀ x : F, logDeriv (φ (C x)) = φ (C (logDeriv x)) := fun x ↦ by
    unfold logDeriv
    rw [hψ]
    exact (map_div₀ ψ _ _).symm
  -- the places: monic irreducible polynomials, all normal
  let S : Set F[X] := {p | p.Monic ∧ Irreducible p}
  have hS : ∀ p ∈ S, Prime p ∧ ¬p ∣ p′ := fun p hp ↦
    ⟨hp.2.prime, by rw [hD]; exact not_dvd_deriv_of_monic η hconst' hp.1 hp.2.natDegree_pos⟩
  have hreg : ∀ p (hp : p ∈ S), φ A ∈ regularAt K p (hS p hp).1 :=
    fun p hp ↦ algebraMap_mem_regularAt _ _
  -- `v` is a polynomial
  obtain ⟨P, rfl⟩ : ∃ P : F[X], v = φ P := by
    refine exists_polynomial_of_regularAt v fun p hm hp ↦ ?_
    exact mem_regularAt_of_liouville_eq hp.prime (hS p ⟨hm, hp⟩).2
      (not_dvd_natCast_polynomial hp.prime) s (fun i ↦ φ (C (c i))) u v (φ A)
      (fun i _ ↦ algebraMap_mem_regularAt _ _) hu (algebraMap_mem_regularAt _ _) h
  -- write the `u i` as fractions and strip all monic irreducible factors
  have hfrac : ∀ i, ∃ a b : F[X], (u i ≠ 0 → a ≠ 0 ∧ b ≠ 0) ∧ u i = φ a / φ b := fun i ↦ by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := F[X]) (u i)
    refine ⟨a, b, fun hne ↦ ⟨?_, nonZeroDivisors.ne_zero hb⟩, hab.symm⟩
    rintro rfl
    exact hne (by rw [← hab]; simp)
  choose a b hab using hfrac
  have hsum : ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) =
      ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a i) / φ (b i)) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [← (hab i).2]
  rw [hsum] at h
  obtain ⟨a', b', hne', hred, hsum'⟩ := exists_reduced_logs S hS s c (φ P) (φ A) hreg _ a b
    (fun i hi ↦ (hab i).1 (hu i hi)) le_rfl h
  have hC : ∀ i, ∃ ea eb : F, i ∈ s → ea ≠ 0 ∧ eb ≠ 0 ∧ a' i = C ea ∧ b' i = C eb := fun i ↦ by
    by_cases hi : i ∈ s
    · obtain ⟨ea, hea, h1⟩ := eq_C_of_forall_monic_irreducible_not_dvd (hne' i hi).1
        fun p hm hp ↦ (hred i hi p ⟨hm, hp⟩).1
      obtain ⟨eb, heb, h2⟩ := eq_C_of_forall_monic_irreducible_not_dvd (hne' i hi).2
        fun p hm hp ↦ (hred i hi p ⟨hm, hp⟩).2
      exact ⟨ea, eb, fun _ ↦ ⟨hea, heb, h1, h2⟩⟩
    · exact ⟨0, 0, fun h' ↦ absurd h' hi⟩
  choose ea eb hC using hC
  have hsum'' : ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a' i) / φ (b' i)) =
      φ (C (∑ i ∈ s, c i * logDeriv (ea i / eb i))) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨_, _, h1, h2⟩ := hC i hi
    have hdiv : φ (C (ea i)) / φ (C (eb i)) = φ (C (ea i / eb i)) := (map_div₀ ψ _ _).symm
    rw [h1, h2, hdiv, hψlog, map_mul, map_mul]
  refine ⟨fun i ↦ ea i / eb i, P, fun i hi ↦ div_ne_zero (hC i hi).1 (hC i hi).2.1, rfl, ?_⟩
  apply hinj
  rw [← hD, ← deriv_algebraMap, map_sub, h, hsum', hsum'']
  ring

theorem liouville_primitive_core (η : F) (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hconst : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (α : F)
    (h : φ (C α) = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (c₀ d : F), (∀ i ∈ s, e i ≠ 0) ∧ c₀′ = 0 ∧
      α = ∑ i ∈ s, c i * logDeriv (e i) + c₀ * η + d′ := by
  have hconst' : ∀ P : F[X], implicitDeriv (C η) P = 0 → ∃ e : F, P = C e :=
    fun P hP ↦ hconst P (by rw [hD, hP])
  obtain ⟨e, P, he, -, hP⟩ := liouville_primitive_structure η hD hconst s c u hu v (C α) h
  rw [← C_sub] at hP
  obtain ⟨c₀, d, hc₀, hPd⟩ := eq_linear_of_deriv_eq_C η hconst' hP
  refine ⟨e, c₀, d, he, hc₀, ?_⟩
  have h3 : implicitDeriv (C η) P = C (c₀ * η + d′) := by
    rw [hPd]
    simp only [map_add, Derivation.leibniz, implicitDeriv_C, implicitDeriv_X, hc₀, smul_eq_mul,
      map_zero, mul_zero, add_zero]
    rw [← C_mul, ← C_add]
  have h4 := C_injective (hP.symm.trans h3)
  linear_combination h4

/-- **Integrability criterion for `f t + f₀`, `t` primitive** (`t′ = η`). If `f t + f₀` has an
integral of Liouville form in `F(t)`, there are a constant `c ∈ F` and `p₁ ∈ F` with
`p₁′ + 2 c η = f`: the antiderivative is `c t² + p₁ t + …`. For `t = log b` this is the
limited-integration condition "`f - 2 c b′ / b` has an integral in `F`". -/
theorem exists_limited_integral_of_liouville (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hconst : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (f f₀ : F)
    (h : φ (C f * X + C f₀) = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ c₂ p₁ : F, c₂′ = 0 ∧ p₁′ + 2 * c₂ * η = f := by
  have hconst' : ∀ P : F[X], implicitDeriv (C η) P = 0 → ∃ e : F, P = C e :=
    fun P hP ↦ hconst P (by rw [hD, hP])
  obtain ⟨e, P, -, -, hP⟩ :=
    liouville_primitive_structure η hD hconst s c u hu v (C f * X + C f₀) h
  have hdegA : (implicitDeriv (C η) P).natDegree ≤ 1 := by
    rw [hP, add_sub_assoc, ← C_sub]
    exact natDegree_linear_le
  have hdegP := natDegree_le_succ_of_natDegree_deriv_le η hconst' hdegA
  refine ⟨P.coeff 2, P.coeff 1, ?_, ?_⟩
  · have h2 := congrArg (fun Q : F[X] ↦ Q.coeff 2) hP
    simp only [coeff_implicitDeriv_C, coeff_sub, coeff_add, coeff_C_mul, coeff_X, coeff_C] at h2
    rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 2 + 1)] at h2
    simpa using h2
  · have h1 := congrArg (fun Q : F[X] ↦ Q.coeff 1) hP
    simp only [coeff_implicitDeriv_C, coeff_sub, coeff_add, coeff_C_mul, coeff_X_one, coeff_C] at h1
    norm_num at h1
    linear_combination h1

/-- **Coefficient equations for a polynomial integrand in a primitive `t`** (`t′ = η`). If
`A ∈ F[t]` has an integral of Liouville form in `F(t)`, there are `pⱼ ∈ F` with
`pⱼ′ + (j + 1) η pⱼ₊₁ = Aⱼ` for all `j ≥ 1`, and `p_{d+1}` constant for `d ≥ deg A`: the
antiderivative is `∑ pⱼ t ^ j + …`. -/
theorem exists_coeffs_of_liouville_primitive (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hconst : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (A : F[X])
    (h : φ A = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ p : ℕ → F, (∀ j, 1 ≤ j → (p j)′ + ((j + 1 : ℕ) : F) * η * p (j + 1) = A.coeff j) ∧
      ∀ d, A.natDegree ≤ d → (p (d + 1))′ = 0 := by
  have hconst' : ∀ P : F[X], implicitDeriv (C η) P = 0 → ∃ e : F, P = C e :=
    fun P hP ↦ hconst P (by rw [hD, hP])
  obtain ⟨e, P, -, -, hP⟩ := liouville_primitive_structure η hD hconst s c u hu v A h
  have hcoeff : ∀ j, 1 ≤ j → (P.coeff j)′ + ((j + 1 : ℕ) : F) * η * P.coeff (j + 1) =
      A.coeff j := fun j hj ↦ by
    have hj' := congrArg (fun Q : F[X] ↦ Q.coeff j) hP
    simp only [coeff_implicitDeriv_C, coeff_sub, coeff_C, if_neg (by omega : ¬j = 0),
      sub_zero] at hj'
    rw [← hj']
    push_cast
    ring
  refine ⟨P.coeff, hcoeff, fun d hd ↦ ?_⟩
  have hdegA : (implicitDeriv (C η) P).natDegree ≤ A.natDegree := by
    rw [hP]
    exact (natDegree_sub_le _ _).trans (max_le le_rfl (by rw [natDegree_C]; exact Nat.zero_le _))
  have hdegP := natDegree_le_succ_of_natDegree_deriv_le η hconst' hdegA
  have h1 := hcoeff (d + 1) (by omega)
  rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < d + 1 + 1),
    coeff_eq_zero_of_natDegree_lt (by omega : A.natDegree < d + 1), mul_zero,
    add_zero] at h1
  exact h1

end Differential
