import RischTragerBronstein.Liouville.Reduce
import RischTragerBronstein.Liouville.MonicPrimes
import RischTragerBronstein.Liouville.ExponentialPoly

/-!
# Liouville's theorem for an exponential monomial: the core

Let `t` be an exponential monomial over `F` (`t′ = η t`, `η ∈ F`) introducing no new constants, and
`K = F(t)`. If `α ∈ F` satisfies `α = ∑ cᵢ uᵢ′ / uᵢ + v′` with `cᵢ ∈ F`, `uᵢ ∈ K ∖ {0}`, `v ∈ K`,
then

  `α = ∑ cᵢ eᵢ′ / eᵢ + (∑ cᵢ mᵢ) η + d′`   with `eᵢ ∈ F ∖ {0}`, `mᵢ ∈ ℤ`, `d ∈ F`.

When `η = a′` and the `cᵢ` are constants, `(∑ cᵢ mᵢ) η = ((∑ cᵢ mᵢ) a)′` and this is Liouville's
theorem for `F(exp a) / F`.

The only special prime is `t`. Away from it the argument is that of the primitive case: `v` has
poles only at `t`, so `v = P / t ^ k`, and the `uᵢ` reduce to monomials `eᵢ t ^ mᵢ`. Finally
`v′ ∈ F` forces `v ∈ F` (`eq_monomial_of_deriv`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Differential

variable {F K : Type*} [Field F] [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]

local notation "φ" => algebraMap F[X] K

/-- A nonzero polynomial whose only monic irreducible factor is `t` is a monomial. -/
lemma eq_C_mul_X_pow_of_forall_not_dvd {a : F[X]} (ha0 : a ≠ 0)
    (h : ∀ p : F[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ a) :
    ∃ (e : F) (k : ℕ), e ≠ 0 ∧ a = C e * X ^ k := by
  obtain ⟨k, a₁, ha₁, rfl⟩ := exists_pow_mul_not_dvd (prime_X (R := F)) ha0
  have ha₁0 : a₁ ≠ 0 := right_ne_zero_of_mul ha0
  obtain ⟨e, he, rfl⟩ := eq_C_of_forall_monic_irreducible_not_dvd ha₁0 fun p hm hp hpa ↦ by
    by_cases hpX : p = X
    · exact ha₁ (hpX ▸ hpa)
    · exact h p hm hp hpX (Dvd.dvd.mul_left hpa _)
  exact ⟨e, k, he, mul_comm _ _⟩

/-- An element of `F(t)` with poles only at `t` is a Laurent polynomial. -/
theorem exists_laurent_of_regularAt (v : K)
    (hv : ∀ (p : F[X]) (_ : p.Monic) (hp : Irreducible p), p ≠ X → v ∈ regularAt K p hp.prime) :
    ∃ (P : F[X]) (k : ℕ), v = φ P / φ X ^ k := by
  obtain ⟨a, ⟨b, hb⟩, hrel, rfl⟩ := IsFractionRing.exists_reduced_fraction (A := F[X]) v
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hφb : φ b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr hb0
  rw [IsFractionRing.mk'_eq_div] at hv ⊢
  obtain ⟨e, k, he, rfl⟩ := eq_C_mul_X_pow_of_forall_not_dvd hb0 fun p hm hp hpX hpb ↦ by
    obtain ⟨c, d, hd, hcd⟩ := hv p hm hp hpX
    have : φ (a * d) = φ (c * b) := by
      rw [map_mul, map_mul, ← hcd]
      simp only
      field_simp
    have h2 := IsFractionRing.injective F[X] K this
    have hpa : p ∣ a := (hp.prime.dvd_or_dvd (h2 ▸ Dvd.dvd.mul_left hpb c)).resolve_right hd
    exact hp.not_isUnit (hrel hpa hpb)
  refine ⟨a * C e⁻¹, k, ?_⟩
  have hφe : φ (C e) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr (C_ne_zero.mpr he)
  have hφX : φ X ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr X_ne_zero
  have hinv : φ (C e⁻¹) = (φ (C e))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← C_mul, inv_mul_cancel₀ he, C_1, map_one])
  rw [map_mul, map_mul, map_pow, hinv]
  field_simp

variable [CharZero F] [Differential F] [Differential F[X]] [Differential K]
variable [DifferentialAlgebra F[X] K]

/-- **Structure of a Liouville identity in an exponential extension, general form.** If `α ∈ K`
is regular away from `t` and `α = ∑ cᵢ uᵢ′ / uᵢ + v′` in `K = F(t)`, then `v = P / t ^ k` is a
Laurent polynomial and the logarithmic derivatives sum to an element
`β₀ = ∑ cᵢ eᵢ′ / eᵢ + (∑ cᵢ mᵢ) η` of `F`: `v′ = α - β₀`. -/
theorem liouville_exponential_structure_gen (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (α : K)
    (hα : ∀ (p : F[X]) (_ : p.Monic) (hp : Irreducible p), p ≠ X → α ∈ regularAt K p hp.prime)
    (h : α = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (m : ι → ℤ) (P : F[X]) (k : ℕ), (∀ i ∈ s, e i ≠ 0) ∧ v = φ P / φ X ^ k ∧
      v′ = α - φ (C (∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η)) := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hconst' : ∀ (P : F[X]) (n : ℕ), implicitDeriv (C η * X) P * X ^ n =
      P * implicitDeriv (C η * X) (X ^ n) → ∃ e : F, P = C e * X ^ n :=
    fun P n hP ↦ hconst P n (by rw [hD, hD, hP])
  let ψ : F →+* K := (algebraMap F[X] K).comp C
  have hψ : ∀ x : F, (φ (C x))′ = φ (C x′) := fun x ↦ by
    rw [deriv_algebraMap, hD, implicitDeriv_C]
  have hψlog : ∀ x : F, logDeriv (φ (C x)) = φ (C (logDeriv x)) := fun x ↦ by
    unfold logDeriv
    rw [hψ]
    exact (map_div₀ ψ _ _).symm
  have hφX : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hXlog : logDeriv (φ X) = φ (C η) := by
    unfold logDeriv
    rw [deriv_algebraMap, hD, implicitDeriv_X, map_mul]
    field_simp
  -- the places: monic irreducibles other than `t`, all normal
  let S : Set F[X] := {p | p.Monic ∧ Irreducible p ∧ p ≠ X}
  have hS : ∀ p ∈ S, Prime p ∧ ¬p ∣ p′ := fun p hp ↦
    ⟨hp.2.1.prime, by rw [hD]; exact not_dvd_deriv_of_monic_ne_X η hconst' hp.1 hp.2.1 hp.2.2⟩
  have hreg : ∀ p (hp : p ∈ S), α ∈ regularAt K p (hS p hp).1 :=
    fun p hp ↦ hα p hp.1 hp.2.1 hp.2.2
  -- `v` is a Laurent polynomial
  obtain ⟨P, k, rfl⟩ : ∃ (P : F[X]) (k : ℕ), v = φ P / φ X ^ k := by
    refine exists_laurent_of_regularAt v fun p hm hp hpX ↦ ?_
    exact mem_regularAt_of_liouville_eq hp.prime (hS p ⟨hm, hp, hpX⟩).2
      (not_dvd_natCast_polynomial hp.prime) s (fun i ↦ φ (C (c i))) u v α
      (fun i _ ↦ algebraMap_mem_regularAt _ _) hu (hα p hm hp hpX) h
  -- strip the normal primes from the `u i`
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
  obtain ⟨a', b', hne', hred, hsum'⟩ := exists_reduced_logs S hS s c (φ P / φ X ^ k) α
    hreg _ a b (fun i hi ↦ (hab i).1 (hu i hi)) le_rfl h
  have hC : ∀ i, ∃ (ea eb : F) (ka kb : ℕ), i ∈ s →
      ea ≠ 0 ∧ eb ≠ 0 ∧ a' i = C ea * X ^ ka ∧ b' i = C eb * X ^ kb := fun i ↦ by
    by_cases hi : i ∈ s
    · obtain ⟨ea, ka, hea, h1⟩ := eq_C_mul_X_pow_of_forall_not_dvd (hne' i hi).1
        fun p hm hp hpX ↦ (hred i hi p ⟨hm, hp, hpX⟩).1
      obtain ⟨eb, kb, heb, h2⟩ := eq_C_mul_X_pow_of_forall_not_dvd (hne' i hi).2
        fun p hm hp hpX ↦ (hred i hi p ⟨hm, hp, hpX⟩).2
      exact ⟨ea, eb, ka, kb, fun _ ↦ ⟨hea, heb, h1, h2⟩⟩
    · exact ⟨0, 0, 0, 0, fun h' ↦ absurd h' hi⟩
  choose ea eb ka kb hC using hC
  let m : ι → ℤ := fun i ↦ (ka i : ℤ) - kb i
  have hsum'' : ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (a' i) / φ (b' i)) =
      φ (C (∑ i ∈ s, c i * logDeriv (ea i / eb i) + (∑ i ∈ s, c i * m i) * η)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨hea, heb, h1, h2⟩ := hC i hi
    have hφea : φ (C (ea i)) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (C_ne_zero.mpr hea)
    have hφeb : φ (C (eb i)) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (C_ne_zero.mpr heb)
    have hdiv : logDeriv (φ (C (ea i)) / φ (C (eb i))) = φ (C (logDeriv (ea i / eb i))) := by
      rw [show φ (C (ea i)) / φ (C (eb i)) = φ (C (ea i / eb i)) from (map_div₀ ψ _ _).symm, hψlog]
    rw [h1, h2, map_mul, map_mul, map_pow, map_pow,
      logDeriv_div _ _ (mul_ne_zero hφea (pow_ne_zero _ hφX))
        (mul_ne_zero hφeb (pow_ne_zero _ hφX)),
      logDeriv_mul _ _ hφea (pow_ne_zero _ hφX), logDeriv_mul _ _ hφeb (pow_ne_zero _ hφX),
      logDeriv_pow, logDeriv_pow, hXlog]
    have : logDeriv (φ (C (ea i))) - logDeriv (φ (C (eb i))) =
        φ (C (logDeriv (ea i / eb i))) := by
      rw [← hdiv, logDeriv_div _ _ hφea hφeb]
    have hR : φ (C (c i * logDeriv (ea i / eb i) + c i * (m i : F) * η)) =
        φ (C (c i)) * φ (C (logDeriv (ea i / eb i))) +
          φ (C (c i)) * ((ka i : K) - (kb i : K)) * φ (C η) := by
      simp only [m, Int.cast_sub, Int.cast_natCast, map_add, map_mul, map_sub, map_natCast]
    rw [hR, ← this]
    ring
  refine ⟨fun i ↦ ea i / eb i, m, P, k,
    fun i hi ↦ div_ne_zero (hC i hi).1 (hC i hi).2.1, rfl, ?_⟩
  rw [h, hsum', hsum'']
  ring

/-- **Structure of a Liouville identity in an exponential extension.** If `A ∈ F[t]` satisfies
`A = ∑ cᵢ uᵢ′ / uᵢ + v′` in `K = F(t)`, then `v = P / t ^ k` is a Laurent polynomial and the
logarithmic derivatives sum to an element `β₀ = ∑ cᵢ eᵢ′ / eᵢ + (∑ cᵢ mᵢ) η` of `F`:
`P′ - k η P = (A - β₀) t ^ k`. -/
theorem liouville_exponential_structure (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (A : F[X])
    (h : φ A = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (m : ι → ℤ) (P : F[X]) (k : ℕ), (∀ i ∈ s, e i ≠ 0) ∧ v = φ P / φ X ^ k ∧
      implicitDeriv (C η * X) P - C (k * η) * P =
        (A - C (∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η)) * X ^ k := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hφX : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  obtain ⟨e, m, P, k, he, rfl, hv⟩ := liouville_exponential_structure_gen η hD hconst s c u hu v
    (φ A) (fun p _ hp _ ↦ algebraMap_mem_regularAt _ _) h
  set β₀ : F := ∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η with hβ₀
  have hv' : (φ P / φ X ^ k)′ = φ (A - C β₀) := by rw [map_sub, hv]
  refine ⟨e, m, P, k, he, rfl, ?_⟩
  apply hinj
  have hXk : (φ X ^ k)′ = φ (C (k * η)) * φ X ^ k := by
    rw [← map_pow, deriv_algebraMap, hD, deriv_X_pow, map_mul, map_pow]
  rw [Derivation.leibniz_div, hXk, deriv_algebraMap, hD] at hv'
  simp only [smul_eq_mul] at hv'
  have hXk0 : φ X ^ k ≠ 0 := pow_ne_zero _ hφX
  have hk : φ (implicitDeriv (C η * X) P) - φ (C (k * η)) * φ P = φ (A - C β₀) * φ X ^ k := by
    rw [← hv']
    field_simp
  rw [map_sub, map_mul φ, map_mul φ, map_pow]
  exact hk

/-- **Laurent version of the structure theorem.** If `A / t ^ n` (`A ∈ F[t]`) satisfies
`A / t ^ n = ∑ cᵢ uᵢ′ / uᵢ + v′` in `K = F(t)`, then `v = P / t ^ (k + n)` and
`P′ - (k + n) η P = (A - β₀ t ^ n) t ^ k`. -/
theorem liouville_exponential_structure_laurent (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (A : F[X])
    (n : ℕ) (h : φ A / φ X ^ n = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (m : ι → ℤ) (P : F[X]) (k : ℕ), (∀ i ∈ s, e i ≠ 0) ∧
      v = φ P / φ X ^ (k + n) ∧
      implicitDeriv (C η * X) P - C ((k + n : ℕ) * η) * P =
        (A - C (∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η) * X ^ n) * X ^ k := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hφX : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hα : ∀ (p : F[X]) (_ : p.Monic) (hp : Irreducible p), p ≠ X →
      φ A / φ X ^ n ∈ regularAt K p hp.prime := fun p hm hp hpX ↦ by
    refine ⟨A, X ^ n, fun hdvd ↦ hpX ?_, by rw [map_pow]; field_simp⟩
    have hpX' : p ∣ X := hp.prime.dvd_of_dvd_pow hdvd
    exact eq_of_monic_of_associated hm monic_X
      (hp.associated_of_dvd irreducible_X hpX')
  obtain ⟨e, m, P₀, k, he, hv0, hv⟩ := liouville_exponential_structure_gen η hD hconst s c u hu v
    (φ A / φ X ^ n) hα h
  set β₀ : F := ∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η with hβ₀
  have hv1 : v = φ (P₀ * X ^ n) / φ X ^ (k + n) := by
    rw [hv0, map_mul, map_pow, pow_add]
    field_simp
  refine ⟨e, m, P₀ * X ^ n, k, he, hv1, ?_⟩
  apply hinj
  have hXk : (φ X ^ (k + n))′ = φ (C ((k + n : ℕ) * η)) * φ X ^ (k + n) := by
    rw [← map_pow, deriv_algebraMap, hD, deriv_X_pow, map_mul, map_pow]
  rw [hv1, Derivation.leibniz_div, hXk, deriv_algebraMap, hD] at hv
  simp only [smul_eq_mul] at hv
  have hk : φ (implicitDeriv (C η * X) (P₀ * X ^ n)) - φ (C ((k + n : ℕ) * η)) * φ (P₀ * X ^ n) =
      (φ A - φ (C β₀) * φ X ^ n) * φ X ^ k := by
    have hXn : φ X ^ n ≠ 0 := pow_ne_zero _ hφX
    have hXk0 : φ X ^ (k + n) ≠ 0 := pow_ne_zero _ hφX
    field_simp at hv
    rw [pow_add] at hv
    have hXk1 : φ X ^ k ≠ 0 := pow_ne_zero _ hφX
    field_simp at hv
    linear_combination hv
  simp only [map_sub, map_mul, map_pow] at hk ⊢
  exact hk

theorem liouville_exponential_core (η : F) (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (α : F)
    (h : φ (C α) = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (m : ι → ℤ) (d : F), (∀ i ∈ s, e i ≠ 0) ∧
      α = ∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η + d′ := by
  obtain ⟨e, m, P, k, he, -, hP⟩ := liouville_exponential_structure η hD hconst s c u hu v (C α) h
  refine ⟨e, m, P.coeff k, he, ?_⟩
  have hcoeff := congrArg (fun Q : F[X] ↦ Q.coeff k) hP
  simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, ← C_sub, coeff_X_pow, ite_true,
    mul_one] at hcoeff
  linear_combination -hcoeff

/-- **The Risch differential equation criterion.** If `f t` (`f ∈ F`, `t′ = η t`) has an integral
of Liouville form in `F(t)`, then `y′ + η y = f` has a solution `y ∈ F`. -/
theorem exists_rde_solution_of_liouville (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (f : F)
    (h : φ (C f * X) = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ y : F, y′ + η * y = f := by
  obtain ⟨e, m, P, k, -, -, hP⟩ :=
    liouville_exponential_structure η hD hconst s c u hu v (C f * X) h
  refine ⟨P.coeff (k + 1), ?_⟩
  have hcoeff := congrArg (fun Q : F[X] ↦ Q.coeff (k + 1)) hP
  simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, sub_mul, coeff_mul_X_pow',
    mul_assoc, coeff_C_mul, coeff_X_mul, coeff_X_pow] at hcoeff
  simp only [le_add_iff_nonneg_right, zero_le, ite_true, Nat.add_sub_cancel_left, coeff_X_one,
    coeff_C, mul_one] at hcoeff
  push_cast at hcoeff
  simp at hcoeff
  linear_combination hcoeff

/-- **The Risch differential equation criterion for polynomials in `t`.** If `A ∈ F[t]`
(`t′ = η t`) has an integral of Liouville form in `F(t)`, then for every `j ≥ 1` the equation
`y′ + j η y = A_j` has a solution `y ∈ F`: the antiderivative is `∑ yⱼ t ^ j + …`. -/
theorem exists_rde_solutions_of_liouville (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (A : F[X])
    (h : φ A = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) (j : ℕ) (hj : j ≠ 0) :
    ∃ y : F, y′ + (j : F) * η * y = A.coeff j := by
  obtain ⟨e, m, P, k, -, -, hP⟩ := liouville_exponential_structure η hD hconst s c u hu v A h
  refine ⟨P.coeff (k + j), ?_⟩
  have hcoeff := congrArg (fun Q : F[X] ↦ Q.coeff (k + j)) hP
  simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_mul_X_pow',
    le_add_iff_nonneg_right, zero_le, ite_true, Nat.add_sub_cancel_left, coeff_C,
    if_neg hj, sub_zero] at hcoeff
  push_cast at hcoeff
  linear_combination hcoeff

/-- **The Risch differential equation criterion for Laurent polynomials in `t`.** If `A / t ^ n`
(`t′ = η t`) has an integral of Liouville form in `F(t)`, then for every `j ≠ n` the equation
`y′ + (j - n) η y = A_j` has a solution `y ∈ F`. -/
theorem exists_rde_solutions_of_liouville_laurent (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (A : F[X])
    (n : ℕ) (h : φ A / φ X ^ n = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′)
    (j : ℕ) (hj : j ≠ n) :
    ∃ y : F, y′ + ((j : F) - n) * η * y = A.coeff j := by
  obtain ⟨e, m, P, k, -, -, hP⟩ :=
    liouville_exponential_structure_laurent η hD hconst s c u hu v A n h
  refine ⟨P.coeff (k + j), ?_⟩
  have hcoeff := congrArg (fun Q : F[X] ↦ Q.coeff (k + j)) hP
  simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_mul_X_pow',
    le_add_iff_nonneg_right, zero_le, ite_true, Nat.add_sub_cancel_left, coeff_X_pow,
    coeff_C] at hcoeff
  have hjn : j - n = 0 → ¬n ≤ j := fun h0 hle ↦ hj (by omega)
  have h0 : (if n ≤ j then (if j - n = 0 then
      (∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η) else 0) else 0) = 0 := by
    split_ifs with h1 h2
    · exact absurd h1 (hjn h2)
    · rfl
    · rfl
  rw [h0] at hcoeff
  push_cast at hcoeff
  linear_combination hcoeff

/-- The coefficient of `t ^ 0` in a Laurent integrand with an integral of Liouville form has a
limited integral over `F`. -/
theorem exists_limited_of_liouville_laurent (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → K) (hu : ∀ i ∈ s, u i ≠ 0) (v : K) (A : F[X])
    (n : ℕ) (h : φ A / φ X ^ n = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (m : ι → ℤ) (d : F), (∀ i ∈ s, e i ≠ 0) ∧
      A.coeff n = ∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η + d′ := by
  obtain ⟨e, m, P, k, he, -, hP⟩ :=
    liouville_exponential_structure_laurent η hD hconst s c u hu v A n h
  refine ⟨e, m, P.coeff (k + n), he, ?_⟩
  have hcoeff := congrArg (fun Q : F[X] ↦ Q.coeff (k + n)) hP
  simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_mul_X_pow',
    le_add_iff_nonneg_right, zero_le, ite_true, Nat.add_sub_cancel_left, coeff_X_pow,
    coeff_C, le_refl, Nat.sub_self] at hcoeff
  push_cast at hcoeff
  linear_combination -hcoeff

/-- **Constants of an exponential extension.** If no `P / t ^ n` is a new constant, then `F(t)` has
no new constants at all. -/
theorem constant_of_exponential (η : F) (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    (f : K) (hf : f′ = 0) : ∃ e : F, f = φ (C e) := by
  obtain ⟨_, _, P, k, -, hv, hP⟩ := liouville_exponential_structure (ι := Empty) η hD hconst ∅
    (fun _ ↦ 0) (fun _ ↦ 1) (by simp) f 0 (by simp [hf])
  simp only [Finset.sum_empty, zero_mul, add_zero, C_0, sub_zero] at hP
  have hP' : P′ * X ^ k = P * (X ^ k)′ := by
    rw [hD, hD, deriv_X_pow]
    linear_combination X ^ k * hP
  obtain ⟨e, he⟩ := hconst P k hP'
  refine ⟨e, ?_⟩
  have hφX : φ X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr X_ne_zero
  rw [hv, he, map_mul, map_pow]
  field_simp

end Differential
