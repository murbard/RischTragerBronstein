import RischTragerBronstein.Liouville.SimpleTranscendental
import RischTragerBronstein.Liouville.ExponentialCore

/-!
# One Liouville step inside an ambient field: exponential case

`liouville_step_exponential`: let `E / F` be differential fields, `t ∈ E` transcendental over `F`
with `t′ = η t`, `η ∈ F`, and suppose `F⟮t⟯` has no constants outside `F`. If `α ∈ F` satisfies
`α = ∑ cᵢ uᵢ′ / uᵢ + v′` with `uᵢ, v ∈ F⟮t⟯` and `cᵢ ∈ F`, then
`α = ∑ cᵢ eᵢ′ / eᵢ + (∑ cᵢ mᵢ) η + d′` with `eᵢ, d ∈ F`, `mᵢ ∈ ℤ`.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

theorem liouville_step_exponential (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η * t)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (v : E) (hv : v ∈ F⟮t⟯) (α : F)
    (h : algebraMap F E α = ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (m : ι → ℤ) (d : F), (∀ i ∈ s, e i ≠ 0) ∧
      α = ∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η + d′ := by
  classical
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η * X)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  have hinjφ : Function.Injective (algebraMap F[X] F⟮t⟯) := IsFractionRing.injective _ _
  -- no new constants, at the level of polynomials
  have hconstE : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n := by
    intro P n hP
    have hXn : algebraMap F[X] F⟮t⟯ (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ hinjφ).mpr (pow_ne_zero _ X_ne_zero)
    have h0 : (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n))′ = 0 := by
      rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap]
      simp only [smul_eq_mul, ← map_mul, ← map_sub]
      rw [show X ^ n * P′ - P * (X ^ n)′ = 0 by rw [← hP]; ring, map_zero, mul_zero]
    have h1 : ((algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n) : F⟮t⟯) : E)′ = 0 := by
      exact congrArg Subtype.val h0
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n)).2 h1
    refine ⟨e, hinjt ?_⟩
    have hXnE : aeval t (X ^ n : F[X]) ≠ 0 := by
      rw [← algebraMap_adjoinSimple]
      exact fun h' ↦ hXn (Subtype.ext h')
    rw [map_mul, aeval_C, he, IntermediateField.coe_div, algebraMap_adjoinSimple,
      algebraMap_adjoinSimple]
    field_simp
  -- lift the data to `F⟮t⟯`
  let u' : ι → F⟮t⟯ := fun i ↦ if hi : i ∈ s then ⟨u i, (hu i hi).1⟩ else 1
  let v' : F⟮t⟯ := ⟨v, hv⟩
  have hu' : ∀ i ∈ s, u' i ≠ 0 := fun i hi h0 ↦ by
    simp only [u', dif_pos hi] at h0
    exact (hu i hi).2 (congrArg Subtype.val h0)
  have hcoeC : ∀ a : F, ((algebraMap F[X] F⟮t⟯ (C a) : F⟮t⟯) : E) = algebraMap F E a := fun a ↦ by
    rw [algebraMap_adjoinSimple, aeval_C]
  have hlog : ∀ i ∈ s, ((logDeriv (u' i) : F⟮t⟯) : E) = logDeriv (u i) := fun i hi ↦ by
    simp only [u', dif_pos hi, logDeriv, IntermediateField.coe_div]
    rfl
  have h' : algebraMap F[X] F⟮t⟯ (C α) =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [hcoeC, h, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  exact liouville_exponential_core (K := F⟮t⟯) η (fun _ ↦ rfl) hconstE s c u' hu' v' α h'

/-- **The Risch differential equation criterion inside an ambient field.** If `f t` has a Liouville
form with data in `F⟮t⟯ ⊆ E` (`t′ = η t`, `t` transcendental, no new constants), then
`y′ + η y = f` has a solution `y ∈ F`. -/
theorem rde_step_exponential (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η * t)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (v : E) (hv : v ∈ F⟮t⟯) (f : F)
    (h : algebraMap F E f * t = ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    ∃ y : F, y′ + η * y = f := by
  classical
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η * X)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  have hinjφ : Function.Injective (algebraMap F[X] F⟮t⟯) := IsFractionRing.injective _ _
  -- no new constants, at the level of polynomials
  have hconstE : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n := by
    intro P n hP
    have hXn : algebraMap F[X] F⟮t⟯ (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ hinjφ).mpr (pow_ne_zero _ X_ne_zero)
    have h0 : (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n))′ = 0 := by
      rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap]
      simp only [smul_eq_mul, ← map_mul, ← map_sub]
      rw [show X ^ n * P′ - P * (X ^ n)′ = 0 by rw [← hP]; ring, map_zero, mul_zero]
    have h1 : ((algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n) : F⟮t⟯) : E)′ = 0 := by
      exact congrArg Subtype.val h0
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n)).2 h1
    refine ⟨e, hinjt ?_⟩
    have hXnE : aeval t (X ^ n : F[X]) ≠ 0 := by
      rw [← algebraMap_adjoinSimple]
      exact fun h' ↦ hXn (Subtype.ext h')
    rw [map_mul, aeval_C, he, IntermediateField.coe_div, algebraMap_adjoinSimple,
      algebraMap_adjoinSimple]
    field_simp
  -- lift the data to `F⟮t⟯`
  let u' : ι → F⟮t⟯ := fun i ↦ if hi : i ∈ s then ⟨u i, (hu i hi).1⟩ else 1
  let v' : F⟮t⟯ := ⟨v, hv⟩
  have hu' : ∀ i ∈ s, u' i ≠ 0 := fun i hi h0 ↦ by
    simp only [u', dif_pos hi] at h0
    exact (hu i hi).2 (congrArg Subtype.val h0)
  have hcoeC : ∀ a : F, ((algebraMap F[X] F⟮t⟯ (C a) : F⟮t⟯) : E) = algebraMap F E a := fun a ↦ by
    rw [algebraMap_adjoinSimple, aeval_C]
  have hlog : ∀ i ∈ s, ((logDeriv (u' i) : F⟮t⟯) : E) = logDeriv (u i) := fun i hi ↦ by
    simp only [u', dif_pos hi, logDeriv, IntermediateField.coe_div]
    rfl
  have h' : algebraMap F[X] F⟮t⟯ (C f * X) =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, map_mul, aeval_C, aeval_X, h, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  exact exists_rde_solution_of_liouville (K := F⟮t⟯) η (fun _ ↦ rfl) hconstE s c u' hu' v' f h'


/-- **The criterion for polynomials in `t`, inside an ambient field.** If `A(t)` (`A ∈ F[X]`,
`t′ = η t`, `t` transcendental, no new constants) has a Liouville form with data in `F⟮t⟯ ⊆ E`,
then for every `j ≥ 1` the equation `y′ + j η y = A_j` has a solution `y ∈ F`. -/
theorem rde_step_exponential_poly (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η * t)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (v : E) (hv : v ∈ F⟮t⟯) (A : F[X])
    (h : aeval t A = ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) (j : ℕ) (hj : j ≠ 0) :
    ∃ y : F, y′ + (j : F) * η * y = A.coeff j := by
  classical
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η * X)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  have hinjφ : Function.Injective (algebraMap F[X] F⟮t⟯) := IsFractionRing.injective _ _
  -- no new constants, at the level of polynomials
  have hconstE : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n := by
    intro P n hP
    have hXn : algebraMap F[X] F⟮t⟯ (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ hinjφ).mpr (pow_ne_zero _ X_ne_zero)
    have h0 : (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n))′ = 0 := by
      rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap]
      simp only [smul_eq_mul, ← map_mul, ← map_sub]
      rw [show X ^ n * P′ - P * (X ^ n)′ = 0 by rw [← hP]; ring, map_zero, mul_zero]
    have h1 : ((algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n) : F⟮t⟯) : E)′ = 0 := by
      exact congrArg Subtype.val h0
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P / algebraMap F[X] F⟮t⟯ (X ^ n)).2 h1
    refine ⟨e, hinjt ?_⟩
    have hXnE : aeval t (X ^ n : F[X]) ≠ 0 := by
      rw [← algebraMap_adjoinSimple]
      exact fun h' ↦ hXn (Subtype.ext h')
    rw [map_mul, aeval_C, he, IntermediateField.coe_div, algebraMap_adjoinSimple,
      algebraMap_adjoinSimple]
    field_simp
  -- lift the data to `F⟮t⟯`
  let u' : ι → F⟮t⟯ := fun i ↦ if hi : i ∈ s then ⟨u i, (hu i hi).1⟩ else 1
  let v' : F⟮t⟯ := ⟨v, hv⟩
  have hu' : ∀ i ∈ s, u' i ≠ 0 := fun i hi h0 ↦ by
    simp only [u', dif_pos hi] at h0
    exact (hu i hi).2 (congrArg Subtype.val h0)
  have hcoeC : ∀ a : F, ((algebraMap F[X] F⟮t⟯ (C a) : F⟮t⟯) : E) = algebraMap F E a := fun a ↦ by
    rw [algebraMap_adjoinSimple, aeval_C]
  have hlog : ∀ i ∈ s, ((logDeriv (u' i) : F⟮t⟯) : E) = logDeriv (u i) := fun i hi ↦ by
    simp only [u', dif_pos hi, logDeriv, IntermediateField.coe_div]
    rfl
  have h' : algebraMap F[X] F⟮t⟯ A =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, h, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  exact exists_rde_solutions_of_liouville (K := F⟮t⟯) η (fun _ ↦ rfl) hconstE s c u' hu' v' A h'
    j hj



end Differential
