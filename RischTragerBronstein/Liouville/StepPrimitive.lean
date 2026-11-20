import RischTragerBronstein.Liouville.SimpleTranscendental
import RischTragerBronstein.Liouville.PrimitiveCore

/-!
# One Liouville step inside an ambient field: primitive case

`liouville_step_primitive`: let `E / F` be differential fields, `t ∈ E` transcendental over `F` with
`t′ = η ∈ F`, and suppose `F⟮t⟯` has no constants outside `F`. If `α ∈ F` satisfies
`α = ∑ cᵢ uᵢ′ / uᵢ + v′` with `uᵢ, v ∈ F⟮t⟯` and `cᵢ ∈ F`, then
`α = ∑ cᵢ eᵢ′ / eᵢ + c₀ η + d′` with `eᵢ, d ∈ F` and `c₀ ∈ F` constant.

Same statement as `liouville_primitive_core`, but for a subfield `F⟮t⟯` of an arbitrary ambient `E`
rather than for an abstract fraction field: this is the form needed to descend along a tower.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

theorem liouville_step_primitive (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (v : E) (hv : v ∈ F⟮t⟯) (α : F)
    (h : algebraMap F E α = ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    ∃ (e : ι → F) (c₀ d : F), (∀ i ∈ s, e i ≠ 0) ∧ c₀′ = 0 ∧
      α = ∑ i ∈ s, c i * logDeriv (e i) + c₀ * η + d′ := by
  classical
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t (C η) hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t (C η) hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  -- no new constants, at the level of polynomials
  have hconstP : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e := fun P hP ↦ by
    have h1 : ((algebraMap F[X] F⟮t⟯ P : F⟮t⟯) : E)′ = 0 := by
      have := congrArg (fun y : F⟮t⟯ ↦ (y : E)) (deriv_algebraMap (A := F[X]) (B := F⟮t⟯) P)
      simp only [hP, map_zero, ZeroMemClass.coe_zero] at this
      exact this
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P).2 h1
    refine ⟨e, hinjt ?_⟩
    rw [aeval_C, he, algebraMap_adjoinSimple]
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
  exact liouville_primitive_core (K := F⟮t⟯) η (fun _ ↦ rfl) hconstP s c u' hu' v' α h'

/-- **Limited integration criterion inside an ambient field.** If `f t + f₀` (`t′ = η`, `t`
transcendental, no new constants) has a Liouville form with data in `F⟮t⟯ ⊆ E`, then
`p₁′ + 2 c₂ η = f` for some constant `c₂ ∈ F` and some `p₁ ∈ F`. -/
theorem limited_step_primitive (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (v : E) (hv : v ∈ F⟮t⟯) (f f₀ : F)
    (h : algebraMap F E f * t + algebraMap F E f₀ =
      ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    ∃ c₂ p₁ : F, c₂′ = 0 ∧ p₁′ + 2 * c₂ * η = f := by
  classical
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t (C η) hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t (C η) hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  -- no new constants, at the level of polynomials
  have hconstP : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e := fun P hP ↦ by
    have h1 : ((algebraMap F[X] F⟮t⟯ P : F⟮t⟯) : E)′ = 0 := by
      have := congrArg (fun y : F⟮t⟯ ↦ (y : E)) (deriv_algebraMap (A := F[X]) (B := F⟮t⟯) P)
      simp only [hP, map_zero, ZeroMemClass.coe_zero] at this
      exact this
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P).2 h1
    refine ⟨e, hinjt ?_⟩
    rw [aeval_C, he, algebraMap_adjoinSimple]
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
  have h' : algebraMap F[X] F⟮t⟯ (C f * X + C f₀) =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, map_add, map_mul, aeval_C, aeval_X, aeval_C, h, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  exact exists_limited_integral_of_liouville (K := F⟮t⟯) η (fun _ ↦ rfl) hconstP s c u' hu' v'
    f f₀ h'

/-- Coefficient equations for a polynomial integrand in a primitive `t`, inside an ambient
field. -/
theorem coeffs_step_primitive (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (v : E) (hv : v ∈ F⟮t⟯) (A : F[X])
    (h : aeval t A = ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    ∃ p : ℕ → F, (∀ j, 1 ≤ j → (p j)′ + ((j + 1 : ℕ) : F) * η * p (j + 1) = A.coeff j) ∧
      ∀ d, A.natDegree ≤ d → (p (d + 1))′ = 0 := by
  classical
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t (C η) hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t (C η) hw
  have hinjt : Function.Injective (aeval t : F[X] →ₐ[F] E) := transcendental_iff_injective.mp htr
  -- no new constants, at the level of polynomials
  have hconstP : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e := fun P hP ↦ by
    have h1 : ((algebraMap F[X] F⟮t⟯ P : F⟮t⟯) : E)′ = 0 := by
      have := congrArg (fun y : F⟮t⟯ ↦ (y : E)) (deriv_algebraMap (A := F[X]) (B := F⟮t⟯) P)
      simp only [hP, map_zero, ZeroMemClass.coe_zero] at this
      exact this
    obtain ⟨e, he⟩ := hconst _ (algebraMap F[X] F⟮t⟯ P).2 h1
    refine ⟨e, hinjt ?_⟩
    rw [aeval_C, he, algebraMap_adjoinSimple]
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
    rw [algebraMap_adjoinSimple, h, IntermediateField.coe_add,
      AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  exact exists_coeffs_of_liouville_primitive (K := F⟮t⟯) η (fun _ ↦ rfl) hconstP s c u' hu' v'
    A h'

end Differential
