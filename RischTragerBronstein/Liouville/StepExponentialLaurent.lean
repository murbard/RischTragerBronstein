import RischTragerBronstein.Liouville.StepExponential

/-!
# The Laurent step for an exponential, inside an ambient field

If `A(t) / t ^ n` (`t = exp`, transcendental over `F`) has an integral of Liouville form inside
`F(t) ⊆ E`, then every coefficient `A_j`, `j ≠ n`, satisfies a Risch differential equation over
`F`, and `A_n` has a limited integral over `F`.
-/


set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- Laurent polynomials in an exponential: coefficientwise criteria. -/
theorem rde_step_exponential_laurent (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η * t)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    {ι : Type*} (s : Finset ι) (c : ι → F) (u : ι → E) (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0)
    (v : E) (hv : v ∈ F⟮t⟯) (A : F[X])
    (n : ℕ) (h : aeval t A / t ^ n = ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′) :
    (∀ j : ℕ, j ≠ n → ∃ y : F, y′ + ((j : F) - n) * η * y = A.coeff j) ∧
      ∃ (e : ι → F) (m : ι → ℤ) (d : F), (∀ i ∈ s, e i ≠ 0) ∧
        A.coeff n = ∑ i ∈ s, c i * logDeriv (e i) + (∑ i ∈ s, c i * m i) * η + d′ := by
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
  have h' : algebraMap F[X] F⟮t⟯ A / algebraMap F[X] F⟮t⟯ X ^ n =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [IntermediateField.coe_div, IntermediateField.coe_pow, algebraMap_adjoinSimple,
      algebraMap_adjoinSimple, aeval_X, h, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  exact ⟨fun j hj ↦ exists_rde_solutions_of_liouville_laurent (K := F⟮t⟯) η (fun _ ↦ rfl) hconstE
      s c u' hu' v' A n h' j hj,
    exists_limited_of_liouville_laurent (K := F⟮t⟯) η (fun _ ↦ rfl) hconstE s c u' hu' v' A n h'⟩

end Differential
