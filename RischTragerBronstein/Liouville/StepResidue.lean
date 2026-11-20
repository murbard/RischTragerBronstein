import RischTragerBronstein.Liouville.SimpleTranscendental
import RischTragerBronstein.Liouville.ResidueCriterion
import RischTragerBronstein.Liouville.Reduce

/-!
# `1 / t` has no Liouville form, for a primitive `t`

`not_liouville_inv_primitive`: let `E / F` be differential fields, `t ∈ E` transcendental over `F`
with `t′ = η ∈ F`, `η ≠ 0`, and suppose no constant `N ∈ F` satisfies `N η = 1`. Then `1 / t` is
**not** of the form `∑ cᵢ uᵢ′ / uᵢ + v′` with `uᵢ, v ∈ F⟮t⟯` and constant `cᵢ ∈ F`.

This is the residue criterion at the prime `p = t`: the residue of `1 / t` is `1 / η`, which would
have to be a constant. For `t = log x`, `η = 1 / x`, it shows that the logarithmic integral
`∫ dx / log x` is not elementary (`RDE/LogIntegral.lean`).
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

theorem not_liouville_inv_primitive (t : E) (htr : Transcendental F t) (η : F) (hη0 : η ≠ 0)
    (ht : t′ = algebraMap F E η) (hη : ∀ N : F, N′ = 0 → N * η ≠ 1)
    {ι : Type*} (s : Finset ι) (c : ι → F) (hc : ∀ i ∈ s, (c i)′ = 0) (u : ι → E)
    (hu : ∀ i ∈ s, u i ∈ F⟮t⟯ ∧ u i ≠ 0) (v : E) (hv : v ∈ F⟮t⟯) :
    t⁻¹ ≠ ∑ i ∈ s, algebraMap F E (c i) * logDeriv (u i) + v′ := by
  classical
  intro h
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht]
  let _ := algebraAdjoinSimple (F := F) t
  let _ : Differential F[X] := polynomialOfDeriv (C η)
  let _ : Differential F⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t (C η) hw)
  have hFR : IsFractionRing F[X] F⟮t⟯ := isFractionRing_adjoin_simple t htr
  have hDA : DifferentialAlgebra F[X] F⟮t⟯ := differentialAlgebra_adjoin_simple t (C η) hw
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
  have h' : algebraMap F[X] F⟮t⟯ 1 / algebraMap F[X] F⟮t⟯ (X * 1) =
      ∑ i ∈ s, algebraMap F[X] F⟮t⟯ (C (c i)) * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    rw [IntermediateField.coe_div, algebraMap_adjoinSimple, algebraMap_adjoinSimple, map_one,
      mul_one, aeval_X, one_div, h, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, hcoeC, hlog i hi]
  -- `X` is a normal prime: `X′ = η ≠ 0` is a nonzero constant
  have hXd : (X : F[X])′ = C η := implicitDeriv_X (C η)
  have hnorm : ¬(X : F[X]) ∣ (X : F[X])′ := by
    rw [hXd]
    intro hdvd
    exact hη0 (eq_zero_of_prime_dvd_C prime_X hdvd)
  obtain ⟨N, hN, hdvd⟩ := residue_criterion (K := F⟮t⟯) prime_X hnorm 1 1
    (fun h1 ↦ not_isUnit_X (isUnit_of_dvd_one h1)) s c hc u' hu' v' h'
  rw [mul_one, hXd, ← C_mul, ← C_1, ← C_sub] at hdvd
  have := eq_zero_of_prime_dvd_C prime_X hdvd
  exact hη N hN (by linear_combination -this)

end Differential
