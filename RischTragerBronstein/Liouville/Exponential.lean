import RischTragerBronstein.Liouville.ExponentialCore
import RischTragerBronstein.Differential.Constants
import Mathlib.FieldTheory.Differential.Liouville

/-!
# Liouville's theorem for an exponential extension

`isLiouville_exp`: if `t = exp a₁` is adjoined to `F` (`F(t) = RatFunc F`, `t′ = a₁′ t`) without
creating new constants, then `F(t) / F` is a Liouville extension in the sense of Mathlib's
`IsLiouville`. Together with `isLiouville_log` and Mathlib's algebraic case this covers the three
kinds of elementary steps.
-/

open Finset Polynomial

namespace Differential

variable {F : Type*} [Field F] [CharZero F] [Differential F]

theorem isLiouville_exp (a₁ : F)
    (hconst : letI := ratFuncOfDeriv (C a₁′ * X)
      ∀ f : RatFunc F, f′ = 0 → f ∈ Set.range (algebraMap F (RatFunc F))) :
    letI := ratFuncOfDeriv (C a₁′ * X)
    letI := differentialAlgebra_ratFuncOfDeriv (C a₁′ * X)
    IsLiouville F (RatFunc F) := by
  classical
  let _ : Differential F[X] := polynomialOfDeriv (C a₁′ * X)
  let _ : Differential (RatFunc F) := ratFuncOfDeriv (C a₁′ * X)
  have hDAF : DifferentialAlgebra F (RatFunc F) := differentialAlgebra_ratFuncOfDeriv _
  have hDAP : DifferentialAlgebra F[X] (RatFunc F) := differentialAlgebra_ofFractionRing _ _
  let φ : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  have hcast : ∀ y : F, algebraMap F (RatFunc F) y = φ (C y) := fun y ↦ by
    rw [RatFunc.algebraMap_eq_C]; exact (RatFunc.algebraMap_C y).symm
  have hconstE : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n := by
    intro P n hP
    have h0 : (φ P / φ (X ^ n))′ = 0 :=
      (ofFractionRing_deriv_div_eq_zero_iff F[X] (RatFunc F) P (X ^ n)
        (pow_ne_zero _ X_ne_zero)).mpr hP
    obtain ⟨e, he⟩ := hconst _ h0
    refine ⟨e, RatFunc.algebraMap_injective F ?_⟩
    have hX : φ (X ^ n) ≠ 0 := RatFunc.algebraMap_ne_zero (pow_ne_zero _ X_ne_zero)
    rw [map_mul, ← hcast, he]
    change φ P = φ P / φ (X ^ n) * φ (X ^ n)
    field_simp
  refine ⟨?_⟩
  intro a ι _ c hc u v h
  let s : Finset ι := Finset.univ.filter fun i ↦ u i ≠ 0
  have hsum : ∑ i, algebraMap F (RatFunc F) (c i) * logDeriv (u i) =
      ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with hi
    · rw [hcast]
    · rw [not_not.mp hi, logDeriv_zero, mul_zero]
  have h' : φ (C a) = ∑ i ∈ s, φ (C (c i)) * logDeriv (u i) + v′ := by
    rw [← hcast, ← hsum]; exact h
  obtain ⟨e, m, d, he, hfin⟩ := liouville_exponential_core (K := RatFunc F) a₁′
    (fun _ ↦ rfl) hconstE s c u (fun i hi ↦ (Finset.mem_filter.mp hi).2) v a h'
  -- `∑ cᵢ mᵢ` is a constant
  have hN : (∑ i ∈ s, c i * (m i : F))′ = 0 := by
    rw [← mem_constants]
    exact sum_mem fun i _ ↦ mul_mem (mem_constants.mpr (hc i)) (intCast_mem _ _)
  refine ⟨ι, inferInstance, c, hc, fun i ↦ if u i ≠ 0 then e i else 1,
    (∑ i ∈ s, c i * (m i : F)) * a₁ + d, ?_⟩
  have : ∑ i, c i * logDeriv (if u i ≠ 0 then e i else 1) = ∑ i ∈ s, c i * logDeriv (e i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with hi
    · rfl
    · rw [logDeriv_one, mul_zero]
  rw [this, hfin, map_add, Derivation.leibniz, hN]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

end Differential
