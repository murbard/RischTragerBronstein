import RischTragerBronstein.Liouville.PrimitiveCore
import Mathlib.FieldTheory.Differential.Liouville

/-!
# Liouville's theorem for a logarithmic extension

`isLiouville_log`: if `t = log a₀` is adjoined to `F` (`F(t) = RatFunc F`, `t′ = a₀′ / a₀`) without
creating new constants, then `F(t) / F` is a Liouville extension in the sense of Mathlib's
`IsLiouville`. Mathlib proves this for algebraic extensions only; this is the logarithmic
transcendental case.
-/

open Finset Polynomial

namespace Differential

variable {F : Type*} [Field F] [CharZero F] [Differential F]

theorem isLiouville_log (a₀ : F)
    (hconst : letI := ratFuncOfDeriv (C (logDeriv a₀))
      ∀ f : RatFunc F, f′ = 0 → f ∈ Set.range (algebraMap F (RatFunc F))) :
    letI := ratFuncOfDeriv (C (logDeriv a₀))
    letI := differentialAlgebra_ratFuncOfDeriv (C (logDeriv a₀))
    IsLiouville F (RatFunc F) := by
  classical
  let _ : Differential F[X] := polynomialOfDeriv (C (logDeriv a₀))
  let _ : Differential (RatFunc F) := ratFuncOfDeriv (C (logDeriv a₀))
  have hDAF : DifferentialAlgebra F (RatFunc F) := differentialAlgebra_ratFuncOfDeriv _
  have hDAP : DifferentialAlgebra F[X] (RatFunc F) := differentialAlgebra_ofFractionRing _ _
  let φ : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  have hcast : ∀ y : F, algebraMap F (RatFunc F) y = φ (C y) := fun y ↦ by
    rw [RatFunc.algebraMap_eq_C]; exact (RatFunc.algebraMap_C y).symm
  have hconstP : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e := fun P hP ↦ by
    have : (φ P)′ = 0 := by rw [deriv_algebraMap (A := F[X]) (B := RatFunc F) P, hP, map_zero]
    obtain ⟨e, he⟩ := hconst _ this
    exact ⟨e, RatFunc.algebraMap_injective F (by rw [← he, hcast])⟩
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
  obtain ⟨e, c₀, d, he, hc₀, hfin⟩ := liouville_primitive_core (K := RatFunc F) (logDeriv a₀)
    (fun _ ↦ rfl) hconstP s c u (fun i hi ↦ (Finset.mem_filter.mp hi).2) v a h'
  refine ⟨Option ι, inferInstance, fun o ↦ o.elim c₀ c, ?_,
    fun o ↦ o.elim a₀ fun i ↦ if u i ≠ 0 then e i else 1, d, ?_⟩
  · rintro (_ | i)
    · exact hc₀
    · exact hc i
  · rw [Fintype.sum_option, hfin]
    simp only [Option.elim]
    have : ∑ i, c i * logDeriv (if u i ≠ 0 then e i else 1) = ∑ i ∈ s, c i * logDeriv (e i) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      split_ifs with hi
      · rfl
      · rw [logDeriv_one, mul_zero]
    rw [this]
    ring

end Differential
