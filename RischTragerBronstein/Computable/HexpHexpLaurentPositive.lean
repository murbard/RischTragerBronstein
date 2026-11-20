import RischTragerBronstein.Computable.HexpHexpLaurentStrong
import RischTragerBronstein.Computable.ExpPrimLaurentPositive
import RischTragerBronstein.Computable.ExpExpLaurentPositive

/-!
# Two general hyperexponentials: the Laurent part is integrated by `rdeHexp₂`
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀] [CPoly.HasRatRoots R] [HasNatTest R]

variable {K : Type*} [Field K] [Algebra F₀ K] [Differential K] [DifferentialAlgebra F₀ K]

/-- **The Laurent part is integrated** (two hyperexponentials). -/
theorem hexpHexpLaurent_antiderivative (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁)
    (Hn₂ Hd₂ : CPoly R) (hHd20 : toPoly Hd₂ ≠ 0) (t : K) (ht0 : t ≠ 0)
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly Hn₂) / aeval x₀ (toPoly Hd₂)) * t)
    (N n : ℕ) (A : ℕ → GFrac (GFrac R)) (Y : ℕ → GPoly (GFrac R))
    (hD0 : ∀ j < N, GPoly.isZero (ops₁g R) (A j).2 = false)
    (hsome : ∀ j < N, j ≠ n → rdeHexp₂ Hn Hd (smul ((((j : ℤ) - n : ℤ)) : R) Hn₂) Hd₂ (A j).1
      (GPoly.splitX (ops₁g R) (A j).2).2 (GPoly.splitX (ops₁g R) (A j).2).1 = some (Y j)) :
    (∑ j ∈ (Finset.range N).erase n,
        algebraMap F₀ K (valP x₀ t₁ (Y j) / valP x₀ t₁ (A j).2) * t ^ j / t ^ n)′ =
      ∑ j ∈ (Finset.range N).erase n, algebraMap F₀ K (valG x₀ t₁ (A j)) * t ^ j / t ^ n := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap F₀ K).injective
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  obtain ⟨hjn, hjN⟩ := Finset.mem_erase.mp hj
  have hjN' := Finset.mem_range.mp hjN
  have hsp0 : GPoly.isZero (ops₁g R) (GPoly.splitX (ops₁g R) (A j).2).2 = false :=
    isZero_splitX_false hR x₀ hx₀ _ (hD0 j hjN')
  have hsol := rdeHexp₂_sound_F₀ hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ _ _ hHd20 _ _ _
    hsp0 (hsome j hjN' hjn)
  rw [← valP_splitX hR x₀ t₁ hx₀ (A j).2] at hsol
  have hg : aeval x₀ (toPoly (smul ((((j : ℤ) - n : ℤ)) : R) Hn₂)) / aeval x₀ (toPoly Hd₂) =
      ((j : F₀) - n) * (aeval x₀ (toPoly Hn₂) / aeval x₀ (toPoly Hd₂)) := by
    rw [toPoly_smul, map_mul, aeval_C, mul_div_assoc]
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
  rw [hg] at hsol
  rw [deriv_mul_pow_div_pow _ t _ ht0 ht, valG, ← map_natCast (algebraMap F₀ K) j,
    ← map_natCast (algebraMap F₀ K) n, ← map_sub, ← map_mul, deriv_algebraMap, ← map_mul,
    ← map_add, hsol]

end Tower
