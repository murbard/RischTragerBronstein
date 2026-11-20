import RischTragerBronstein.Computable.Prim2ResidueStrong
import RischTragerBronstein.Computable.Prim2PolyPositive

/-!
# Height three: the combined decision for two primitives over `R(x)`

`K = R(x)(t₁)(t₂)`. For an integrand in Hermite-reduced form at the top step,

  `f = g′ + ∑_{k ≤ d₂} Aₖ(x, t₁) t₂ ^ k + b(t₂) / sd(t₂)`,

`Aₖ ∈ R(x)[t₁]` (codes), `sd ∈ R(x)(t₁)[t₂]` squarefree, `deg b < deg sd`:

`f` has an elementary integral **iff** the residue test passes and `integratePrim2Poly` succeeds.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

theorem prim2Full_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (g : K) (d₂ : ℕ) (A : ℕ → Poly2 R) (hA : ∀ k, (A k).Wf)
    (b sd r : F₀[X]) (hsd : Squarefree sd) (hdeg : b.degree < sd.degree)
    (hst : aeval t sd ≠ 0)
    (hr : sd ∣ r * (mapCoeffs sd +
      C (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) * derivative sd) - b) :
    HasElementaryIntegral (g′ + ∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valF₀ x₀ t₁ (A k)) * t ^ k + aeval t b / aeval t sd) ↔
      sd ∣ residueTest r sd ∧ integratePrim2Poly En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A d₂ = true := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  set Asum : K := ∑ k ∈ Finset.range (d₂ + 1), algebraMap F₀ K (valF₀ x₀ t₁ (A k)) * t ^ k
    with hAsum
  set Ap : F₀[X] := ∑ k ∈ Finset.range (d₂ + 1), C (valF₀ x₀ t₁ (A k)) * X ^ k with hAp
  have hApv : aeval t Ap = Asum := by
    simp only [hAp, hAsum, map_sum, map_mul, map_pow, aeval_C, aeval_X]
  set η₀ : F₀ := aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂) with hη₀
  have hlogIn : sd ∣ residueTest r sd → HasElementaryIntegralIn (aeval t b / aeval t sd) :=
    fun hT ↦ hasElementaryIntegralIn_of_residueTest t η₀ 0
      (by rw [ht, map_zero, zero_mul, add_zero]) 1 one_ne_zero (by rw [logDeriv_one, map_zero])
      sd b r (PerfectField.separable_iff_squarefree.mpr hsd) hst hdeg
      (by rwa [C_0, zero_mul, add_zero]) hT
  have hpoly := integratePrim2Poly_decides (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen
    ht Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep d₂ A hA
  constructor
  · intro hf
    have h1 : HasElementaryIntegral (Asum + aeval t b / aeval t sd) := by
      have := hf.sub_in (hasElementaryIntegralIn_deriv g)
      have heq : g′ + Asum + aeval t b / aeval t sd - g′ = Asum + aeval t b / aeval t sd := by
        ring
      rwa [heq] at this
    have hT : sd ∣ residueTest r sd := by
      by_contra hT
      have hr' : sd ∣ r * (mapCoeffs sd + C η₀ * derivative sd) - (Ap * sd + b) := by
        have : r * (mapCoeffs sd + C η₀ * derivative sd) - (Ap * sd + b) =
            (r * (mapCoeffs sd + C η₀ * derivative sd) - b) - Ap * sd := by ring
        rw [this]
        exact dvd_sub hr (dvd_mul_left sd Ap)
      refine not_hasElementaryIntegral_prim2Residue hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen
        ht Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep (Ap * sd + b) sd r hsd hr' hT ?_
      rw [map_add, map_mul, add_div, mul_div_assoc, div_self hst, mul_one, hApv]
      exact h1
    refine ⟨hT, hpoly.mp ?_⟩
    have := h1.sub_in (hlogIn hT)
    rwa [add_sub_cancel_right] at this
  · rintro ⟨hT, hsome⟩
    have hA' : HasElementaryIntegral Asum := hpoly.mpr hsome
    have := ((hA'.add_in (hlogIn hT)).add_in (hasElementaryIntegralIn_deriv g))
    have heq : g′ + Asum + aeval t b / aeval t sd = Asum + aeval t b / aeval t sd + g′ := by
      ring
    rwa [heq]

end CPoly
