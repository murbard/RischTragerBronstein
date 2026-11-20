import RischTragerBronstein.Computable.GCodeF0
import RischTragerBronstein.Computable.Prim2BaseFull
import RischTragerBronstein.Computable.Prim2LoopGenPositive
import RischTragerBronstein.Computable.Prim2PolyGenStrong

/-!
# Height three: polynomials in `t₂` with **arbitrary** coefficients in `R(x)(t₁)` — decided

`integratePrim2PolyGen` runs the general `t₂`-loop (`prim2LoopGen`: one parametric limited
integration problem in `R(x)(t₁)` per power of `t₂`) and then hands the level-0 remainder
`A₀ - η₂ Q₁ ∈ R(x)(t₁)` to the height-two integrator `integratePrim`.

`integratePrim2PolyGen_decides`: the answer is `true` **iff** `∑ Aₖ t₂ ^ k` has an elementary
integral over `K = R(x)(t₁)(t₂)`. No assumption on constants.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential Tower

section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- The integrator for `∑ₖ Aₖ t₂ ^ k`, `Aₖ ∈ R(x)(t₁)` given by fraction codes. -/
def integratePrim2PolyGen (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (En₂ Ed₂ : CPoly R)
    (Iη₂ : RationalIntegral R) (A : ℕ → GFrac (GFrac R)) (d₂ : ℕ) : Bool :=
  match prim2LoopGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A d₂ ([], [(ops₁g R).one]) with
  | none => false
  | some L =>
    let G := normF₂ (gCode En₁ Ed₁ En₂ Ed₂ 0 (A 0) (lastGen ([], [(ops₁g R).one]) L))
    integratePrim En₁ Ed₁ Iη₁ G.1 G.2

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **Height three, polynomial part with general coefficients: decided**, both directions. -/
theorem integratePrim2PolyGen_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (d₂ : ℕ) (A : ℕ → GFrac (GFrac R)) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valG x₀ t₁ (A k)) * t ^ k) ↔
      integratePrim2PolyGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A d₂ = true := by
  unfold integratePrim2PolyGen
  cases hL : prim2LoopGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A d₂ ([], [(ops₁g R).one]) with
  | none =>
    simp only [Bool.false_eq_true, iff_false]
    exact not_hasElementaryIntegral_prim2PolyGen hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht
      Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep d₂ A hL
  | some L =>
    simp only
    have hanti := prim2LoopGen_antiderivative (K := K) hR x₀ t₁ hx₀ ht₁ t ht hcη₁ hcη₂ hη₁0
      hindep A d₂ _ hL
    have hQ0 : valG x₀ t₁ (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by
      simp [valG, valP]
    rw [hQ0, map_zero, map_zero, zero_mul, zero_add] at hanti
    obtain ⟨hden, hval⟩ := valG_gCode_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hcη₂ hη₁0 hindep 0 (A 0)
      (lastGen ([], [(ops₁g R).one]) L)
    rw [hanti, hasElementaryIntegral_deriv_add_iff,
      ← prim2BaseGen_decides (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht Iη₁ Iη₂
        hcη₁ hcη₂ hη₁0 hindep _ _ hden, Prod.mk.eta, hval]
    simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]

end CPoly
