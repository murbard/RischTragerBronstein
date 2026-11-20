import RischTragerBronstein.Computable.HexpPrimBaseResidue
import RischTragerBronstein.Computable.Prim2BaseFull

/-!
# An exponential over `R(x)(t₁)`: every element of `R(x)(t₁)` at level `0`

Viewed in `K = R(x)(t₁)(t₂)`, an element of `R(x)(t₁)` has an elementary integral iff the
height-two integrator `Tower.integratePrim` says so.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]
variable [HasRatRoots R] [HasNatTest R]

/-- **General elements of `R(x)(t₁)` under an exponential: decided.** -/
theorem hexpPrimBaseFull_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (Gn Gd μ : CPoly R) (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (hcop : IsCoprime (toPoly Gn) (toPoly Gd)) (hcert : hyperexpMonomialCheck Gn Gd μ = true)
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * t)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (Ap bc sc : GPoly (GFrac R))
    (hsqc : GPoly.squarefreeCheck (Tower.ops₁g R) sc = true)
    (hcopc : GPoly.coprimeDerivCheck (Tower.ops₁g R) [(En₁, Ed₁)] sc = true)
    (hlen : (GPoly.trim (Tower.ops₁g R) bc).length < (GPoly.trim (Tower.ops₁g R) sc).length) :
    HasElementaryIntegral (algebraMap F₀ K
        (Tower.valP x₀ t₁ Ap + Tower.valP x₀ t₁ bc / Tower.valP x₀ t₁ sc)) ↔
      (GPoly.residueCheck (Tower.ops₁g R) [(En₁, Ed₁)] bc sc &&
        (primLoop En₁ Ed₁ Iη₁ (Tower.polyA Ap) (Tower.polyD Ap) Ap.length ([], [1])).isSome) =
        true := by
  have hbase := hexpPrimBase_decides (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ Gn Gd μ hGn0 hGd0 hcop hcert t ht0 hgen ht
    Iη₁ hcη₁ hη₁0 Ap.length (Tower.polyA Ap) (Tower.polyD Ap)
    (fun j _ ↦ Tower.normFrac_den_ne_zero _)
  rw [← valP_eq_sum_poly] at hbase
  rw [Bool.and_eq_true, ← hbase]
  constructor
  · intro h
    have hres : GPoly.residueCheck (Tower.ops₁g R) [(En₁, Ed₁)] bc sc = true := by
      by_contra hf
      rw [Bool.not_eq_true] at hf
      obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h
      exact not_elementary_hexpPrimBaseResidue hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ Gn Gd μ hGn0 hGd0 hcop hcert t ht0 hgen ht
        Iη₁ hcη₁ hη₁0 Ap bc sc hsqc hcopc hf E hE g hg
    refine ⟨hres, ?_⟩
    have := h.sub_in (hasElementaryIntegralIn_prim2BaseResidue (K := K) hR x₀ t₁ hx₀ ht₁ hcη₁
      hη₁0 bc sc hsqc hcopc hlen hres)
    rwa [← map_sub, add_sub_cancel_right] at this
  · rintro ⟨hres, h⟩
    rw [map_add]
    exact h.add_in (hasElementaryIntegralIn_prim2BaseResidue (K := K) hR x₀ t₁ hx₀ ht₁ hcη₁
      hη₁0 bc sc hsqc hcopc hlen hres)

/-- **Every element of `R(x)(t₁)`, viewed under an exponential `t₂ = log u`, is decided by the
height-two integrator `Tower.integratePrim`.** -/
theorem hexpPrimBaseGen_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : hyperexpMonomialCheck Hn Hd μ = true)
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd)) * t)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.isZero (Tower.ops₁g R) Gd = false) :
    HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ (Gn, Gd))) ↔
      Tower.integratePrim En₁ Ed₁ Iη₁ Gn Gd = true := by
  obtain ⟨hid, hsqc, hcopc, hlen⟩ := Tower.hermite_valG_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 Gn Gd hGd
  rw [hid, map_add, ← deriv_algebraMap, hasElementaryIntegral_deriv_add_iff,
    hexpPrimBaseFull_decides hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ Hn Hd μ hHn0 hHd0 hcop hcert t ht0 hgen ht
      Iη₁ hcη₁ hη₁0 _ _ _ hsqc hcopc hlen]
  rfl

end CPoly
