import RischTragerBronstein.Computable.Prim2BaseResiduePos
import RischTragerBronstein.Computable.Prim2Base
import RischTragerBronstein.Computable.HermiteF0
import RischTragerBronstein.Computable.IntegrateLog

/-!
# Height three: general elements of `R(x)(t₁)` inside `R(x)(t₁)(t₂)` — decided

For `α = Ap(t₁) + b(t₁) / s(t₁)` (`s` certified squarefree and coprime to `s′`, `deg b < deg s`;
this is the output format of Hermite reduction followed by a division) viewed in
`K = R(x)(t₁)(t₂)`:

`α` has an elementary integral over `K` **iff** the residue test passes on `b / s` and `primLoop`
succeeds on `Ap`. The second primitive never helps at level `t₁`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- The value of a polynomial code, written with the normalised coefficient codes. -/
theorem valP_eq_sum_poly (x₀ t₁ : F₀) (q : GPoly (GFrac R)) :
    Tower.valP x₀ t₁ q = ∑ j ∈ Finset.range (q.length + 1),
      aeval x₀ (toPoly (Tower.polyA q j)) / aeval x₀ (toPoly (Tower.polyD q j)) * t₁ ^ j := by
  have hn : ∀ j, aeval x₀ (toPoly (Tower.polyA q j)) / aeval x₀ (toPoly (Tower.polyD q j)) =
      aeval x₀ (toPoly (q.getD j ([], [1])).1) / aeval x₀ (toPoly (q.getD j ([], [1])).2) :=
    fun j ↦ by
      unfold Tower.polyA Tower.polyD Tower.normFrac
      split_ifs with hz
      · have hz' := (isZero_iff _).mp hz
        rw [hz', map_zero, div_zero]
        simp [toPoly]
      · rfl
  rw [Finset.sum_range_succ, hn, List.getD_eq_default _ _ le_rfl]
  simp only [toPoly, map_zero, zero_div, zero_mul, add_zero, Tower.valP, hn]

/-- **General elements of `R(x)(t₁)` inside a tower of two primitives: decided.** -/
theorem prim2BaseFull_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (Ap bc sc : GPoly (GFrac R))
    (hsqc : GPoly.squarefreeCheck (Tower.ops₁g R) sc = true)
    (hcopc : GPoly.coprimeDerivCheck (Tower.ops₁g R) [(En₁, Ed₁)] sc = true)
    (hlen : (GPoly.trim (Tower.ops₁g R) bc).length < (GPoly.trim (Tower.ops₁g R) sc).length) :
    HasElementaryIntegral (algebraMap F₀ K
        (Tower.valP x₀ t₁ Ap + Tower.valP x₀ t₁ bc / Tower.valP x₀ t₁ sc)) ↔
      (GPoly.residueCheck (Tower.ops₁g R) [(En₁, Ed₁)] bc sc &&
        (primLoop En₁ Ed₁ Iη₁ (Tower.polyA Ap) (Tower.polyD Ap) Ap.length ([], [1])).isSome) =
        true := by
  have hbase := prim2Base_decides (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht
    Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep Ap.length (Tower.polyA Ap) (Tower.polyD Ap)
    (fun j _ ↦ Tower.normFrac_den_ne_zero _)
  rw [← valP_eq_sum_poly] at hbase
  rw [Bool.and_eq_true, ← hbase]
  constructor
  · intro h
    have hres : GPoly.residueCheck (Tower.ops₁g R) [(En₁, Ed₁)] bc sc = true := by
      by_contra hf
      rw [Bool.not_eq_true] at hf
      obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h
      exact not_elementary_prim2BaseResidue hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht
        Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep Ap bc sc hsqc hcopc hf E hE g hg
    refine ⟨hres, ?_⟩
    have := h.sub_in (hasElementaryIntegralIn_prim2BaseResidue (K := K) hR x₀ t₁ hx₀ ht₁ hcη₁
      hη₁0 bc sc hsqc hcopc hlen hres)
    rwa [← map_sub, add_sub_cancel_right] at this
  · rintro ⟨hres, h⟩
    rw [map_add]
    exact h.add_in (hasElementaryIntegralIn_prim2BaseResidue (K := K) hR x₀ t₁ hx₀ ht₁ hcη₁
      hη₁0 bc sc hsqc hcopc hlen hres)

/-- Adding a derivative of an element of the field does not change elementary integrability. -/
theorem hasElementaryIntegral_deriv_add_iff (g β : K) :
    HasElementaryIntegral (g′ + β) ↔ HasElementaryIntegral β := by
  constructor
  · intro h
    have := h.sub_in (hasElementaryIntegralIn_deriv g)
    rwa [add_sub_cancel_left] at this
  · intro h
    rw [add_comm]
    exact h.add_in (hasElementaryIntegralIn_deriv g)

/-- **Every element of `R(x)(t₁)`, viewed in a tower of two primitives, is decided by the
height-two integrator `Tower.integratePrim`.** -/
theorem prim2BaseGen_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.isZero (Tower.ops₁g R) Gd = false) :
    HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ (Gn, Gd))) ↔
      Tower.integratePrim En₁ Ed₁ Iη₁ Gn Gd = true := by
  obtain ⟨hid, hsqc, hcopc, hlen⟩ := Tower.hermite_valG_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 Gn Gd hGd
  rw [hid, map_add, ← deriv_algebraMap, hasElementaryIntegral_deriv_add_iff,
    prim2BaseFull_decides hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht Iη₁ Iη₂ hcη₁ hcη₂
      hη₁0 hindep _ _ _ hsqc hcopc hlen]
  rfl

end CPoly
