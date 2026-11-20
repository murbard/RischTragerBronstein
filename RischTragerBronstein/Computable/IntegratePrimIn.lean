import RischTragerBronstein.Computable.Prim2BaseFull

/-!
# The height-two integrator is sound in every larger field

If `Tower.integratePrim En₁ Ed₁ Iη₁ Gn Gd = true`, then the element `Gn / Gd` of
`F₀ = R(x₀)(t₁)` has an elementary integral over **every** differential field `K ⊇ F₀`
(no hypothesis on how `K` is generated).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

theorem hasElementaryIntegral_valG_of_integratePrim (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.isZero (Tower.ops₁g R) Gd = false)
    (h : Tower.integratePrim En₁ Ed₁ Iη₁ Gn Gd = true) :
    HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ (Gn, Gd))) := by
  obtain ⟨hid, hsqc, hcopc, hlen⟩ := Tower.hermite_valG_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 Gn Gd hGd
  rw [hid, map_add, ← deriv_algebraMap, hasElementaryIntegral_deriv_add_iff]
  simp only [Tower.integratePrim, Bool.and_eq_true] at h
  obtain ⟨hres, hsome⟩ := h
  set q := (GPoly.divMod (Tower.ops₁g R)
    (GPoly.hermite (Tower.ops₁g R) [(En₁, Ed₁)] Gn Gd).b
    (GPoly.hermite (Tower.ops₁g R) [(En₁, Ed₁)] Gn Gd).s).1 with hq
  have hpoly : HasElementaryIntegral (algebraMap F₀ K (Tower.valP x₀ t₁ q)) := by
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
    have hRK : ∀ r : R, (algebraMap R K r)′ = 0 := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R F₀ K, deriv_algebraMap, hR, map_zero]
    let _ : Differential R := ⟨0⟩
    have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
    have hDAR : DifferentialAlgebra R K := ⟨fun r ↦ by rw [hRK, h0, map_zero]⟩
    have haevx : ∀ P : R[X], aeval (algebraMap F₀ K x₀) P = algebraMap F₀ K (aeval x₀ P) :=
      fun P ↦ aeval_algebraMap_apply K x₀ P
    have := hasElementaryIntegral_primPoly h0 (algebraMap F₀ K x₀) (algebraMap F₀ K t₁)
      (by rw [deriv_algebraMap, hx₀, map_one]) En₁ Ed₁
      (by rw [deriv_algebraMap, ht₁, map_div₀, haevx, haevx]) Iη₁ hcη₁ q.length
      (Tower.polyA q) (Tower.polyD q) (fun j _ ↦ Tower.normFrac_den_ne_zero _) hL
    rw [valP_eq_sum_poly]
    simpa only [map_sum, map_mul, map_pow, map_div₀, haevx] using this
  rw [map_add]
  exact hpoly.add_in (hasElementaryIntegralIn_prim2BaseResidue (K := K) hR x₀ t₁ hx₀ ht₁ hcη₁
    hη₁0 _ _ hsqc hcopc hlen hres)

end CPoly
