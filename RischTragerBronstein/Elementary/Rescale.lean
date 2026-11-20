import RischTragerBronstein.Elementary.Defs

/-!
# Rescaling the derivation

For a differential field `(F, ∂)` and `φ ∈ F`, `φ ≠ 0`, the derivation `φ∂` has the same elementary
extensions (logarithms, exponentials and algebraic elements are preserved), so

  `f` has an elementary integral for `∂`  ⟺  `φ f` has one for `φ∂`

(`hasElementaryIntegral_rescale_iff`). This is the change of variables `∫ f dx = ∫ f (dx/dt) dt`:
with `φ = 1/t′`, `t` becomes a variable with derivative `1`.
-/

open Differential IntermediateField

universe u

namespace Differential

/-- The rescaled differential structure `φ ∂`. -/
def rescale {K : Type*} [CommRing K] (D : Differential K) (φ : K) : Differential K :=
  ⟨φ • D.deriv⟩

lemma rescale_deriv {K : Type*} [CommRing K] (D : Differential K) (φ a : K) :
    (rescale D φ).deriv a = φ * D.deriv a := rfl

section Tower

variable {F : Type u} {K : Type*} [Field F] [Field K] [Algebra F K]

lemma isElementaryOver_rescale (DK : Differential K) (φ : K)
    (E : IntermediateField F K) (t : K)
    (h : @IsElementaryOver F K _ _ DK _ E t) :
    @IsElementaryOver F K _ _ (rescale DK φ) _ E t := by
  rcases h with h | ⟨a, ha, ha0, h⟩ | ⟨ht, a, ha, h⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨a, ha, ha0, ?_⟩)
    change φ * DK.deriv t = (φ * DK.deriv a) / a
    change DK.deriv t = DK.deriv a / a at h
    rw [h, mul_div_assoc]
  · refine Or.inr (Or.inr ⟨ht, a, ha, ?_⟩)
    change (φ * DK.deriv t) / t = φ * DK.deriv a
    change DK.deriv t / t = DK.deriv a at h
    rw [mul_div_assoc, h]

lemma isElementaryTower_rescale (DK : Differential K) (φ : K)
    (E : IntermediateField F K) (h : @IsElementaryTower F K _ _ DK _ E) :
    @IsElementaryTower F K _ _ (rescale DK φ) _ E := by
  induction h with
  | base => exact @IsElementaryTower.base F K _ _ (rescale DK φ) _
  | adjoin E t _ ht ih =>
    exact @IsElementaryTower.adjoin F K _ _ (rescale DK φ) _ E t ih
      (isElementaryOver_rescale DK φ E t ht)

end Tower

/-- **Rescaling the derivation**: an elementary integral of `f` for `∂` gives one of `φ f` for
`φ∂`. -/
theorem hasElementaryIntegral_rescale {F : Type u} [Field F] (DF : Differential F) (φ f : F)
    (h : @HasElementaryIntegral F _ DF f) :
    @HasElementaryIntegral F _ (rescale DF φ) (φ * f) := by
  obtain ⟨K, _, DK, _, hDA, hE, g, hg⟩ := h
  let DK' := rescale DK (algebraMap F K φ)
  have hDA' : @DifferentialAlgebra F K _ _ _ (rescale DF φ) DK' :=
    @DifferentialAlgebra.mk F K _ _ _ (rescale DF φ) DK' (fun a ↦ by
      change algebraMap F K φ * DK.deriv (algebraMap F K a) = algebraMap F K (φ * DF.deriv a)
      rw [map_mul]
      congr 1
      exact hDA.deriv_algebraMap a)
  refine ⟨K, inferInstance, DK', inferInstance, hDA', ?_, g, ?_⟩
  · exact isElementaryTower_rescale DK (algebraMap F K φ) ⊤ hE
  · change algebraMap F K φ * DK.deriv g = algebraMap F K (φ * f)
    rw [map_mul]
    congr 1

lemma rescale_rescale {K : Type*} [CommRing K] (D : Differential K) (φ ψ : K) :
    rescale (rescale D φ) ψ = rescale D (ψ * φ) := by
  show (⟨ψ • (φ • D.deriv)⟩ : Differential K) = ⟨(ψ * φ) • D.deriv⟩
  rw [smul_smul]

lemma rescale_one {K : Type*} [CommRing K] (D : Differential K) : rescale D 1 = D := by
  unfold rescale
  cases D
  congr 1
  exact one_smul _ _

/-- **Invariance under rescaling**: `∫ f` is elementary for `∂` iff `∫ φ f` is for `φ∂`. -/
theorem hasElementaryIntegral_rescale_iff {F : Type u} [Field F] (DF : Differential F) (φ f : F)
    (hφ : φ ≠ 0) :
    @HasElementaryIntegral F _ (rescale DF φ) (φ * f) ↔ @HasElementaryIntegral F _ DF f := by
  refine ⟨fun h ↦ ?_, hasElementaryIntegral_rescale DF φ f⟩
  have := hasElementaryIntegral_rescale (rescale DF φ) φ⁻¹ (φ * f) h
  rwa [rescale_rescale, inv_mul_cancel₀ hφ, rescale_one, ← mul_assoc, inv_mul_cancel₀ hφ,
    one_mul] at this

end Differential
