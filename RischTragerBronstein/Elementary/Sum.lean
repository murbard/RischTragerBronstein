import RischTragerBronstein.Elementary.Trans

/-!
# Sums of elementary-integrable elements

Two elementary extensions of `F` need not visibly have a common extension, so
`HasElementaryIntegral f₁ → HasElementaryIntegral f₂ → HasElementaryIntegral (f₁ + f₂)` is not
immediate. It is when the second integrability statement is *stable under extension* — which is
how all positive results of this development are proved (`…_in` forms).
-/

namespace Differential

universe u

variable {F : Type u} [Field F] [Differential F]

/-- `f₂` has an elementary integral over every elementary extension of `F`. -/
def HasElementaryIntegralIn (f₂ : F) : Prop :=
  ∀ (E : Type u) [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E],
    IsElementaryExtension F E → HasElementaryIntegral (algebraMap F E f₂)

theorem HasElementaryIntegralIn.hasElementaryIntegral {f : F} (h : HasElementaryIntegralIn f) :
    HasElementaryIntegral f := by
  have hFF : IsElementaryExtension F F := by
    have h' : (⊥ : IntermediateField F F) = ⊤ :=
      eq_top_iff.mpr fun x _ ↦ IntermediateField.mem_bot.mpr ⟨x, rfl⟩
    unfold IsElementaryExtension
    rw [← h']
    exact IsElementaryTower.base
  exact h F hFF

theorem HasElementaryIntegral.add_in {f₁ f₂ : F} (h₁ : HasElementaryIntegral f₁)
    (h₂ : HasElementaryIntegralIn f₂) : HasElementaryIntegral (f₁ + f₂) := by
  obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h₁
  obtain ⟨E', _, _, _, _, hE', g', hg'⟩ := h₂ E hE
  let _ : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra F E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap F E a))′ = algebraMap E E' (algebraMap F E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  refine ⟨E', inferInstance, inferInstance, inferInstance, hDA, hE.trans hE',
    algebraMap E E' g + g', ?_⟩
  rw [map_add, deriv_algebraMap, hg, hg', map_add]
  rfl

theorem HasElementaryIntegral.sub_in {f₁ f₂ : F} (h₁ : HasElementaryIntegral f₁)
    (h₂ : HasElementaryIntegralIn f₂) : HasElementaryIntegral (f₁ - f₂) := by
  obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h₁
  obtain ⟨E', _, _, _, _, hE', g', hg'⟩ := h₂ E hE
  let _ : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra F E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap F E a))′ = algebraMap E E' (algebraMap F E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  refine ⟨E', inferInstance, inferInstance, inferInstance, hDA, hE.trans hE',
    algebraMap E E' g - g', ?_⟩
  rw [map_sub, deriv_algebraMap, hg, hg', map_sub]
  rfl

/-- Derivatives are integrable over every extension. -/
theorem hasElementaryIntegralIn_deriv (g : F) : HasElementaryIntegralIn g′ :=
  fun E _ _ _ _ _ ↦ by
    rw [← deriv_algebraMap]
    exact hasElementaryIntegral_of_deriv _

/-- Negation preserves elementary integrability. -/
theorem HasElementaryIntegral.neg {f : F} (h : HasElementaryIntegral f) :
    HasElementaryIntegral (-f) := by
  obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hE, -g, by
    rw [map_neg, hg, map_neg]⟩

end Differential
