import RischTragerBronstein.Elementary.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Transitivity of elementary extensions

If `K / F` and `L / K` are elementary extensions then so is `L / F`. Consequently, to show that
`f ∈ F` has an elementary integral it suffices to find one over some elementary extension of `F`
(`HasElementaryIntegral.of_extension`). Every multi-step construction of an elementary
antiderivative goes through this file.

The proof transports the tower of `K / F` into `L` along `K → L`, and then continues with the
tower of `L / K`, viewed over `F` by restriction of scalars.
-/

open IntermediateField

namespace Differential

universe u

variable {F : Type u} {K L : Type*} [Field F] [Field K] [Field L]
variable [Differential F] [Differential K] [Differential L]
variable [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
variable [DifferentialAlgebra K L]

omit [Differential F] in
/-- The image in `L` of an elementary tower of `K / F` is an elementary tower of `L / F`. -/
lemma IsElementaryTower.map {E : IntermediateField F K} (hE : IsElementaryTower E) :
    IsElementaryTower (E.map (IsScalarTower.toAlgHom F K L)) := by
  induction hE with
  | base => rw [IntermediateField.map_bot]; exact .base
  | adjoin E t _ ht ih =>
    rw [IntermediateField.map_sup, IntermediateField.adjoin_map, Set.image_singleton]
    refine .adjoin _ _ ih ?_
    have hmem : ∀ a ∈ E, algebraMap K L a ∈ E.map (IsScalarTower.toAlgHom F K L) :=
      fun a ha ↦ ⟨a, ha, rfl⟩
    rcases ht with ht | ⟨a, ha, ha0, hta⟩ | ⟨ht0, a, ha, hta⟩
    · -- algebraic
      left
      obtain ⟨p, hp0, hp⟩ := ht
      let e : E →+* E.map (IsScalarTower.toAlgHom F K L) :=
        (E.equivMap (IsScalarTower.toAlgHom F K L)).toRingEquiv.toRingHom
      have he : Function.Injective e := (E.equivMap (IsScalarTower.toAlgHom F K L)).injective
      refine ⟨p.map e, (Polynomial.map_ne_zero_iff he).mpr hp0, ?_⟩
      have h2 : Polynomial.aeval (algebraMap K L t) (p.map e) =
          algebraMap K L (Polynomial.aeval t p) := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def, Polynomial.hom_eval₂]
        rfl
      change Polynomial.aeval (algebraMap K L t) (p.map e) = 0
      rw [h2, hp, map_zero]
    · -- logarithm
      right; left
      refine ⟨algebraMap K L a, hmem a ha, by simpa using ha0, ?_⟩
      change (algebraMap K L t)′ = _
      rw [deriv_algebraMap, hta, logDeriv_algebraMap]
    · -- exponential
      right; right
      refine ⟨by change algebraMap K L t ≠ 0; simpa using ht0, algebraMap K L a, hmem a ha, ?_⟩
      change logDeriv (algebraMap K L t) = _
      rw [logDeriv_algebraMap, hta, deriv_algebraMap]

omit [Differential F] in
/-- An elementary tower of `L / K` on top of an elementary `K / F` is an elementary tower of
`L / F`. -/
lemma IsElementaryTower.restrictScalars (hK : IsElementaryExtension F K)
    {E : IntermediateField K L} (hE : IsElementaryTower E) :
    IsElementaryTower (E.restrictScalars F) := by
  induction hE with
  | base =>
    have : (⊥ : IntermediateField K L).restrictScalars F =
        (⊤ : IntermediateField F K).map (IsScalarTower.toAlgHom F K L) := by
      ext x
      simp only [mem_restrictScalars, IntermediateField.mem_bot, IntermediateField.mem_map,
        IntermediateField.mem_top, true_and]
      rfl
    rw [this]
    exact IsElementaryTower.map hK
  | adjoin E t _ ht ih =>
    have hsup : (E ⊔ K⟮t⟯).restrictScalars F = E.restrictScalars F ⊔ F⟮t⟯ := by
      apply le_antisymm
      · -- the right-hand side, as an intermediate field of `L / K`
        let N : IntermediateField K L :=
          { (E.restrictScalars F ⊔ F⟮t⟯).toSubfield with
            algebraMap_mem' := fun k ↦
              (le_sup_left : E.restrictScalars F ≤ E.restrictScalars F ⊔ F⟮t⟯)
                (E.algebraMap_mem k) }
        have h1 : E ≤ N := fun x hx ↦
          (le_sup_left : E.restrictScalars F ≤ E.restrictScalars F ⊔ F⟮t⟯) hx
        have h2 : K⟮t⟯ ≤ N := by
          rw [adjoin_le_iff, Set.singleton_subset_iff]
          exact (le_sup_right : F⟮t⟯ ≤ E.restrictScalars F ⊔ F⟮t⟯) (mem_adjoin_simple_self F t)
        exact fun x hx ↦ (sup_le h1 h2) hx
      · refine sup_le (fun x hx ↦ (le_sup_left : E ≤ E ⊔ K⟮t⟯) hx) ?_
        rw [adjoin_le_iff, Set.singleton_subset_iff]
        exact (le_sup_right : K⟮t⟯ ≤ E ⊔ K⟮t⟯) (mem_adjoin_simple_self K t)
    rw [hsup]
    refine .adjoin _ _ ih ?_
    rcases ht with ht | ⟨a, ha, ha0, hta⟩ | ⟨ht0, a, ha, hta⟩
    · exact Or.inl ht
    · exact Or.inr (Or.inl ⟨a, ha, ha0, hta⟩)
    · exact Or.inr (Or.inr ⟨ht0, a, ha, hta⟩)

omit [Differential F] in
/-- **Transitivity of elementary extensions.** -/
theorem IsElementaryExtension.trans (hK : IsElementaryExtension F K)
    (hL : IsElementaryExtension K L) : IsElementaryExtension F L := by
  have := IsElementaryTower.restrictScalars (F := F) hK hL
  rwa [restrictScalars_top] at this

end Differential

namespace Differential

universe u

variable {F : Type u} [Field F] [Differential F]

/-- To integrate `f ∈ F` in elementary terms, one may first pass to an elementary extension
`K` of `F`. -/
theorem HasElementaryIntegral.of_extension {K : Type u} [Field K] [Differential K] [Algebra F K]
    [DifferentialAlgebra F K] (hK : IsElementaryExtension F K) {f : F}
    (hf : HasElementaryIntegral (algebraMap F K f)) : HasElementaryIntegral f := by
  obtain ⟨L, _, _, _, _, hL, g, hg⟩ := hf
  let _ : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra F L :=
    ⟨fun a ↦ by
      change (algebraMap K L (algebraMap F K a))′ = algebraMap K L (algebraMap F K a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, hDA, hK.trans hL, g, hg⟩


end Differential
