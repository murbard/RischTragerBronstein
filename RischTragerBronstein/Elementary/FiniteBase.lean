import RischTragerBronstein.Elementary.Trans
import RischTragerBronstein.Elementary.Algebraic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Elementary integrability is invariant under finite extensions of the base

For a finite extension `E' / E` of differential fields of characteristic zero and `h ∈ E`:

`hasElementaryIntegral_finite_iff`: `h` has an elementary integral over `E'` iff it has one over
`E`.

`←` is `HasElementaryIntegral.of_extension` (finite extensions are elementary). For `→`, an
elementary extension `L ∋ g` (`g′ = h`) of `E` is enlarged to the splitting field `L'` over `L` of the
minimal polynomial of a primitive element of `E'`; `E'` embeds into `L'` (compatibly with the
derivations: `algHom_deriv'`), and the tower of `L' / E` is also a tower over `E'`
(`IsElementaryTower.baseChange`).

This lets a decision procedure pass to a convenient finite cover of the curve.
-/

open IntermediateField Polynomial

namespace Differential

universe u

section BaseChange

variable {F F' L : Type*} [Field F] [Field F'] [Field L] [Differential L]
variable [Algebra F F'] [Algebra F L] [Algebra F' L] [IsScalarTower F F' L]

/-- An elementary tower over `F` generates an elementary tower over `F' ⊇ F`. -/
lemma IsElementaryTower.baseChange {M : IntermediateField F L} (hM : IsElementaryTower M) :
    IsElementaryTower (IntermediateField.adjoin F' (M : Set L)) := by
  induction hM with
  | base =>
    have : IntermediateField.adjoin F' ((⊥ : IntermediateField F L) : Set L) = ⊥ := by
      refine le_antisymm (adjoin_le_iff.mpr fun x hx ↦ ?_) bot_le
      obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
      rw [IsScalarTower.algebraMap_apply F F' L]
      exact IntermediateField.algebraMap_mem _ _
    rw [this]
    exact .base
  | adjoin M t _ ht ih =>
    have hsup : IntermediateField.adjoin F' ((M ⊔ F⟮t⟯ : IntermediateField F L) : Set L) =
        IntermediateField.adjoin F' (M : Set L) ⊔ F'⟮t⟯ := by
      apply le_antisymm
      · rw [adjoin_le_iff]
        have h1 : M ≤ (IntermediateField.adjoin F' (M : Set L) ⊔ F'⟮t⟯).restrictScalars F := fun x hx ↦
          (le_sup_left : IntermediateField.adjoin F' (M : Set L) ≤ _) (subset_adjoin F' _ hx)
        have h2 : F⟮t⟯ ≤ (IntermediateField.adjoin F' (M : Set L) ⊔ F'⟮t⟯).restrictScalars F := by
          rw [adjoin_simple_le_iff]
          exact (le_sup_right : F'⟮t⟯ ≤ _) (mem_adjoin_simple_self F' t)
        exact fun x hx ↦ (sup_le h1 h2) hx
      · refine sup_le (adjoin.mono _ _ _ fun x hx ↦ (le_sup_left : M ≤ M ⊔ F⟮t⟯) hx) ?_
        rw [adjoin_simple_le_iff]
        exact subset_adjoin F' _ ((le_sup_right : F⟮t⟯ ≤ M ⊔ F⟮t⟯) (mem_adjoin_simple_self F t))
    rw [hsup]
    refine .adjoin _ _ ih ?_
    have hmem : ∀ a ∈ M, a ∈ IntermediateField.adjoin F' (M : Set L) := fun a ha ↦ subset_adjoin F' _ ha
    rcases ht with ⟨p, hp0, hp⟩ | ⟨a, ha, ha0, hta⟩ | ⟨ht0, a, ha, hta⟩
    · left
      let e : M →+* IntermediateField.adjoin F' (M : Set L) :=
        { toFun := fun x ↦ ⟨x, hmem x x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      have he : Function.Injective e := fun x y hxy ↦ Subtype.ext (congrArg Subtype.val hxy :)
      refine ⟨p.map e, (Polynomial.map_ne_zero_iff he).mpr hp0, ?_⟩
      rw [aeval_def, eval₂_map]
      exact hp
    · exact Or.inr (Or.inl ⟨a, hmem a ha, ha0, hta⟩)
    · exact Or.inr (Or.inr ⟨ht0, a, hmem a ha, hta⟩)

/-- An elementary extension of `F` is an elementary extension of every intermediate `F'`. -/
theorem IsElementaryExtension.baseChange (h : IsElementaryExtension F L) :
    IsElementaryExtension F' L := by
  have := IsElementaryTower.baseChange (F' := F') h
  unfold IsElementaryExtension
  simpa [adjoin_univ] using this

end BaseChange

variable {E E' : Type u} [Field E] [Field E'] [Differential E] [Differential E'] [Algebra E E']
variable [DifferentialAlgebra E E'] [FiniteDimensional E E'] [CharZero E]

/-- **Elementary integrals persist in finite extensions of the base.** -/
theorem HasElementaryIntegral.finiteBase {h : E} (hh : HasElementaryIntegral h) :
    HasElementaryIntegral (algebraMap E E' h) := by
  obtain ⟨L, iL, DL, iA, iDA, hL, g, hg⟩ := hh
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E E'
  have hint : IsIntegral E α := Algebra.IsIntegral.isIntegral α
  set p := minpoly E α with hp
  set q : L[X] := p.map (algebraMap E L) with hq
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  letI : Differential (SplittingField q) := differentialFiniteDimensional L (SplittingField q)
  haveI : DifferentialAlgebra L (SplittingField q) := differentialAlgebraFiniteDimensional
  have hdeg : q.degree ≠ 0 := by
    rw [hq, degree_map]
    exact (minpoly.degree_pos hint).ne'
  obtain ⟨r, hr⟩ := (SplittingField.splits q).exists_eval_eq_zero
    (by rw [degree_map]; exact hdeg)
  have hmap : q.map (algebraMap L (SplittingField q)) = p.map (algebraMap E (SplittingField q)) := by
    rw [hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hroot : r ∈ p.aroots (SplittingField q) := by
    rw [mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, ← hmap]
    exact hr
  let φ0 : E⟮α⟯ →ₐ[E] SplittingField q := (algHomAdjoinIntegralEquiv E hint).symm ⟨r, hroot⟩
  let ψ : E' ≃ₐ[E] E⟮α⟯ := topEquiv.symm.trans (equivOfEq hα).symm
  let φ : E' →ₐ[E] SplittingField q := φ0.comp ψ.toAlgHom
  letI : Algebra E' (SplittingField q) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower E E' (SplittingField q) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  haveI hDAE : DifferentialAlgebra E (SplittingField q) :=
    ⟨fun a ↦ by
      rw [IsScalarTower.algebraMap_apply E L (SplittingField q), deriv_algebraMap,
        deriv_algebraMap, ← IsScalarTower.algebraMap_apply]⟩
  have hDA : DifferentialAlgebra E' (SplittingField q) :=
    ⟨fun a ↦ (algHom_deriv' φ φ.injective a).symm⟩
  have hLL : IsElementaryExtension L (SplittingField q) := isElementaryExtension_of_finiteDimensional
  have hEL : IsElementaryExtension E (SplittingField q) := hL.trans hLL
  refine ⟨SplittingField q, inferInstance, inferInstance, inferInstance, hDA,
    IsElementaryExtension.baseChange (F := E) hEL, algebraMap L _ g, ?_⟩
  rw [deriv_algebraMap, hg, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply E E' (SplittingField q)]

/-- **Invariance under finite extensions of the base**: `h ∈ E` has an elementary integral over a
finite extension `E'` of `E` iff it has one over `E`. -/
theorem hasElementaryIntegral_finite_iff (h : E) :
    HasElementaryIntegral (algebraMap E E' h) ↔ HasElementaryIntegral h :=
  ⟨HasElementaryIntegral.of_extension isElementaryExtension_of_finiteDimensional,
    HasElementaryIntegral.finiteBase⟩

end Differential
