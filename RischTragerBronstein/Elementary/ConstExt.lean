import RischTragerBronstein.Elementary.CommonExt

/-!
# Elementary integrability does not depend on the constants

* `isElementaryTower_adjoin_consts`: adjoining finitely many constants is an elementary tower
  (a constant is a logarithm of `1`).
* **`hasElementaryIntegral_of_liouvilleIn_constField`**: the converse of the strong Liouville
  theorem — a Liouville form `v′ + ∑ cᵢ uᵢ′/uᵢ` of `f ∈ F` with `v`, `uᵢ` in `F(Const K)`, for any
  differential field `K ⊇ F`, gives an elementary integral of `f` over `F`.
  **`hasElementaryIntegral_iff_liouvilleIn`**: `∫ f` is elementary over `F` iff such a form exists.
* **`hasElementaryIntegral_constGen_iff`**: if `E ⊇ F` is generated over `F` by constants, then
  `∫ f` is elementary over `E` iff it is over `F` — the field of constants may be enlarged or
  shrunk freely (e.g. `ℚ(x)` against `ℂ(x)`).
-/

open Polynomial IntermediateField

namespace Differential

universe u

section Tower

variable {F K : Type*} [Field F] [Field K] [Differential K] [Algebra F K]

/-- Adjoining finitely many constants gives an elementary tower. -/
lemma isElementaryTower_adjoin_consts (S : Finset K) (hS : ∀ t ∈ S, t′ = 0) :
    IsElementaryTower (adjoin F (S : Set K)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [adjoin_empty] using IsElementaryTower.base
  | insert t S _ ih =>
    have h : adjoin F ((insert t S : Finset K) : Set K) = adjoin F (S : Set K) ⊔ F⟮t⟯ := by
      rw [Finset.coe_insert, Set.insert_eq, adjoin_union, sup_comm]
    rw [h]
    refine .adjoin _ _ (ih fun x hx ↦ hS x (Finset.mem_insert_of_mem hx))
      (Or.inr (Or.inl ⟨1, one_mem _, one_ne_zero, ?_⟩))
    rw [hS t (Finset.mem_insert_self t S), logDeriv_one]

end Tower

variable {F : Type u} [Field F] [Differential F] [CharZero F]

/-- **The converse of the strong Liouville theorem**: a Liouville form of `f` over
`F(Const K)`, in any differential field `K ⊇ F`, gives an elementary integral of `f` over `F`. -/
theorem hasElementaryIntegral_of_liouvilleIn_constField {K : Type u} [Field K] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] (f : F)
    (h : LiouvilleIn (constField F K) (algebraMap F K f)) : HasElementaryIntegral f := by
  classical
  obtain ⟨K₀, _, _, _, _, l, hlc, hlgen, ι, sI, c, u, v, hcu, heq⟩ :=
    exists_const_gen_liouville f h
  have hE : IsElementaryExtension F K₀ := by
    unfold IsElementaryExtension
    rw [← hlgen]
    have := isElementaryTower_adjoin_consts (F := F) l.toFinset
      (fun t ht ↦ hlc t (List.mem_toFinset.mp ht))
    rwa [List.coe_toFinset] at this
  have hform := hasElementaryIntegral_of_liouville_form v (sI.toList.map fun i ↦ (c i, u i)) (by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact hcu i (Finset.mem_toList.mp hi))
  have hval : v′ + ((sI.toList.map fun i ↦ (c i, u i)).map fun p ↦ p.1 * logDeriv p.2).sum =
      algebraMap F K₀ f := by
    rw [heq, List.map_map, Finset.sum_map_toList, add_comm]
    rfl
  rw [hval] at hform
  exact HasElementaryIntegral.of_extension hE hform

/-- **Liouville's theorem, as an equivalence**: `∫ f` is elementary over `F` iff `f` has a
Liouville form over `F(Const K)` in some differential field `K ⊇ F`. -/
theorem hasElementaryIntegral_iff_liouvilleIn (f : F) :
    HasElementaryIntegral f ↔ ∃ (K : Type u) (_ : Field K) (_ : Differential K) (_ : Algebra F K)
      (_ : DifferentialAlgebra F K), LiouvilleIn (constField F K) (algebraMap F K f) :=
  ⟨fun ⟨K, i1, i2, i3, i4, hK, g, hg⟩ ↦ ⟨K, i1, i2, i3, i4, liouville_strong hK f g hg⟩,
    fun ⟨_, _, _, _, _, h⟩ ↦ hasElementaryIntegral_of_liouvilleIn_constField f h⟩

section ConstGen

variable {E : Type u} [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E]

/-- **Descent of the constants**: if `E` is generated over `F` by constants, an elementary
integral over `E` of some `f ∈ F` gives one over `F`. -/
theorem HasElementaryIntegral.of_constGen
    (hE : IntermediateField.adjoin F {c : E | c′ = 0} = ⊤) {f : F}
    (h : HasElementaryIntegral (algebraMap F E f)) : HasElementaryIntegral f := by
  classical
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨K, _, _, _, _, hK, g, hg⟩ := h
  obtain ⟨ι, sI, c, u, v, hdata, hv, heq⟩ := liouville_strong hK (algebraMap F E f) g hg
  letI : Algebra F K := ((algebraMap E K).comp (algebraMap F E)).toAlgebra
  haveI : IsScalarTower F E K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI hDA : DifferentialAlgebra F K :=
    ⟨fun a ↦ by
      change (algebraMap E K (algebraMap F E a))′ = algebraMap E K (algebraMap F E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  -- the image of `E` lies in `F(Const K)`
  have hEK : ∀ e : E, algebraMap E K e ∈ constField F K := by
    intro e
    have he : e ∈ IntermediateField.adjoin F {c : E | c′ = 0} := by rw [hE]; exact mem_top
    have hmap : (IntermediateField.adjoin F {c : E | c′ = 0}).map (IsScalarTower.toAlgHom F E K) ≤
        constField F K := by
      rw [adjoin_map]
      refine adjoin.mono F _ _ ?_
      rintro _ ⟨x, hx, rfl⟩
      change (algebraMap E K x)′ = 0
      rw [deriv_algebraMap, show x′ = 0 from hx, map_zero]
    exact hmap ((IntermediateField.mem_map _).mpr ⟨e, he, rfl⟩)
  -- hence `E(Const K) ⊆ F(Const K)`
  let N : IntermediateField E K :=
    { carrier := (constField F K : Set K)
      mul_mem' := fun hx hy ↦ mul_mem hx hy
      one_mem' := one_mem _
      add_mem' := fun hx hy ↦ add_mem hx hy
      zero_mem' := zero_mem _
      algebraMap_mem' := hEK
      inv_mem' := fun _ hx ↦ inv_mem hx }
  have hle : constField E K ≤ N := by
    unfold constField
    rw [adjoin_le_iff]
    intro x hx
    exact mem_constField_of_deriv_eq_zero (F := F) hx
  exact hasElementaryIntegral_of_liouvilleIn_constField f
    ⟨ι, sI, c, u, v, fun i hi ↦ ⟨(hdata i hi).1, hle (hdata i hi).2.1, (hdata i hi).2.2⟩, hle hv, heq⟩

/-- **Elementary integrability does not depend on the constants**: if `E` is generated over `F`
by constants, `∫ f` is elementary over `E` iff it is elementary over `F`. -/
theorem hasElementaryIntegral_constGen_iff
    (hE : IntermediateField.adjoin F {c : E | c′ = 0} = ⊤) (f : F) :
    HasElementaryIntegral (algebraMap F E f) ↔ HasElementaryIntegral f :=
  ⟨HasElementaryIntegral.of_constGen hE, fun h ↦ h.over_ext E⟩

end ConstGen

end Differential
