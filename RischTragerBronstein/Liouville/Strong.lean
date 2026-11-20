import RischTragerBronstein.Liouville.Tower

/-!
# The strong Liouville theorem: no hypothesis on constants

Let `E / F` be an elementary extension of differential fields of characteristic zero; `E` may have
more constants than `F`. Let `constField F E = F(Const E) ⊆ E` be the subfield generated over `F`
by the constants of `E`.

**Theorem** (`liouville_strong`). If `α ∈ F` has an antiderivative in `E`, then
`α = ∑ cᵢ uᵢ′ / uᵢ + v′` with `uᵢ, v ∈ F(Const E)` and `cᵢ ∈ Const E`.

Proof: `E` is also an elementary extension of `F(Const E)` (`isElementaryExtension_constField`) —
the same tower, with every field enlarged by the constants — and over that base there are no new
constants, so `liouville_of_isElementaryExtension` applies.

This removes the "same constants" assumption from the theory: a non-elementarity proof now only has
to exclude Liouville forms over the constant-field extension `F(Const E)`.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

variable (F E) in
/-- `F(Const E)`: the subfield of `E` generated over `F` by the constants of `E`. -/
def constField : IntermediateField F E := IntermediateField.adjoin F {c : E | c′ = 0}

lemma mem_constField_of_deriv_eq_zero {c : E} (hc : c′ = 0) : c ∈ Differential.constField F E :=
  subset_adjoin F _ hc

/-- Adjoining a set whose elements have derivatives in the result preserves closure under the
derivation. -/
lemma DerivClosed.adjoin_set {M : IntermediateField F E} (hM : DerivClosed M) (S : Set E)
    (hS : ∀ x ∈ S, x′ ∈ M ⊔ IntermediateField.adjoin F S) : DerivClosed (M ⊔ IntermediateField.adjoin F S) := by
  set N := M ⊔ IntermediateField.adjoin F S with hN
  let T : IntermediateField F E :=
    { carrier := {x | x ∈ N ∧ x′ ∈ N}
      mul_mem' := fun {x y} hx hy ↦ ⟨mul_mem hx.1 hy.1, by
        rw [Derivation.leibniz]
        exact add_mem (mul_mem hx.1 hy.2) (mul_mem hy.1 hx.2)⟩
      one_mem' := ⟨one_mem _, by simp⟩
      add_mem' := fun {x y} hx hy ↦ ⟨add_mem hx.1 hy.1, by
        rw [map_add]; exact add_mem hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      algebraMap_mem' := fun a ↦ ⟨N.algebraMap_mem a, by
        rw [deriv_algebraMap]; exact N.algebraMap_mem _⟩
      inv_mem' := fun x hx ↦ ⟨inv_mem hx.1, by
        rw [Derivation.leibniz_inv]
        exact mul_mem (neg_mem (pow_mem (inv_mem hx.1) 2)) hx.2⟩ }
  have hMT : M ≤ T := fun x hx ↦ ⟨(le_sup_left : M ≤ N) hx, (le_sup_left : M ≤ N) (hM x hx)⟩
  have hST : IntermediateField.adjoin F S ≤ T := adjoin_le_iff.mpr fun x hx ↦
    ⟨(le_sup_right : IntermediateField.adjoin F S ≤ N) (subset_adjoin F S hx), hS x hx⟩
  exact fun x hx ↦ ((sup_le hMT hST) hx).2

lemma derivClosed_constField : DerivClosed (Differential.constField F E) := by
  have h := (derivClosed_bot (F := F) (K := E)).adjoin_set {c : E | c′ = 0} fun x hx ↦ by
    rw [Set.mem_ofPred_eq] at hx
    rw [hx]; exact zero_mem _
  rwa [bot_sup_eq] at h

/-- The tower of `E / F`, enlarged by the constants, is an elementary tower of `E / F(Const E)`. -/
lemma IsElementaryTower.extendConst {M : IntermediateField F E} (hM : IsElementaryTower M) :
    letI := differentialOfDerivClosed (derivClosed_constField (F := F) (E := E))
    IsElementaryTower (F := Differential.constField F E) (IntermediateField.adjoin (Differential.constField F E) (M : Set E)) := by
  let _ := differentialOfDerivClosed (derivClosed_constField (F := F) (E := E))
  induction hM with
  | base =>
    have : IntermediateField.adjoin (Differential.constField F E) ((⊥ : IntermediateField F E) : Set E) = ⊥ := by
      rw [eq_bot_iff, adjoin_le_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
      exact IntermediateField.mem_bot.mpr ⟨algebraMap F (Differential.constField F E) a, rfl⟩
    rw [this]
    exact IsElementaryTower.base
  | adjoin M t _ ht ih =>
    set K' := Differential.constField F E
    have hle : ∀ x ∈ M, x ∈ IntermediateField.adjoin K' (M : Set E) := fun x hx ↦ subset_adjoin K' _ hx
    have hsup : IntermediateField.adjoin K' ((M ⊔ F⟮t⟯ : IntermediateField F E) : Set E) =
        IntermediateField.adjoin K' (M : Set E) ⊔ K'⟮t⟯ := by
      apply le_antisymm
      · rw [adjoin_le_iff]
        -- `M ⊔ F⟮t⟯` is contained in the `F`-field underlying the right-hand side
        have : M ⊔ F⟮t⟯ ≤ (IntermediateField.adjoin K' (M : Set E) ⊔ K'⟮t⟯).restrictScalars F := by
          refine sup_le (fun x hx ↦ ?_) ?_
          · exact (le_sup_left : IntermediateField.adjoin K' (M : Set E) ≤ _) (hle x hx)
          · rw [adjoin_le_iff, Set.singleton_subset_iff]
            exact (le_sup_right : K'⟮t⟯ ≤ IntermediateField.adjoin K' (M : Set E) ⊔ K'⟮t⟯)
              (mem_adjoin_simple_self K' t)
        exact fun x hx ↦ this hx
      · refine sup_le (adjoin.mono K' _ _ fun x hx ↦ (le_sup_left : M ≤ M ⊔ F⟮t⟯) hx) ?_
        rw [adjoin_le_iff, Set.singleton_subset_iff]
        exact subset_adjoin K' _ ((le_sup_right : F⟮t⟯ ≤ M ⊔ F⟮t⟯) (mem_adjoin_simple_self F t))
    rw [hsup]
    refine IsElementaryTower.adjoin _ t ih ?_
    rcases ht with ht | ⟨a, ha, ha0, hta⟩ | ⟨ht0, a, ha, hta⟩
    · -- algebraic over `M`, hence over the larger field
      left
      obtain ⟨p, hp0, hp⟩ := ht
      let ι : M →+* IntermediateField.adjoin K' (M : Set E) :=
        { toFun := fun x ↦ ⟨x.1, hle x.1 x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      have hι : Function.Injective ι := fun x y h ↦
        Subtype.ext (congrArg (fun z : IntermediateField.adjoin K' (M : Set E) ↦ (z : E)) h)
      refine ⟨p.map ι, (Polynomial.map_ne_zero_iff hι).mpr hp0, ?_⟩
      rw [aeval_def, eval₂_map]
      rw [aeval_def] at hp
      exact hp
    · exact Or.inr (Or.inl ⟨a, hle a ha, ha0, hta⟩)
    · exact Or.inr (Or.inr ⟨ht0, a, hle a ha, hta⟩)

/-- `E` is elementary over `F(Const E)`. -/
theorem isElementaryExtension_constField (hE : IsElementaryExtension F E) :
    letI := differentialOfDerivClosed (derivClosed_constField (F := F) (E := E))
    IsElementaryExtension (Differential.constField F E) E := by
  let _ := differentialOfDerivClosed (derivClosed_constField (F := F) (E := E))
  have h := IsElementaryTower.extendConst hE
  have htop : IntermediateField.adjoin (Differential.constField F E) ((⊤ : IntermediateField F E) : Set E) = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ subset_adjoin _ _ (by simp)
  unfold IsElementaryExtension
  rwa [htop] at h

/-- **The strong Liouville theorem.** No hypothesis on the constants of `E`. -/
theorem liouville_strong (hE : IsElementaryExtension F E) (α : F) (g : E)
    (hg : g′ = algebraMap F E α) : LiouvilleIn (Differential.constField F E) (algebraMap F E α) := by
  let _ := differentialOfDerivClosed (derivClosed_constField (F := F) (E := E))
  have hDA : DifferentialAlgebra (Differential.constField F E) E :=
    differentialAlgebra_of_derivClosed derivClosed_constField
  have hchar : CharZero (Differential.constField F E) :=
    charZero_of_injective_algebraMap (algebraMap F (Differential.constField F E)).injective
  have hconst : ∀ x : E, x′ = 0 → x ∈ Set.range (algebraMap (Differential.constField F E) E) :=
    fun x hx ↦ ⟨⟨x, mem_constField_of_deriv_eq_zero hx⟩, rfl⟩
  obtain ⟨ι, s, c, u, v, hdata, heq⟩ := liouville_of_isElementaryExtension hconst
    (isElementaryExtension_constField hE) (algebraMap F (Differential.constField F E) α) g hg
  refine ⟨ι, s, fun i ↦ (c i : E), fun i ↦ (u i : E), (v : E), fun i hi ↦ ⟨?_, (u i).2, ?_⟩,
    v.2, ?_⟩
  · exact congrArg Subtype.val (hdata i hi).1
  · exact fun h0 ↦ (hdata i hi).2 (Subtype.ext h0)
  · have := congrArg Subtype.val heq
    rw [IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum] at this
    refine this.trans ?_
    congr 1

end Differential
