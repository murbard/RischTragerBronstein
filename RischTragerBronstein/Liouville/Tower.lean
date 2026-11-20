import RischTragerBronstein.Liouville.Steps

/-!
# Liouville's theorem for elementary extensions (Rosenlicht's form)

**Theorem** (`liouville_of_isElementaryExtension`). Let `E / F` be an elementary extension of
differential fields of characteristic zero such that every constant of `E` lies in `F`. If `α ∈ F`
has an antiderivative in `E`, then

  `α = ∑ cᵢ uᵢ′ / uᵢ + v′`   with `uᵢ, v ∈ F` and constants `cᵢ ∈ F`.

The proof descends along the tower, one elementary step at a time (`LiouvilleIn.descend_log`,
`descend_exp`, `descend_alg`). At each step the current field `M` of the tower — a differential
subfield by `IsElementaryTower.derivClosed` — plays the role of the base field.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

local notation "ψ" => algebraMap F E

/-- One step of the descent, in the tower: from data in `M(t)` to data in `M`. -/
theorem LiouvilleIn.descend_step (hconst : ∀ x : E, x′ = 0 → x ∈ Set.range ψ)
    {M : IntermediateField F E} (hcl : DerivClosed M) {t : E} (ht : IsElementaryOver M t) {α : F}
    (h : LiouvilleIn (M ⊔ F⟮t⟯) (ψ α)) : LiouvilleIn M (ψ α) := by
  let _ : Differential M := differentialOfDerivClosed hcl
  have hDA : DifferentialAlgebra M E := differentialAlgebra_of_derivClosed hcl
  have hchar : CharZero M := charZero_of_injective_algebraMap (algebraMap F M).injective
  have hconst₁ : ∀ x : E, x′ = 0 → x ∈ Set.range (algebraMap M E) := fun x hx ↦ by
    obtain ⟨a, rfl⟩ := hconst x hx
    exact ⟨algebraMap F M a, rfl⟩
  -- the same data, over the base field `M`
  have hmem : ∀ x : E, x ∈ M ⊔ F⟮t⟯ ↔ x ∈ (M⟮t⟯ : IntermediateField M E) := fun x ↦ by
    rw [← restrictScalars_adjoin_eq_sup, mem_restrictScalars]
  have h₁ : LiouvilleIn (F := M) M⟮t⟯ (algebraMap M E (algebraMap F M α)) := by
    obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := h
    exact ⟨ι, s, c, u, v, fun i hi ↦ ⟨(hdata i hi).1, (hmem _).mp (hdata i hi).2.1,
      (hdata i hi).2.2⟩, (hmem _).mp hv, heq⟩
  have hback : LiouvilleIn (F := M) (⊥ : IntermediateField M E)
      (algebraMap M E (algebraMap F M α)) → LiouvilleIn M (ψ α) := by
    rintro ⟨ι, s, c, u, v, hdata, hv, heq⟩
    have hbot : ∀ x : E, x ∈ (⊥ : IntermediateField M E) → x ∈ M := fun x hx ↦ by
      obtain ⟨m, rfl⟩ := IntermediateField.mem_bot.mp hx
      exact m.2
    exact ⟨ι, s, c, u, v, fun i hi ↦ ⟨(hdata i hi).1, hbot _ (hdata i hi).2.1, (hdata i hi).2.2⟩,
      hbot _ hv, heq⟩
  apply hback
  by_cases halg : IsAlgebraic M t
  · exact LiouvilleIn.descend_alg hconst₁ halg h₁
  · rcases ht with ht | ⟨a, ha, ha0, hta⟩ | ⟨ht0, a, ha, hta⟩
    · exact absurd ht halg
    · refine LiouvilleIn.descend_log hconst₁ halg (b := ⟨a, ha⟩) ?_
        (fun h0 ↦ ha0 (congrArg Subtype.val h0)) h₁
      rw [hta]
      simp only [logDeriv]
      rfl
    · refine LiouvilleIn.descend_exp hconst₁ halg (b := ⟨a, ha⟩) ?_ h₁
      rw [logDeriv, div_eq_iff ht0] at hta
      rw [hta]
      rfl

/-- Descent along a whole elementary tower. -/
theorem LiouvilleIn.of_tower (hconst : ∀ x : E, x′ = 0 → x ∈ Set.range ψ)
    {M : IntermediateField F E} (hM : IsElementaryTower M) {α : F}
    (h : LiouvilleIn M (ψ α)) : LiouvilleIn (⊥ : IntermediateField F E) (ψ α) := by
  induction hM with
  | base => exact h
  | adjoin M t hM ht ih => exact ih (LiouvilleIn.descend_step hconst hM.derivClosed ht h)

/-- **Liouville's theorem** for an elementary extension with no new constants. -/
theorem liouville_of_isElementaryExtension (hconst : ∀ x : E, x′ = 0 → x ∈ Set.range ψ)
    (hE : IsElementaryExtension F E) (α : F) (g : E) (hg : g′ = ψ α) :
    ∃ (ι : Type) (s : Finset ι) (c u : ι → F) (v : F),
      (∀ i ∈ s, (c i)′ = 0 ∧ u i ≠ 0) ∧ α = ∑ i ∈ s, c i * logDeriv (u i) + v′ := by
  have htop : LiouvilleIn (⊤ : IntermediateField F E) (ψ α) :=
    ⟨Empty, ∅, fun _ ↦ 0, fun _ ↦ 1, g, by simp, IntermediateField.mem_top, by simp [hg]⟩
  obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := LiouvilleIn.of_tower hconst hE htop
  choose! γ hγ using fun i (hi : i ∈ s) ↦ hconst (c i) (hdata i hi).1
  choose! u₀ hu₀ using fun i (hi : i ∈ s) ↦ IntermediateField.mem_bot.mp (hdata i hi).2.1
  obtain ⟨v₀, rfl⟩ := IntermediateField.mem_bot.mp hv
  have hinj : Function.Injective ψ := (algebraMap F E).injective
  refine ⟨ι, s, γ, u₀, v₀, fun i hi ↦ ⟨?_, ?_⟩, ?_⟩
  · apply hinj
    rw [← deriv_algebraMap, hγ i hi, (hdata i hi).1, map_zero]
  · intro h0
    exact (hdata i hi).2.2 (by rw [← hu₀ i hi, h0, map_zero])
  · apply hinj
    rw [heq, map_add, map_sum, deriv_algebraMap]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [map_mul, ← logDeriv_algebraMap, hγ i hi, hu₀ i hi]

end Differential
