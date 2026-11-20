import RischTragerBronstein.Liouville.StepPrimitive
import RischTragerBronstein.Liouville.StepExponential
import Mathlib.FieldTheory.Differential.Liouville

/-!
# Descending a Liouville form through one elementary step

`LiouvilleIn M α`: the element `α ∈ E` has a Liouville form `α = ∑ cᵢ uᵢ′ / uᵢ + v′` whose data
`uᵢ, v` lie in the subfield `M` of `E`, with constants `cᵢ ∈ E`.

Assuming all constants of `E` lie in the base field `F`, a Liouville form for `α ∈ F` with data in
`F⟮t⟯` descends to one with data in `F` (that is, in `⊥`) whenever `t` is

* a logarithm over `F`, transcendental (`LiouvilleIn.descend_log`),
* an exponential over `F`, transcendental (`LiouvilleIn.descend_exp`),
* algebraic over `F` (`LiouvilleIn.descend_alg`, from Mathlib's `isLiouville_of_finiteDimensional`).
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial Finset

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- `α` has a Liouville form with data in `M`. -/
def LiouvilleIn (M : IntermediateField F E) (α : E) : Prop :=
  ∃ (ι : Type) (s : Finset ι) (c u : ι → E) (v : E),
    (∀ i ∈ s, (c i)′ = 0 ∧ u i ∈ M ∧ u i ≠ 0) ∧ v ∈ M ∧
      α = ∑ i ∈ s, c i * logDeriv (u i) + v′

variable (hconst : ∀ x : E, x′ = 0 → x ∈ Set.range (algebraMap F E))

local notation "ψ" => algebraMap F E

lemma logDeriv_algebraMap' (e : F) : logDeriv (ψ e) = ψ (logDeriv e) := logDeriv_algebraMap e

include hconst in
theorem LiouvilleIn.descend_log {t : E} (htr : Transcendental F t) {b : F} (ht : t′ = ψ (logDeriv b))
    (hb : b ≠ 0) {α : F} (h : LiouvilleIn F⟮t⟯ (ψ α)) : LiouvilleIn (⊥ : IntermediateField F E) (ψ α) := by
  classical
  obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := h
  choose! γ hγ using fun i (hi : i ∈ s) ↦ hconst (c i) (hdata i hi).1
  have heq' : ψ α = ∑ i ∈ s, ψ (γ i) * logDeriv (u i) + v′ := by
    rw [heq]; congr 1
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hγ i hi]
  obtain ⟨e, c₀, d, he, hc₀, hfin⟩ := liouville_step_primitive t htr (logDeriv b) ht
    (fun x _ hx ↦ hconst x hx) s γ u (fun i hi ↦ (hdata i hi).2) v hv α heq'
  refine ⟨Option ι, insertNone s, fun o ↦ o.elim (ψ c₀) c, fun o ↦ o.elim (ψ b) fun i ↦ ψ (e i),
    ψ d, ?_, (⊥ : IntermediateField F E).algebraMap_mem d, ?_⟩
  · rintro (_ | i) hi
    · exact ⟨by simp only [Option.elim]; rw [deriv_algebraMap, hc₀, map_zero],
        (⊥ : IntermediateField F E).algebraMap_mem b, by simpa using hb⟩
    · have hi' : i ∈ s := by simpa using hi
      exact ⟨(hdata i hi').1, (⊥ : IntermediateField F E).algebraMap_mem _, by simpa using he i hi'⟩
  · rw [hfin, Finset.sum_insertNone]
    simp only [Option.elim, map_add, map_mul, map_sum, logDeriv_algebraMap', deriv_algebraMap]
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [hγ i hi]]
    ring

include hconst in
theorem LiouvilleIn.descend_exp {t : E} (htr : Transcendental F t) {b : F} (ht : t′ = ψ b′ * t)
    {α : F} (h : LiouvilleIn F⟮t⟯ (ψ α)) : LiouvilleIn (⊥ : IntermediateField F E) (ψ α) := by
  classical
  obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := h
  choose! γ hγ using fun i (hi : i ∈ s) ↦ hconst (c i) (hdata i hi).1
  have hγ' : ∀ i ∈ s, (γ i)′ = 0 := fun i hi ↦ by
    apply (algebraMap F E).injective
    rw [← deriv_algebraMap, hγ i hi, (hdata i hi).1, map_zero]
  have heq' : ψ α = ∑ i ∈ s, ψ (γ i) * logDeriv (u i) + v′ := by
    rw [heq]; congr 1
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hγ i hi]
  obtain ⟨e, m, d, he, hfin⟩ := liouville_step_exponential t htr b′ ht
    (fun x _ hx ↦ hconst x hx) s γ u (fun i hi ↦ (hdata i hi).2) v hv α heq'
  have hN : (∑ i ∈ s, γ i * (m i : F))′ = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Derivation.leibniz, hγ' i hi, Derivation.map_intCast]
    simp
  refine ⟨ι, s, c, fun i ↦ ψ (e i), ψ ((∑ i ∈ s, γ i * (m i : F)) * b + d), ?_,
    (⊥ : IntermediateField F E).algebraMap_mem _, ?_⟩
  · exact fun i hi ↦ ⟨(hdata i hi).1, (⊥ : IntermediateField F E).algebraMap_mem _,
      by simpa using he i hi⟩
  · have hd : (ψ ((∑ i ∈ s, γ i * (m i : F)) * b + d))′ =
        ψ ((∑ i ∈ s, γ i * (m i : F)) * b′ + d′) := by
      rw [deriv_algebraMap, map_add, Derivation.leibniz, hN]
      simp
    rw [hfin, hd]
    simp only [map_add, map_mul, map_sum, logDeriv_algebraMap']
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [hγ i hi]]
    ring

include hconst in
theorem LiouvilleIn.descend_alg {t : E} (halg : IsAlgebraic F t) {α : F}
    (h : LiouvilleIn F⟮t⟯ (ψ α)) : LiouvilleIn (⊥ : IntermediateField F E) (ψ α) := by
  classical
  obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := h
  choose! γ hγ using fun i (hi : i ∈ s) ↦ hconst (c i) (hdata i hi).1
  have hγ' : ∀ i ∈ s, (γ i)′ = 0 := fun i hi ↦ by
    apply (algebraMap F E).injective
    rw [← deriv_algebraMap, hγ i hi, (hdata i hi).1, map_zero]
  have : FiniteDimensional F F⟮t⟯ := adjoin.finiteDimensional halg.isIntegral
  have hL : IsLiouville F F⟮t⟯ := inferInstance
  -- transfer the identity to `F⟮t⟯`
  let B := F⟮t⟯
  have hinjB : Function.Injective (algebraMap B E) := (algebraMap B E).injective
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, h₀⟩ := hL.isLiouville α s (fun i ↦ γ i) (fun i ↦ hγ' i i.2)
    (fun i ↦ ⟨u i, (hdata i i.2).2.1⟩) ⟨v, hv⟩ (by
      apply hinjB
      rw [map_add, map_sum, ← IsScalarTower.algebraMap_apply]
      simp only [map_mul, ← logDeriv_algebraMap, ← deriv_algebraMap,
        ← IsScalarTower.algebraMap_apply]
      rw [heq, ← Finset.sum_coe_sort s]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * logDeriv (u i)) (hγ i i.2).symm)
  refine ⟨ι₀, Finset.univ.filter fun x ↦ u₀ x ≠ 0, fun x ↦ ψ (c₀ x), fun x ↦ ψ (u₀ x), ψ v₀, ?_,
    (⊥ : IntermediateField F E).algebraMap_mem _, ?_⟩
  · intro x hx
    exact ⟨by rw [deriv_algebraMap, hc₀, map_zero],
      (⊥ : IntermediateField F E).algebraMap_mem _, by simpa using (Finset.mem_filter.mp hx).2⟩
  · rw [h₀, Finset.sum_filter]
    simp only [map_add, map_sum, map_mul, logDeriv_algebraMap', deriv_algebraMap]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs with hx
    · rfl
    · rw [not_not.mp hx, logDeriv_zero, map_zero, mul_zero]

end Differential
