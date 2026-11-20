import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A rational vector in the row space

`exists_comb`: if every rational relation `∑_P λ_P A_P = 0` between the rows of a finite matrix
`A` also kills the column `v`, then `v = A s` for a rational vector `s`.
-/

open Module

/-- **A column in the column space**, by duality. -/
theorem exists_comb {P I : Type*} [Fintype P] [Fintype I] (A : P → I → ℚ) (v : P → ℚ)
    (h : ∀ lam : P → ℚ, (∀ i, ∑ p, lam p * A p i = 0) → ∑ p, lam p * v p = 0) :
    ∃ s : I → ℚ, ∀ p, ∑ i, s i * A p i = v p := by
  classical
  set L : I → (P → ℚ) →ₗ[ℚ] ℚ := fun i ↦
    { toFun := fun lam ↦ ∑ p, lam p * A p i
      map_add' := fun a b ↦ by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a ↦ by simp [Finset.mul_sum, mul_assoc] }
  set Kf : (P → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun lam ↦ ∑ p, lam p * v p
      map_add' := fun a b ↦ by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a ↦ by simp [Finset.mul_sum, mul_assoc] }
  have hker : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker Kf := by
    intro lam hlam
    rw [Submodule.mem_iInf] at hlam
    exact h lam fun i ↦ hlam i
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨s, fun p ↦ ?_⟩
  have := congrArg (fun f : (P → ℚ) →ₗ[ℚ] ℚ ↦ f (Pi.single p 1)) hs
  rw [LinearMap.sum_apply] at this
  simpa [L, Kf, Pi.single_apply] using this
