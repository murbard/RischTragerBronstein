import RischTragerBronstein.Computable.SysDenAnn

/-!
# Diagonalization of matrices annihilated by split squarefree polynomials

If `∏_{μ ∈ s} (A − μ) = 0` for a finite set `s` of scalars, every vector is a sum of
eigenvectors (the Lagrange idempotents `Lμ(A)` project onto them, `∑ Lμ = 1`), so a basis of
eigenvectors exists and `B⁻¹ A B` is diagonal for the matrix `B` of that basis
(`exists_diag_of_ann`). Over `ℚ` this applies to the residue matrices of logarithmic derivations
(eigenvalues `±k/n!`).
-/

open Polynomial

namespace Tower.Sys

variable {K : Type*} [Field K] {n : ℕ}

/-- **Eigenvectors span** when `∏_{μ ∈ s} (A − μ) = 0`. -/
lemma mem_span_eigen [DecidableEq K] (A : Matrix (Fin n) (Fin n) K) (s : Finset K)
    (hann : aeval A (Lagrange.nodal s id) = 0) (v : Fin n → K) :
    v ∈ Submodule.span K {u : Fin n → K | ∃ μ ∈ s, A.mulVec u = μ • u} := by
  by_cases hs : s.Nonempty
  · have hsum := Lagrange.sum_basis (v := (id : K → K)) (Set.injOn_id _) hs
    have hv : v = ∑ μ ∈ s, (aeval A (Lagrange.basis s id μ)).mulVec v := by
      rw [← Matrix.sum_mulVec, ← map_sum, hsum, map_one, Matrix.one_mulVec]
    rw [hv]
    refine Submodule.sum_mem _ fun μ hμ ↦ Submodule.subset_span ⟨μ, hμ, ?_⟩
    have h := congrArg (aeval A) (X_sub_mul_basis s id μ hμ)
    rw [map_mul, map_mul, hann, mul_zero, map_sub, aeval_X, aeval_C] at h
    rw [Matrix.mulVec_mulVec, ← sub_eq_zero, ← Matrix.mulVec_mulVec]
    have : (A - algebraMap K _ (id μ)) * aeval A (Lagrange.basis s id μ) = 0 := h
    have e : μ • (aeval A (Lagrange.basis s id μ)).mulVec v =
        (algebraMap K (Matrix (Fin n) (Fin n) K) μ * aeval A (Lagrange.basis s id μ)).mulVec v := by
      rw [← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [e, Matrix.mulVec_mulVec, ← Matrix.sub_mulVec, ← sub_mul]
    simp only [id] at this
    rw [this, Matrix.zero_mulVec]
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst hs
    rw [Lagrange.nodal_empty, map_one] at hann
    have : v = 0 := by
      funext i
      have := congrFun (congrFun hann i) i
      simp at this
    rw [this]; exact Submodule.zero_mem _

/-- **Diagonalization**: if `∏_{μ ∈ s} (A − μ) = 0` then `B⁻¹ A B` is diagonal for some invertible
`B`. -/
theorem exists_diag_of_ann [DecidableEq K] (A : Matrix (Fin n) (Fin n) K) (s : Finset K)
    (hann : aeval A (Lagrange.nodal s id) = 0) :
    ∃ (B Bi : Matrix (Fin n) (Fin n) K) (d : Fin n → K), B * Bi = 1 ∧ Bi * B = 1 ∧
      Bi * A * B = Matrix.diagonal d := by
  classical
  set E := {u : Fin n → K | ∃ μ ∈ s, A.mulVec u = μ • u} with hE
  have hspan : Submodule.span K E = ⊤ := eq_top_iff.mpr fun v _ ↦ mem_span_eigen A s hann v
  obtain ⟨b, hbE, hbspan, hbli⟩ := exists_linearIndependent K E
  let bas : Module.Basis b K (Fin n → K) := Module.Basis.mk hbli (by
    rw [Subtype.range_coe, hbspan, hspan])
  let v : Module.Basis (Fin n) K (Fin n → K) :=
    bas.reindex (bas.indexEquiv (Pi.basisFun K (Fin n)))
  have hvE : ∀ j, v j ∈ E := fun j ↦ by
    simp only [v, Module.Basis.reindex_apply, bas, Module.Basis.mk_apply]
    exact hbE (Subtype.mem _)
  choose μ _ hμ using hvE
  set B := (Pi.basisFun K (Fin n)).toMatrix v with hB
  set Bi := v.toMatrix (Pi.basisFun K (Fin n)) with hBi
  have h1 : B * Bi = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : Bi * B = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hAB : A * B = B * Matrix.diagonal μ := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hB, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    have := congrFun (hμ j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [this, mul_comm]
  refine ⟨B, Bi, μ, h1, h2, ?_⟩
  rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc, h2, Matrix.one_mul]

end Tower.Sys
