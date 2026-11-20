import RischTragerBronstein.Elementary.AlgDeriv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Trace and norm commute with the derivation

For a finite extension `L/K` of differential fields of characteristic `0`:
`Tr(z′) = Tr(z)′` (`trace_deriv`) and `Tr(u′/u) = N(u)′/N(u)` (`trace_logDeriv`). The
`K`-embeddings of `L` into `K̄` commute with the derivations, since the derivative of an algebraic
element is forced by its minimal polynomial.
-/

open Polynomial

namespace Differential

section Prod

variable {F : Type*} [Field F] [Differential F]

/-- `(∏ fᵢ)′/∏ fᵢ = ∑ fᵢ′/fᵢ`. -/
lemma logDeriv_finset_prod {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i)′ / ∏ i ∈ s, f i = ∑ i ∈ s, (f i)′ / f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    field_simp
    ring

end Prod

variable {K L : Type*} [Field K] [Field L] [Differential K] [Differential L] [Algebra K L]
  [DifferentialAlgebra K L] [CharZero K] [FiniteDimensional K L]

/-- The `K`-embeddings into `K̄` commute with the derivations. -/
lemma algHom_deriv_emb (σ : L →ₐ[K] AlgebraicClosure K) (z : L) : σ z′ = (σ z)′ := by
  have hz : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  rw [deriv_eq_algDerivFun z hz, deriv_eq_algDerivFun (σ z) (hz.map σ)]
  unfold algDerivFun
  rw [minpoly.algHom_eq σ σ.injective z, map_div₀, map_neg, aeval_algHom_apply,
    aeval_algHom_apply]

/-- **The trace commutes with the derivation.** -/
theorem trace_deriv (z : L) : Algebra.trace K L z′ = (Algebra.trace K L z)′ := by
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [trace_eq_sum_embeddings (AlgebraicClosure K), ← deriv_algebraMap,
    trace_eq_sum_embeddings (AlgebraicClosure K), map_sum]
  exact Finset.sum_congr rfl fun σ _ ↦ algHom_deriv_emb σ z

/-- **The trace of a logarithmic derivative is the logarithmic derivative of the norm.** -/
theorem trace_logDeriv (u : L) (hu : u ≠ 0) :
    Algebra.trace K L (u′ / u) = (Algebra.norm K u)′ / Algebra.norm K u := by
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_div₀ (algebraMap K (AlgebraicClosure K)), ← deriv_algebraMap,
    Algebra.norm_eq_prod_embeddings K (AlgebraicClosure K),
    trace_eq_sum_embeddings (AlgebraicClosure K),
    logDeriv_finset_prod _ _ fun σ _ ↦ (map_ne_zero_iff _ σ.injective).mpr hu]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [map_div₀ σ, algHom_deriv_emb]

end Differential

namespace PowerBasis

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **The trace of a power of the generator**: `Tr(θⁱ) = ∑ⱼ [Xʲ](X^{i+j} mod μ)`. -/
theorem trace_gen_pow (pb : PowerBasis K M) (i : ℕ) :
    Algebra.trace K M (pb.gen ^ i) = ∑ j ∈ Finset.range pb.dim,
      ((X ^ (i + j) : K[X]) %ₘ minpoly K pb.gen).coeff j := by
  classical
  rw [Algebra.trace_eq_matrix_trace pb.basis, Matrix.trace]
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ ((X ^ (i + j) : K[X]) %ₘ minpoly K pb.gen).coeff j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, PowerBasis.coe_basis, ← pow_add]
  set μ := minpoly K pb.gen
  have hμ : μ.Monic := minpoly.monic pb.isIntegral_gen
  set r := (X ^ (i + (j : ℕ)) : K[X]) %ₘ μ with hr
  have hev : pb.gen ^ (i + (j : ℕ)) = aeval pb.gen r := by
    have h := modByMonic_add_div (X ^ (i + (j : ℕ)) : K[X]) μ
    have h2 := congrArg (aeval pb.gen) h
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero, map_pow, aeval_X] at h2
    exact h2.symm
  have hdeg : r.natDegree < pb.dim := by
    rw [← PowerBasis.natDegree_minpoly]
    by_cases h0 : r = 0
    · rw [h0, natDegree_zero]; exact Polynomial.natDegree_pos_iff_degree_pos.mpr
        (minpoly.degree_pos pb.isIntegral_gen)
    · exact natDegree_modByMonic_lt _ hμ (minpoly.ne_one K pb.gen)
  have hsum : aeval pb.gen r = ∑ k : Fin pb.dim, r.coeff k • pb.basis k := by
    rw [aeval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range (fun k ↦ r.coeff k • pb.gen ^ k)]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [PowerBasis.coe_basis]
  rw [hev, hsum, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

end PowerBasis
