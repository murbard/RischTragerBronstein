import RischTragerBronstein.Torsion.GoodPrimeAux
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange

/-!
# Non-special base points exist (1): the coefficient spaces

For numerators `Bⱼ(x, y)` (`j < n`) with weights `δⱼ`, `Vsp m` is the space of coefficient vectors
`c` with `deg cⱼ + δⱼ ≤ m` (the functions `∑ cⱼ(x) Bⱼ(x, y)`); `finrank_Vsp`: its dimension is
`∑ⱼ (m + 1 − δⱼ)`. `evPt x y` evaluates at a point. An *admissible fibre* is `x` with `n` values
`yₖ` at which the matrix `[Bⱼ(x, yₖ)]` is invertible.
-/

open Polynomial Module

namespace Curves

open CPoly Sup GTors

section Spaces

variable {K : Type*} [Field K] {n : ℕ} (B : Fin n → K[X][X]) (δ : Fin n → ℕ)

/-- Coefficient arrays to coefficient vectors. -/
noncomputable def coefMap (m : ℕ) : (∀ j : Fin n, Fin (m + 1 - δ j) → K) →ₗ[K] (Fin n → K[X]) :=
  LinearMap.pi fun j ↦ ((degreeLT K (m + 1 - δ j)).subtype ∘ₗ
    (degreeLTEquiv K (m + 1 - δ j)).symm.toLinearMap) ∘ₗ LinearMap.proj j

lemma coefMap_injective (m : ℕ) : Function.Injective (coefMap δ (K := K) m) := by
  intro a b h
  funext j
  have := congrFun h j
  simp only [coefMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe, Submodule.subtype_apply] at this
  exact (degreeLTEquiv K _).symm.injective (Subtype.ext this)

variable (K) in
/-- **The space of coefficient vectors** with `deg cⱼ + δⱼ ≤ m`. -/
noncomputable def Vsp (m : ℕ) : Submodule K (Fin n → K[X]) := LinearMap.range (coefMap (K := K) δ m)

lemma mem_Vsp (m : ℕ) (c : Fin n → K[X]) :
    c ∈ Vsp K δ m ↔ ∀ j, c j ∈ degreeLT K (m + 1 - δ j) := by
  constructor
  · rintro ⟨a, rfl⟩ j
    simp only [coefMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply]
    exact Subtype.mem _
  · intro h
    refine ⟨fun j ↦ degreeLTEquiv K _ ⟨c j, h j⟩, ?_⟩
    funext j
    simp [coefMap]

instance (m : ℕ) : FiniteDimensional K (Vsp K δ m) := by
  unfold Vsp; infer_instance

/-- **The dimension of `Vsp m`.** -/
theorem finrank_Vsp (m : ℕ) : finrank K (Vsp K δ m) = ∑ j, (m + 1 - δ j) := by
  rw [Vsp, LinearMap.finrank_range_of_inj (coefMap_injective δ m), Module.finrank_pi_fintype]
  simp

/-- Evaluation of `∑ⱼ cⱼ(x) Bⱼ(x, y)` at the point `(x, y)`. -/
noncomputable def evPt (x y : K) : (Fin n → K[X]) →ₗ[K] K where
  toFun c := ∑ j, (c j).eval x * evalW (B j) x y
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_assoc]

lemma evPt_apply (x y : K) (c : Fin n → K[X]) :
    evPt B x y c = ∑ j, (c j).eval x * evalW (B j) x y := rfl

/-- An admissible fibre: `n` points `(x, yₖ)` with `[Bⱼ(x, yₖ)]` invertible. -/
structure AdmFib where
  x : K
  ys : Fin n → K
  hdet : (Matrix.of fun (k j : Fin n) ↦ evalW (B j) x (ys k)).det ≠ 0

variable {B}

/-- **Prescribing values on an admissible fibre**: for every `v` there are constants `u` with
`∑ⱼ uⱼ Bⱼ(x, yₖ) = vₖ`. -/
lemma AdmFib.exists_vals (f : AdmFib B) (v : Fin n → K) :
    ∃ u : Fin n → K, ∀ k, ∑ j, u j * evalW (B j) f.x (f.ys k) = v k := by
  classical
  set M := Matrix.of fun (k j : Fin n) ↦ evalW (B j) f.x (f.ys k)
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr f.hdet
  refine ⟨M⁻¹.mulVec v, fun k ↦ ?_⟩
  have := congrFun (Matrix.mulVec_mulVec v M M⁻¹) k
  rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at this
  rw [← this]
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- **Vanishing on a whole admissible fibre** forces the coefficients to vanish at `x`. -/
lemma AdmFib.coeff_eval_eq_zero (f : AdmFib B) (c : Fin n → K[X])
    (h : ∀ k, evPt B f.x (f.ys k) c = 0) : ∀ j, (c j).eval f.x = 0 := by
  classical
  set M := Matrix.of fun (k j : Fin n) ↦ evalW (B j) f.x (f.ys k)
  have hv : M.mulVec (fun j ↦ (c j).eval f.x) = 0 := by
    funext k
    have := h k
    simp only [evPt_apply] at this
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have := Matrix.eq_zero_of_mulVec_eq_zero f.hdet hv
  exact fun j ↦ congrFun this j

end Spaces

end Curves
