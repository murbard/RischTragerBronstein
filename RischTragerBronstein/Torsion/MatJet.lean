import RischTragerBronstein.Torsion.GJets
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Vanishing on a split fibre, in basis coordinates

* `matrix_jet_dvd`: if `M(t)` is a square matrix over `R[t]` whose determinant has unit constant
  term and `M(t) v(t) ≡ 0 (mod tˡ)`, then `v ≡ 0 (mod tˡ)`;
* `coords_dvd_of_vanish`: if `Ψ = ∑ⱼ cⱼ(x) Bⱼ(x, Y)` vanishes to order `ℓ` along `n` jets through
  points above `x₀` at which the matrix of values `Bⱼ(x₀, bₖ)` is invertible, then `(x − x₀)ˡ` divides
  every coordinate `cⱼ`.
-/

open Polynomial Sup

namespace GTors

section Ring

variable {R : Type*} [CommRing R]

/-- **Inverting a matrix modulo `tˡ`.** -/
theorem matrix_jet_dvd {n : ℕ} (M : Matrix (Fin n) (Fin n) R[X]) (hdet : IsUnit (M.det.coeff 0))
    (v : Fin n → R[X]) (ℓ : ℕ) (h : ∀ k, X ^ ℓ ∣ ∑ j, M k j * v j) : ∀ j, X ^ ℓ ∣ v j := by
  classical
  intro j
  have hmul : (M.adjugate * M).mulVec v = M.det • v := by
    rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hj := congrFun hmul j
  rw [← Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul] at hj
  have hd : X ^ ℓ ∣ M.det * v j := by
    rw [← hj, Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun k _ ↦ Dvd.dvd.mul_left (by
      simp only [Matrix.mulVec, dotProduct]; exact h k) _
  exact Jac.X_pow_dvd_of_mul hdet hd

lemma jetN_sum_C_mul {n : ℕ} (c : Fin n → R[X]) (B : Fin n → R[X][X]) (x₀ : R) (V : R[X]) :
    jetN (∑ j, Polynomial.C (c j) * B j) x₀ V = ∑ j, (c j).comp (X + C x₀) * jetN (B j) x₀ V := by
  rw [jetN, Polynomial.map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← jetN, jetN_C_poly_mul]

/-- **Coordinates of a function vanishing on a split fibre.** -/
theorem coords_dvd_of_vanish {n : ℕ} (c : Fin n → R[X]) (B : Fin n → R[X][X]) (x₀ : R)
    (V : Fin n → R[X]) (ℓ : ℕ)
    (hdet : IsUnit (Matrix.det (Matrix.of fun k j ↦ evalW (B j) x₀ ((V k).coeff 0))))
    (h : ∀ k, X ^ ℓ ∣ jetN (∑ j, Polynomial.C (c j) * B j) x₀ (V k)) :
    ∀ j, (X - C x₀) ^ ℓ ∣ c j := by
  set M : Matrix (Fin n) (Fin n) R[X] := Matrix.of fun k j ↦ jetN (B j) x₀ (V k) with hM
  have hM0 : M.det.coeff 0 = Matrix.det (Matrix.of fun k j ↦ evalW (B j) x₀ ((V k).coeff 0)) := by
    rw [coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext k j
    simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, coe_evalRingHom,
      ← coeff_zero_eq_eval_zero, jetN_coeff_zero]
  have := matrix_jet_dvd M (by rw [hM0]; exact hdet) (fun j ↦ (c j).comp (X + C x₀)) ℓ
    (fun k ↦ by
      have := h k
      rw [jetN_sum_C_mul] at this
      simpa only [hM, Matrix.of_apply, mul_comm] using this)
  exact fun j ↦ Jac.dvd_of_comp (this j)

end Ring

end GTors
