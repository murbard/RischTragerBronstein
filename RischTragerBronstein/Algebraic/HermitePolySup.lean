import RischTragerBronstein.Algebraic.HermiteSup
import RischTragerBronstein.Algebraic.HermitePolyK

/-!
# The superelliptic Hermite decomposition as a polynomial identity

`hermite_polyS`: for `p ∈ K[X]` squarefree, `μ ∈ K` not a positive integer, and `D ≠ 0` split,
there are `W, B₀ ∈ K[X]`, a set `T` of non-branch roots of `D` and residues `c` with

  `A D S = S L_D(W) + D² S B₀ + D² ∑_{α ∈ T} c_α S/(X − α)`,  `S = ∏_{α ∈ T} (X − α)`,

where `L_D(W) = (W′D − WD′)p + μ W D p′`.
-/

open Polynomial Differential

namespace EllAlgo

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- `L_D(W) = (W′D − WD′)p + μ W D p′`. -/
noncomputable def LDS (μ : K) (p D W : K[X]) : K[X] :=
  (derivative W * D - W * derivative D) * p + C μ * W * D * derivative p

/-- **The superelliptic Hermite decomposition, polynomial form.** -/
theorem hermite_polyS (p : K[X]) (hsq : Squarefree p) (μ : K) (hμ : ∀ k : ℕ, μ ≠ k + 1)
    (A D : K[X]) (hD : D ≠ 0) (hsplit : D.Splits) :
    ∃ (W B₀ : K[X]) (T : Finset K) (c : K → K), (∀ α ∈ T, D.IsRoot α ∧ ¬ p.IsRoot α) ∧
      A * D * (∏ α ∈ T, (X - C α)) = (∏ α ∈ T, (X - C α)) * LDS μ p D W +
        D ^ 2 * (∏ α ∈ T, (X - C α)) * B₀ +
        D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) := by
  classical
  letI : Differential K := ⟨0⟩
  letI : Differential K[X] := polynomialOfDeriv 1
  letI : Differential (KX K) := ofFractionRing K[X] (KX K)
  set E := KX K
  have hCK : ∀ c : K, c′ = 0 := fun c ↦ Derivation.zero_apply c
  have hCdiff : ∀ c : K, (C c : K[X])′ = 0 := fun c ↦ by
    show implicitDeriv 1 (C c) = 0
    simp [implicitDeriv, hCK]
  haveI : DifferentialAlgebra K E := ⟨fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K K[X] E, ofFractionRing_deriv_algebraMap]
    rw [show (algebraMap K K[X] c)′ = 0 from hCdiff c, map_zero, hCK c, map_zero]⟩
  set x : E := algebraMap K[X] E X
  have hxd : x′ = 1 := by
    rw [ofFractionRing_deriv_algebraMap]
    change algebraMap K[X] E (implicitDeriv 1 X) = 1
    rw [implicitDeriv_X, map_one]
  have hav : ∀ Q : K[X], aeval x Q = algebraMap K[X] E Q := fun Q ↦ by
    induction Q using Polynomial.induction_on' with
    | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
    | monomial n a =>
      rw [aeval_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
        IsScalarTower.algebraMap_apply K K[X] E]
      rfl
  have hinj : Function.Injective (algebraMap K[X] E) := IsFractionRing.injective K[X] E
  have hne : ∀ Q : K[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hQ ↦ by
    rw [hav]; exact (map_ne_zero_iff _ hinj).mpr hQ
  obtain ⟨W, B₀, R, ⟨T, c, hT, rfl⟩, hid⟩ :=
    hermite_existsS hCK hne hxd hsq hμ D.natDegree D rfl hD hsplit A
  refine ⟨W, B₀, T, c, hT, ?_⟩
  apply hinj
  have hDx := hne D hD
  have hlin0 : ∀ α : K, x - algebraMap K E α ≠ 0 := fun α ↦ by
    have := hne _ (X_sub_C_ne_zero α); simpa using this
  have hL : LopS x p μ (aeval x W / aeval x D) = aeval x (LDS μ p D W) / aeval x D ^ 2 := by
    unfold LopS LDS
    rw [Derivation.leibniz_div, deriv_aeval_x x hCK hxd, deriv_aeval_x x hCK hxd]
    simp only [smul_eq_mul, map_add, map_mul, map_sub, aeval_C]
    rw [eq_div_iff (pow_ne_zero 2 hDx), div_eq_mul_inv]
    have hDinv : aeval x D * (aeval x D)⁻¹ = 1 := mul_inv_cancel₀ hDx
    set u := aeval x D * (aeval x D)⁻¹
    linear_combination ((aeval x D * aeval x (derivative W) - aeval x W * aeval x (derivative D)) *
      aeval x p * (u + 1) + algebraMap K E μ * aeval x W * aeval x (derivative p) * aeval x D) * hDinv
  rw [hL] at hid
  have hsum : (∑ α ∈ T, algebraMap K E (c α) / (x - algebraMap K E α)) *
      ∏ α ∈ T, (x - algebraMap K E α) =
      ∑ α ∈ T, algebraMap K E (c α) * ∏ β ∈ T.erase α, (x - algebraMap K E β) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    rw [← Finset.mul_prod_erase T _ hα, ← mul_assoc, div_mul_cancel₀ _ (hlin0 α)]
  simp only [← hav]
  simp only [map_add, map_mul, map_pow, map_prod, map_sum, aeval_C, map_sub, aeval_X]
  rw [← hsum, (div_eq_iff hDx).mp hid]
  have hD2 : aeval x D ^ 2 ≠ 0 := pow_ne_zero 2 hDx
  have hLq : aeval x (LDS μ p D W) = aeval x (LDS μ p D W) / aeval x D ^ 2 * aeval x D ^ 2 :=
    (div_mul_cancel₀ _ hD2).symm
  set Lq := aeval x (LDS μ p D W) / aeval x D ^ 2
  rw [hLq]
  ring

end EllAlgo
