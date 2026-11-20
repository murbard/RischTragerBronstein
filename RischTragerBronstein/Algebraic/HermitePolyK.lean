import RischTragerBronstein.Algebraic.HermiteExistK
import RischTragerBronstein.Differential.Monomial

/-!
# The Hermite decomposition as a polynomial identity, over any field

`hermite_polyK`: for `K` of characteristic zero, `p ∈ K[X]` squarefree with `deg p ≥ 1`, and
`D ≠ 0` split over `K`, there are `W, B₀ ∈ K[X]` (`deg B₀ ≤ n − 2`), a set `T` of non-branch
roots of `D` and residues `c` with

  `2 A D S = S L_D(W) + 2 D² S B₀ + 2 D² ∑_{α ∈ T} c_α S/(X − α)`,  `S = ∏_{α ∈ T} (X − α)`.
-/

open Polynomial Differential

namespace EllAlgo

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- `K(X)`, as an opaque field (so that its `ℤ`-algebra structure is the canonical one). -/
def KX (K : Type*) [Field K] : Type _ := FractionRing K[X]

noncomputable instance (K : Type*) [Field K] : Field (KX K) :=
  inferInstanceAs (Field (FractionRing K[X]))
noncomputable instance (K : Type*) [Field K] : Algebra K[X] (KX K) :=
  inferInstanceAs (Algebra K[X] (FractionRing K[X]))
instance (K : Type*) [Field K] : IsFractionRing K[X] (KX K) :=
  inferInstanceAs (IsFractionRing K[X] (FractionRing K[X]))
noncomputable instance (K : Type*) [Field K] : Algebra K (KX K) :=
  ((algebraMap K[X] (KX K)).comp (algebraMap K K[X])).toAlgebra
instance (K : Type*) [Field K] : IsScalarTower K K[X] (KX K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
instance (K : Type*) [Field K] [CharZero K] : CharZero (KX K) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective K[X] (KX K))

/-- `L_D(W) = 2(W′D − WD′)p + WDp′`. -/
noncomputable def LDK (p D W : K[X]) : K[X] :=
  2 * (derivative W * D - W * derivative D) * p + W * D * derivative p

/-- **The Hermite decomposition over `K`, polynomial form.** -/
theorem hermite_polyK (p : K[X]) (hsq : Squarefree p) (hp1 : 1 ≤ p.natDegree) (A D : K[X])
    (hD : D ≠ 0) (hsplit : D.Splits) :
    ∃ (W B₀ : K[X]) (T : Finset K) (c : K → K), (∀ α ∈ T, D.IsRoot α ∧ ¬ p.IsRoot α) ∧
      (B₀ = 0 ∨ B₀.natDegree + 2 ≤ p.natDegree) ∧
      2 * A * D * (∏ α ∈ T, (X - C α)) = (∏ α ∈ T, (X - C α)) * LDK p D W +
        2 * D ^ 2 * (∏ α ∈ T, (X - C α)) * B₀ +
        2 * D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) := by
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
  obtain ⟨W, B₀, R, ⟨T, c, hT, rfl⟩, hB, hid⟩ :=
    hermite_existsK hCK hne hxd hsq hp1 D.natDegree D rfl hD hsplit A
  refine ⟨W, B₀, T, c, hT, hB, ?_⟩
  apply hinj
  have hDx := hne D hD
  have hlin0 : ∀ α : K, x - algebraMap K E α ≠ 0 := fun α ↦ by
    have := hne _ (X_sub_C_ne_zero α); simpa using this
  have hL : LopK x p (aeval x W / aeval x D) = aeval x (LDK p D W) / (2 * aeval x D ^ 2) := by
    unfold LopK LDK
    rw [Derivation.leibniz_div, deriv_aeval_x x hCK hxd, deriv_aeval_x x hCK hxd]
    simp only [smul_eq_mul, map_add, map_mul, map_sub, map_ofNat]
    have hD2 : (2 : E) * aeval x D ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hDx)
    have hDinv : aeval x D * (aeval x D)⁻¹ = 1 := mul_inv_cancel₀ hDx
    have h2inv : (2 : E) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero
    rw [eq_div_iff hD2]
    set u := aeval x D * (aeval x D)⁻¹
    set v := (2 : E) * 2⁻¹
    linear_combination (2 * (aeval x D * aeval x (derivative W) - aeval x W * aeval x (derivative D)) *
      aeval x p * (u + 1) + v * aeval x W * aeval x (derivative p) * aeval x D) * hDinv +
      (aeval x W * aeval x (derivative p) * aeval x D) * h2inv
  rw [hL] at hid
  have hsum : (∑ α ∈ T, algebraMap K E (c α) / (x - algebraMap K E α)) *
      ∏ α ∈ T, (x - algebraMap K E α) =
      ∑ α ∈ T, algebraMap K E (c α) * ∏ β ∈ T.erase α, (x - algebraMap K E β) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    rw [← Finset.mul_prod_erase T _ hα, ← mul_assoc, div_mul_cancel₀ _ (hlin0 α)]
  simp only [← hav]
  simp only [map_add, map_mul, map_ofNat, map_pow, map_prod, map_sum, aeval_C, map_sub, aeval_X]
  rw [← hsum, (div_eq_iff hDx).mp hid]
  have hD2 : (2 : E) * aeval x D ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hDx)
  have hLq : aeval x (LDK p D W) = aeval x (LDK p D W) / (2 * aeval x D ^ 2) *
      (2 * aeval x D ^ 2) := (div_mul_cancel₀ _ hD2).symm
  set Lq := aeval x (LDK p D W) / (2 * aeval x D ^ 2)
  rw [hLq]
  ring

end EllAlgo
