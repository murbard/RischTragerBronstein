import RischTragerBronstein.Algebraic.HermiteUnique
import RischTragerBronstein.Differential.Monomial

/-!
# The Hermite decomposition as a polynomial identity

`hermite_poly`: for `p ∈ ℚ[X]` squarefree, `deg p ≥ 1`, and `D ≠ 0` split over `ℚ`, there are
`W, B₀ ∈ ℚ[X]` (`deg B₀ ≤ n − 2`), a set `T` of non-branch roots of `D` and residues `c` with

  `2 A D S = S L_D(W) + 2 D² S B₀ + 2 D² ∑_{α ∈ T} c_α S/(X − α)`,  `S = ∏_{α ∈ T} (X − α)`.

Obtained from `hermite_exists` in the differential field `ℚ(X)` (`X′ = 1`).
-/

open Polynomial Differential

namespace EllAlgo

/-- `ℚ` with the zero derivation. -/
local instance : Differential ℚ := ⟨0⟩

/-- `ℚ(X)`, as an opaque field (so that its `ℤ`-algebra structure is the canonical one). -/
def QX : Type := FractionRing ℚ[X]

noncomputable instance : Field QX := inferInstanceAs (Field (FractionRing ℚ[X]))
noncomputable instance : Algebra ℚ[X] QX := inferInstanceAs (Algebra ℚ[X] (FractionRing ℚ[X]))
instance : IsFractionRing ℚ[X] QX := inferInstanceAs (IsFractionRing ℚ[X] (FractionRing ℚ[X]))
instance : CharZero QX :=
  charZero_of_injective_algebraMap (IsFractionRing.injective ℚ[X] QX)

/-- **The Hermite decomposition, polynomial form.** -/
theorem hermite_poly (p : ℚ[X]) (hsq : Squarefree p) (hp1 : 1 ≤ p.natDegree) (A D : ℚ[X])
    (hD : D ≠ 0) (hsplit : D.Splits) :
    ∃ (W B₀ : ℚ[X]) (T : Finset ℚ) (c : ℚ → ℚ), (∀ α ∈ T, D.IsRoot α ∧ ¬ p.IsRoot α) ∧
      (B₀ = 0 ∨ B₀.natDegree + 2 ≤ p.natDegree) ∧
      2 * A * D * (∏ α ∈ T, (X - C α)) = (∏ α ∈ T, (X - C α)) * LD p D W +
        2 * D ^ 2 * (∏ α ∈ T, (X - C α)) * B₀ +
        2 * D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) := by
  classical
  letI : Differential ℚ[X] := polynomialOfDeriv 1
  letI : Differential QX := ofFractionRing ℚ[X] QX
  set K := QX
  set x : K := algebraMap ℚ[X] K X
  have hxd : x′ = 1 := by
    rw [ofFractionRing_deriv_algebraMap]
    change algebraMap ℚ[X] K (implicitDeriv 1 X) = 1
    rw [implicitDeriv_X, map_one]
  have hsc : ∀ q : ℚ, algebraMap ℚ[X] K (C q) = (q : K) := fun q ↦ by
    have : (algebraMap ℚ[X] K).comp (C : ℚ →+* ℚ[X]) = algebraMap ℚ K := RingHom.ext_rat _ _
    have h := RingHom.congr_fun this q
    rw [RingHom.comp_apply] at h
    rw [h, eq_ratCast]
  have hav : ∀ Q : ℚ[X], aeval x Q = algebraMap ℚ[X] K Q := fun Q ↦ by
    induction Q using Polynomial.induction_on' with
    | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
    | monomial n a =>
      rw [aeval_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, hsc, eq_ratCast]
  have hinj : Function.Injective (algebraMap ℚ[X] K) := IsFractionRing.injective ℚ[X] K
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hQ ↦ by
    rw [hav]; exact (map_ne_zero_iff _ hinj).mpr hQ
  obtain ⟨W, B₀, R, ⟨T, c, hT, rfl⟩, hB, hid⟩ :=
    hermite_exists hne hxd hsq hp1 D.natDegree D rfl hD hsplit A
  refine ⟨W, B₀, T, c, hT, hB, ?_⟩
  apply hinj
  have hDx := hne D hD
  have hlin0 : ∀ α : ℚ, x - ((α : ℚ) : K) ≠ 0 := fun α ↦ by
    have := hne _ (X_sub_C_ne_zero α); simpa using this
  -- `Lop (W/D) = L_D(W)/(2D²)`
  have hL : Lop x p (aeval x W / aeval x D) = aeval x (LD p D W) / (2 * aeval x D ^ 2) := by
    unfold Lop LD
    rw [Derivation.leibniz_div, deriv_aeval_rat x hxd, deriv_aeval_rat x hxd]
    simp only [smul_eq_mul, map_add, map_mul, map_sub, map_ofNat]
    have hD2 : (2 : K) * aeval x D ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hDx)
    have hDinv : aeval x D * (aeval x D)⁻¹ = 1 := mul_inv_cancel₀ hDx
    have h2inv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero
    rw [eq_div_iff hD2]
    set u := aeval x D * (aeval x D)⁻¹
    set v := (2 : K) * 2⁻¹
    linear_combination (2 * (aeval x D * aeval x (derivative W) - aeval x W * aeval x (derivative D)) *
      aeval x p * (u + 1) + v * aeval x W * aeval x (derivative p) * aeval x D) * hDinv +
      (aeval x W * aeval x (derivative p) * aeval x D) * h2inv
  rw [hL] at hid
  have hS0 : ∏ α ∈ T, (x - ((α : ℚ) : K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun α _ ↦ hlin0 α
  have hsum : (∑ α ∈ T, ((c α : ℚ) : K) / (x - ((α : ℚ) : K))) *
      ∏ α ∈ T, (x - ((α : ℚ) : K)) =
      ∑ α ∈ T, ((c α : ℚ) : K) * ∏ β ∈ T.erase α, (x - ((β : ℚ) : K)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    rw [← Finset.mul_prod_erase T _ hα, ← mul_assoc, div_mul_cancel₀ _ (hlin0 α)]
  simp only [← hav]
  simp only [map_add, map_mul, map_ofNat, map_pow, map_prod, map_sum, aeval_C, eq_ratCast, map_sub,
    aeval_X]
  rw [← hsum, (div_eq_iff hDx).mp hid]
  have hD2 : (2 : K) * aeval x D ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hDx)
  have hLq : aeval x (LD p D W) = aeval x (LD p D W) / (2 * aeval x D ^ 2) *
      (2 * aeval x D ^ 2) := (div_mul_cancel₀ _ hD2).symm
  set Lq := aeval x (LD p D W) / (2 * aeval x D ^ 2)
  rw [hLq]
  ring

end EllAlgo
