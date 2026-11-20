import RischTragerBronstein.Computable.LimitedPrimPoly
import RischTragerBronstein.Liouville.PrimitiveInField

/-!
# Limited integration inside `S(x)(t₁)`: completeness of the step, in polynomial form

Two-level model: `K₁ = S(x)`, `K₂ = K₁(t₁)` (fraction field of `K₁[X]`, `t₁′ = η₁`, no new constants).
If some `z ∈ K₂` and constant `c ∈ S` satisfy `z′ = A - c η₂` for the polynomial `A ∈ R(x)[t₁]` given
by codes, then `limitedPrimCodes` succeeds; and if `η₂` is not (a constant multiple of) a derivative
in `K₂`, the returned constant is `c` and `z` is the returned polynomial up to a constant.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁]
variable [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The polynomial in `t₁` with coefficient codes `(A j, D j)`, `j ≤ d`. -/
noncomputable def polyOfCodes (ι : R →+* S) (A D : ℕ → CPoly R) (d : ℕ) : K₁[X] :=
  ∑ j ∈ Finset.range (d + 1), C (ev K₁ ι (A j, D j)) * X ^ j

lemma map_polyOfCodes (ι : R →+* S) (A D : ℕ → CPoly R) (d : ℕ) :
    φ₂ (polyOfCodes (K₁ := K₁) ι A D d) =
      ev₂ (K₁ := K₁) ι (φ₂ X) (fun j ↦ (A j, D j)) d := by
  simp only [polyOfCodes, ev₂, map_sum, map_mul, map_pow]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, Polynomial.algebraMap_eq]

theorem limitedPrimCodes_complete_poly (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K₁, y′ = 0 → ∃ b : S, y = φ (C b))
    {En Ed En₂ Ed₂ : CPoly R} {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En Ed Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd : toPoly Ed ≠ 0) (hη0 : isZero Iη₁.r = false)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ev K₁ ι (En, Ed))) P)
    (hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e)
    (hη₂nd : ∀ (y : K₂) (a : S), a ≠ 0 → y′ ≠ φ₂ (C (φ (C a) * ev K₁ ι (En₂, Ed₂))))
    (A D : ℕ → CPoly R) (d : ℕ) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) (z : K₂) (c : S)
    (hz : z′ = φ₂ (polyOfCodes (K₁ := K₁) ι A D d - C (φ (C c) * ev K₁ ι (En₂, Ed₂)))) :
    ∃ (c' : R) (P : ℕ → CPoly R × CPoly R),
      limitedPrimCodes En Ed Iη₁ Iη₂ A D d = some (c', P) ∧ ι c' = c ∧
        (z - ev₂ (K₁ := K₁) ι (φ₂ X) P (d + 1))′ = 0 := by
  -- the coefficient equations
  obtain ⟨-, p, hpe, hpd⟩ := coeffs_of_deriv_in_primitive (K := K₂) (ev K₁ ι (En, Ed)) hD₂ hconst₂
    (polyOfCodes (K₁ := K₁) ι A D d - C (φ (C c) * ev K₁ ι (En₂, Ed₂))) 0 1 squarefree_one
    (by simp) z (by rw [hz, map_zero, zero_div, add_zero])
  have hcoeffA : ∀ i, i ≤ d → (polyOfCodes (K₁ := K₁) ι A D d).coeff i =
      ev K₁ ι (A i, D i) := fun i hi ↦ by
    simp only [polyOfCodes, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_range.mpr (by omega)) h'
  have hdegA : (polyOfCodes (K₁ := K₁) ι A D d -
      C (φ (C c) * ev K₁ ι (En₂, Ed₂))).natDegree ≤ d := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by rw [natDegree_C]; exact Nat.zero_le _))
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp hi; omega)
  have hne : limitedPrim En Ed Iη₁ Iη₂ A D d ≠ none :=
    limitedPrim_complete (K := K₁) ι hD hKconst hcη₁ hcη₂ hEd hη0 A D d hD0 p c
      (fun i h1 h2 ↦ by
        have := hpe i
        rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero, hcoeffA i h2] at this
        exact this)
      (by
        have := hpe 0
        rw [coeff_sub, coeff_C, if_pos rfl, hcoeffA 0 (Nat.zero_le d)] at this
        simp only [Nat.cast_one, zero_add, one_mul] at this
        exact this)
      (hpd d hdegA).1
  have hsome : (limitedPrimCodes En Ed Iη₁ Iη₂ A D d).isSome = true := by
    rw [limitedPrimCodes_isSome]
    exact Option.isSome_iff_ne_none.mpr hne
  obtain ⟨⟨c', P⟩, hcP⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨c', P, hcP, ?_⟩
  have ht₁ : (φ₂ X)′ = algebraMap K₁ K₂ (ev K₁ ι (En, Ed)) := by
    rw [deriv_algebraMap, hD₂, implicitDeriv_X, IsScalarTower.algebraMap_apply K₁ K₁[X] K₂,
      Polynomial.algebraMap_eq]
  obtain ⟨-, hP'⟩ := limitedPrimCodes_sound_poly (K₁ := K₁) (K₂ := K₂) ι hD hcη₁ hcη₂ hEd (φ₂ X)
    ht₁ A D d hD0 hcP
  have hdiff : (z - ev₂ (K₁ := K₁) ι (φ₂ X) P (d + 1))′ =
      φ₂ (C (φ (C (ι c' - c)) * ev K₁ ι (En₂, Ed₂))) := by
    rw [map_sub, hz, hP', map_sub, map_polyOfCodes, IsScalarTower.algebraMap_apply K₁ K₁[X] K₂,
      Polynomial.algebraMap_eq, C_sub, map_sub, sub_mul, C_sub, map_sub]
    ring
  have hc : ι c' = c := by
    by_contra hne'
    exact hη₂nd _ (ι c' - c) (sub_ne_zero.mpr hne') hdiff
  refine ⟨hc, ?_⟩
  rw [hdiff, hc, sub_self, C_0, map_zero, zero_mul, C_0, map_zero]

end CPoly
