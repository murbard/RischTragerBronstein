import RischTragerBronstein.Algebraic.SupDecideQ

/-!
# Superelliptic integrals with rational data, decided end to end

`superDecideQ` builds the number field itself (here `ℚ(ζ₃)` for `n = 3`) and the kernel runs the
whole procedure:

on `y³ = x² + 1`: `∫ ∛(x² + 1)/x dx` is elementary, `∫ ∛(x² + 1) dx` is not. The kernel first
computes the field (`superDecideQ_eq`: it is `ℚ[θ]/(θ² + θ + 1)`), then runs `superDecideM` over it.
-/

open Polynomial Differential CPoly IntermediateField Jac

namespace Sup

namespace DecideQExample

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

lemma sq3 : Squarefree (toPoly ([1, 0, 1] : CPoly ℚ)) := by
  have : toPoly ([1, 0, 1] : CPoly ℚ) = X ^ 2 + 1 := by simp [CPoly.toPoly]; ring
  rw [this]
  refine Polynomial.Separable.squarefree ⟨1, -(Polynomial.C (1 / 2 : ℚ)) * X, ?_⟩
  refine Polynomial.funext fun r ↦ ?_
  simp; ring

lemma deg3 : (toPoly ([1, 0, 1] : CPoly ℚ)).natDegree = ([1, 0, 1] : CPoly ℚ).length - 1 := by
  have : toPoly ([1, 0, 1] : CPoly ℚ) = X ^ 2 + 1 := by simp [CPoly.toPoly]; ring
  rw [this]; simp

/-- The field built by `superDecideQ` (for `n = 3`, `D = x` and `D = 1`) is `ℚ[θ]/(θ² + θ + 1)`. -/
lemma fld : (buildField ([1, 0, 1] : CPoly ℚ) (nbPartK ([1, 0, 1] : CPoly ℚ) [0, 1]) 3 4).map
    PSigma.fst = some [1, 1, 1] := by
  decide +kernel

lemma fld2 : (buildField ([1, 0, 1] : CPoly ℚ) (nbPartK ([1, 0, 1] : CPoly ℚ) [1]) 3 4).map
    PSigma.fst = some [1, 1, 1] := by
  decide +kernel

lemma irr : Kron.irredQ ([1, 1, 1] : CPoly ℚ) = true := by decide +kernel

lemma run1 : @superDecideM [1, 1, 1] ⟨Kron.irredQ_sound _ irr⟩ [1, 0, 1] 3 [[], [1]] [0, 1] 30 =
    some true := by
  decide +kernel

lemma run2 : @superDecideM [1, 1, 1] ⟨Kron.irredQ_sound _ irr⟩ [1, 0, 1] 3 [[], [1]] [1] 30 =
    some false := by
  decide +kernel

/-- **`∫ ∛(x² + 1)/x dx` is elementary.** -/
theorem cbrt_over_x (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (hy : y ^ 3 = x ^ 2 + 1)
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) : HasElementaryIntegral (y / x) := by
  have h := superDecideQ_spec hC x y hx [1, 0, 1] (n := 3) (by norm_num) sq3 deg3 (by decide) (by decide)
    (by simp [CPoly.toPoly, hy]; ring) hgen [[], [1]] [0, 1] (by simp [CPoly.toPoly]) 30 4 true
    ((superDecideQ_eq irr fld).trans run1)
  have e := h.mp rfl
  convert e using 1
  simp [Finset.sum_range_succ, CPoly.toPoly, div_eq_inv_mul]

/-- **`∫ ∛(x² + 1) dx` is not elementary.** -/
theorem cbrt_self (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (hy : y ^ 3 = x ^ 2 + 1)
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) : ¬HasElementaryIntegral y := by
  have h := superDecideQ_spec hC x y hx [1, 0, 1] (n := 3) (by norm_num) sq3 deg3 (by decide) (by decide)
    (by simp [CPoly.toPoly, hy]; ring) hgen [[], [1]] [1] (by simp [CPoly.toPoly]) 30 4 false
    ((superDecideQ_eq irr fld2).trans run2)
  simp only [Bool.false_eq_true, false_iff] at h
  convert h using 2
  simp [Finset.sum_range_succ, CPoly.toPoly]

end DecideQExample

end Sup
