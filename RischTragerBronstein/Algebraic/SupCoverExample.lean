import RischTragerBronstein.Algebraic.SupCover

/-!
# A superelliptic curve with `1 < gcd(n, deg f) < n`, decided through a cover

On `y⁴ = x² − 1` (`gcd(4, 2) = 2`: two places over infinity, each ramified of index `2`),
`superDecideSup` passes to the cover `s² = x` (`k = 2`, `c = 0`), where the curve is
`y⁴ = s⁴ − 1`, moves a branch point to infinity and decides over `ℚ(i)`:
`∫ x y/(2x² − 2) dx` is elementary (it is `y`), `∫ ∜(x² − 1) dx` is not.
-/

open Polynomial Differential CPoly IntermediateField Jac

namespace Sup

namespace CoverExample

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

lemma toPoly_f : toPoly ([-1, 0, 1] : CPoly ℚ) = X ^ 2 - 1 := by simp [CPoly.toPoly]; ring

lemma sqf : Squarefree (toPoly ([-1, 0, 1] : CPoly ℚ)) := by
  rw [toPoly_f]
  refine Polynomial.Separable.squarefree ⟨-1, C (1 / 2 : ℚ) * X, ?_⟩
  refine Polynomial.funext fun r ↦ ?_
  simp; ring

lemma degf : (toPoly ([-1, 0, 1] : CPoly ℚ)).natDegree = ([-1, 0, 1] : CPoly ℚ).length - 1 := by
  rw [toPoly_f, show (X ^ 2 - 1 : ℚ[X]) = X ^ 2 - C 1 by simp, natDegree_X_pow_sub_C]; rfl

lemma hcov : coverC ([-1, 0, 1] : CPoly ℚ) = 0 ∧ coverK ([-1, 0, 1] : CPoly ℚ) 4 = 2 := by
  decide +kernel

lemma hg : compShiftPow ([-1, 0, 1] : CPoly ℚ) 0 2 = [-1, 0, 0, 0, 1] := by decide +kernel

/-- The field for both integrands is `ℚ(i) = ℚ[θ]/(θ² + 1)`. -/
lemma fldA : (buildFieldMob ([-1, 0, 0, 0, 1] : CPoly ℚ)
    (nbPartK ([-1, 0, 0, 0, 1] : CPoly ℚ) (compShiftPow ([-2, 0, 2] : CPoly ℚ) 0 2)) 4 4).map
      PSigma.fst = some [1, 0, 1] := by
  decide +kernel

lemma fldB : (buildFieldMob ([-1, 0, 0, 0, 1] : CPoly ℚ)
    (nbPartK ([-1, 0, 0, 0, 1] : CPoly ℚ) (compShiftPow ([1] : CPoly ℚ) 0 2)) 4 4).map
      PSigma.fst = some [1, 0, 1] := by
  decide +kernel

lemma irr : Kron.irredQ ([1, 0, 1] : CPoly ℚ) = true := by decide +kernel

lemma runA : @superDecideMobM [1, 0, 1] ⟨Kron.irredQ_sound _ irr⟩ [-1, 0, 0, 0, 1] 4
    ([[], [0, 1]].map (coverNum 0 2)) (compShiftPow ([-2, 0, 2] : CPoly ℚ) 0 2) 60 = some true := by
  decide +kernel

lemma runB : @superDecideMobM [1, 0, 1] ⟨Kron.irredQ_sound _ irr⟩ [-1, 0, 0, 0, 1] 4
    ([[], [1]].map (coverNum 0 2)) (compShiftPow ([1] : CPoly ℚ) 0 2) 60 = some false := by
  decide +kernel

lemma hyf {x y : E} (hy : y ^ 4 = x ^ 2 - 1) :
    y ^ 4 = aeval x ((toPoly ([-1, 0, 1] : CPoly ℚ)).map (algebraMap ℚ Kc)) := by
  rw [toPoly_f, hy]; simp

lemma dispatch (A : List (CPoly ℚ)) (D : CPoly ℚ) (B fuel : ℕ) :
    superDecideSup [-1, 0, 1] 4 A D B fuel =
      superDecideMobQ [-1, 0, 0, 0, 1] 4 (A.map (coverNum 0 2)) (compShiftPow D 0 2) B fuel := by
  rw [superDecideSup, if_neg (by decide), if_neg (by decide), superDecideCover, hcov.1, hcov.2, hg]

/-- **`∫ x y/(2x² − 2) dx` is elementary** on `y⁴ = x² − 1`. -/
theorem xy_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 4 = x ^ 2 - 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    HasElementaryIntegral (x * y / (2 * x ^ 2 - 2)) := by
  have h := superDecideSup_spec hC x y hx [-1, 0, 1] (n := 4) (by norm_num) sqf degf (by decide)
    (hyf (Kc := Kc) hy) hgen [[], [0, 1]] [-2, 0, 2] (by
      intro h0
      have := congrArg (fun p : ℚ[X] ↦ p.coeff 2) h0
      simp [CPoly.toPoly] at this) 60 4 true
    (by rw [dispatch, superDecideMobQ_eq irr fldA]; exact runA)
  have e := h.mp rfl
  convert e using 1
  simp [Finset.sum_range_succ, CPoly.toPoly]
  rw [show (algebraMap Kc E) 2 = 2 from map_ofNat _ 2]
  ring

/-- **`∫ ∜(x² − 1) dx` is not elementary.** -/
theorem fourth_root_not_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 4 = x ^ 2 - 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) : ¬HasElementaryIntegral y := by
  have h := superDecideSup_spec hC x y hx [-1, 0, 1] (n := 4) (by norm_num) sqf degf (by decide)
    (hyf (Kc := Kc) hy) hgen [[], [1]] [1] (by simp [CPoly.toPoly]) 60 4 false
    (by rw [dispatch, superDecideMobQ_eq irr fldB]; exact runB)
  simp only [Bool.false_eq_true, false_iff] at h
  convert h using 2
  simp [Finset.sum_range_succ, CPoly.toPoly]

end CoverExample

end Sup
