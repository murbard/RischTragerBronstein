import RischTragerBronstein.Algebraic.SupDecideAll

/-!
# A superelliptic curve with `n ∣ deg f`, decided end to end

On the Fermat cubic `y³ = x³ + 1` (`n = deg f = 3`: three places at infinity, not a branch point),
`superDecideAll` moves the branch point `x = −1` to infinity and decides:
`∫ x² y/(x³ + 1) dx = ∫ x²/y² dx` is elementary (it is `y`), `∫ ∛(x³ + 1) dx` is not.
-/

open Polynomial Differential CPoly IntermediateField Jac

namespace Sup

namespace DecideAllExample

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

lemma toPoly_f : toPoly ([1, 0, 0, 1] : CPoly ℚ) = X ^ 3 + 1 := by simp [CPoly.toPoly]; ring

lemma sqf : Squarefree (toPoly ([1, 0, 0, 1] : CPoly ℚ)) := by
  rw [toPoly_f]
  refine Polynomial.Separable.squarefree ⟨1, C (-1 / 3 : ℚ) * X, ?_⟩
  refine Polynomial.funext fun r ↦ ?_
  simp; ring

lemma degf : (toPoly ([1, 0, 0, 1] : CPoly ℚ)).natDegree = ([1, 0, 0, 1] : CPoly ℚ).length - 1 := by
  rw [toPoly_f]; simp

/-- The field built for both integrands is `ℚ[θ]/(θ² + θ + 1)`. -/
lemma fldA : (buildFieldMob ([1, 0, 0, 1] : CPoly ℚ) (nbPartK ([1, 0, 0, 1] : CPoly ℚ) [1, 0, 0, 1])
    3 4).map PSigma.fst = some [1, 1, 1] := by
  decide +kernel

lemma fldB : (buildFieldMob ([1, 0, 0, 1] : CPoly ℚ) (nbPartK ([1, 0, 0, 1] : CPoly ℚ) [1]) 3 4).map
    PSigma.fst = some [1, 1, 1] := by
  decide +kernel

lemma irr : Kron.irredQ ([1, 1, 1] : CPoly ℚ) = true := by decide +kernel

lemma runA : @superDecideMobM [1, 1, 1] ⟨Kron.irredQ_sound _ irr⟩ [1, 0, 0, 1] 3 [[], [0, 0, 1]]
    [1, 0, 0, 1] 30 = some true := by
  decide +kernel

lemma runB : @superDecideMobM [1, 1, 1] ⟨Kron.irredQ_sound _ irr⟩ [1, 0, 0, 1] 3 [[], [1]] [1] 30 =
    some false := by
  decide +kernel

lemma hyf {x y : E} (hy : y ^ 3 = x ^ 3 + 1) :
    y ^ 3 = aeval x ((toPoly ([1, 0, 0, 1] : CPoly ℚ)).map (algebraMap ℚ Kc)) := by
  rw [toPoly_f, hy]; simp

/-- **`∫ x²/y² dx = ∫ x² y/(x³ + 1) dx` is elementary** on `y³ = x³ + 1`. -/
theorem sq_over_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 3 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    HasElementaryIntegral (x ^ 2 * y / (x ^ 3 + 1)) := by
  have h := superDecideAll_spec hC x y hx [1, 0, 0, 1] (n := 3) (by norm_num) sqf degf (by decide)
    (hyf (Kc := Kc) hy) hgen [[], [0, 0, 1]] [1, 0, 0, 1] (by rw [toPoly_f]; exact X_pow_add_C_ne_zero (by norm_num) _) 30 4 true
    (by
      rw [superDecideAll, if_neg (by decide), if_pos (by decide), superDecideMobQ_eq irr fldA]
      exact runA)
  have e := h.mp rfl
  convert e using 1
  simp [Finset.sum_range_succ, CPoly.toPoly]
  ring

/-- **`∫ ∛(x³ + 1) dx` is not elementary.** -/
theorem cbrt_not_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 3 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) : ¬HasElementaryIntegral y := by
  have h := superDecideAll_spec hC x y hx [1, 0, 0, 1] (n := 3) (by norm_num) sqf degf (by decide)
    (hyf (Kc := Kc) hy) hgen [[], [1]] [1] (by simp [CPoly.toPoly]) 30 4 false
    (by
      rw [superDecideAll, if_neg (by decide), if_pos (by decide), superDecideMobQ_eq irr fldB]
      exact runB)
  simp only [Bool.false_eq_true, false_iff] at h
  convert h using 2
  simp [Finset.sum_range_succ, CPoly.toPoly]

end DecideAllExample

end Sup
