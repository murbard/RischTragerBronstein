import RischTragerBronstein.Computable.Prim2StepGenF0

/-!
# The general `t₂`-loop: the explicit antiderivative

If `prim2LoopGen` returns `L`, then with the explicit `W = prim2WGen … L ∈ K`

  `Q′ t₂ ^ (k + 1) + ∑_{j ≤ k} Aⱼ t₂ ^ j = W′ + (A₀ - η₂ Q₁)`,

for coefficients `Aⱼ` that are arbitrary elements of `R(x)(t₁)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]

/-- The closed-form part of the antiderivative, read off from the output of `prim2Loop`. -/
noncomputable def prim2WGen (x₀ t₁ : F₀) (t : K) :
    ℕ → GFrac (GFrac R) → List (R × GFrac (GFrac R)) → K
  | _, Q, [] => algebraMap F₀ K (valG x₀ t₁ Q) * t
  | m, Q, cQ :: L =>
    (algebraMap F₀ K (valG x₀ t₁ Q) + algebraMap F₀ K (algebraMap R F₀ (cQ.1 / (m : R)))) * t ^ m +
      prim2WGen x₀ t₁ t (m - 1) cQ.2 L

/-- **The result is an antiderivative** (height three, polynomial part). -/
theorem prim2LoopGen_antiderivative (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁)) (t : K)
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    {Iη₁ Iη₂ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (A : ℕ → GFrac (GFrac R)) (k : ℕ)
    (Q : GFrac (GFrac R)) {L : List (R × GFrac (GFrac R))}
    (hL : prim2LoopGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A k Q = some L) :
      (algebraMap F₀ K (valG x₀ t₁ Q))′ * t ^ (k + 1) +
          ∑ j ∈ Finset.range (k + 1), algebraMap F₀ K (valG x₀ t₁ (A j)) * t ^ j =
        (prim2WGen x₀ t₁ t (k + 1) Q L)′ + (algebraMap F₀ K (valG x₀ t₁ (A 0)) -
          algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) *
            algebraMap F₀ K (valG x₀ t₁ (lastGen Q L))) := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap F₀ K).injective
  induction k generalizing Q L with
  | zero =>
    simp only [prim2LoopGen, Option.some.injEq] at hL
    subst hL
    rw [prim2WGen, lastGen, Derivation.leibniz, ht]
    simp only [smul_eq_mul, zero_add, pow_one, Finset.range_one, Finset.sum_singleton, pow_zero,
      mul_one]
    ring
  | succ k ih =>
    simp only [prim2LoopGen] at hL
    cases hstep : prim2StepGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ (k + 1) (A (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      obtain ⟨c, Q'⟩ := cQ
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      have hsol := prim2StepGen_sound_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hcη₂ hη₁0 hindep (k + 1)
        (A (k + 1)) Q hstep
      have hrec := ih Q' hL'
      set γ : K := algebraMap F₀ K (algebraMap R F₀ (c / ((k + 1 + 1 : ℕ) : R))) with hγ
      have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, hR, map_zero]
      have hγc : ((k + 1 + 1 : ℕ) : K) * γ = algebraMap F₀ K (algebraMap R F₀ c) := by
        rw [hγ, map_div₀, map_div₀, map_natCast, map_natCast]
        exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
      set q : K := algebraMap F₀ K (valG x₀ t₁ Q) with hq
      set η₂ : K := algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) with hη₂
      have hX : ((q + γ) * t ^ (k + 1 + 1))′ = q′ * t ^ (k + 1 + 1) +
          ((k + 1 + 1 : ℕ) : K) * (q + γ) * η₂ * t ^ (k + 1) := by
        rw [Derivation.leibniz, map_add, hγ', Derivation.leibniz_pow, ht]
        simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, add_zero]
        ring
      have hW : prim2WGen x₀ t₁ t (k + 1 + 1) Q ((c, Q') :: L') =
          (q + γ) * t ^ (k + 1 + 1) + prim2WGen x₀ t₁ t (k + 1) Q' L' := rfl
      have hsolK := congrArg (algebraMap F₀ K) hsol
      rw [← deriv_algebraMap] at hsolK
      simp only [map_sub, map_mul, map_natCast] at hsolK
      rw [hW, lastGen, map_add, hX, Finset.sum_range_succ _ (k + 1)]
      linear_combination hrec - t ^ (k + 1) * hsolK - η₂ * t ^ (k + 1) * hγc

end Tower
