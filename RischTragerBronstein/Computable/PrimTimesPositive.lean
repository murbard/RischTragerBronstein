import RischTragerBronstein.Computable.LimitedCrit
import RischTragerBronstein.Computable.LogTimesPositive

/-!
# `∫ f(x) t dx` for a primitive `t` over `R(x)`: the positive answer

`hasElementaryIntegral_primTimes`: with `x′ = 1`, `t′ = η(x) = En / Ed`, certified Hermite data for
`f = A / D` and for `η`, if `limitedCrit` returns `some c` — so that `f - c η = p₁′` with
`p₁ = G_f - c G_η ∈ R(x)` — then `f t` has an elementary integral over `K`:

  `f t = (p₁ t + (c / 2) t²)′ - p₁ η`,

and `p₁ η` is a rational function of `x` (`hasElementaryIntegral_rational_in`).

Together with `not_hasElementaryIntegral_primTimes` this decides `∫ f(x) log b(x) dx`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [Field K] [Differential K] [Algebra R K] [DifferentialAlgebra R K]

theorem hasElementaryIntegral_primTimes (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (En Ed : CPoly R) (ht : t′ = aeval x (toPoly En) / aeval x (toPoly Ed))
    (A D : CPoly R) (If Iη : RationalIntegral R) (hcf : rationalCheck A D If = true)
    (hcη : rationalCheck En Ed Iη = true) {c : R}
    (hcrit : limitedCrit If.r If.s Iη.r Iη.s = some c) :
    HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap R K).injective
  have htr : Transcendental R x :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx]; exact one_ne_zero)
  have hinjx : Function.Injective (aeval x : R[X] →ₐ[R] K) := transcendental_iff_injective.mp htr
  have hw : x′ = aeval x (1 : R[X]) := by rw [hx, map_one]
  let _ := algebraAdjoinSimple (F := R) x
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x 1 hw)
  have hFR : IsFractionRing R[X] R⟮x⟯ := isFractionRing_adjoin_simple x htr
  have hDA : DifferentialAlgebra R[X] R⟮x⟯ := differentialAlgebra_adjoin_simple x 1 hw
  have hDpoly : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x⟯ P : R⟮x⟯) : K) = aeval x P :=
    algebraMap_adjoinSimple x
  -- certified decompositions of `f` and `η`, transported to `K`
  have hdecK : ∀ (A' D' : CPoly R) (I : RationalIntegral R), rationalCheck A' D' I = true →
      toPoly I.gd ≠ 0 ∧ toPoly I.s ≠ 0 ∧
      aeval x (toPoly A') / aeval x (toPoly D') =
        (aeval x (toPoly I.gn) / aeval x (toPoly I.gd) + aeval x (toPoly I.Q))′ +
          aeval x (toPoly I.r) / aeval x (toPoly I.s) := by
    intro A' D' I hI
    obtain ⟨hdec, hsq, -⟩ := rationalCheck_sound_map (K := R⟮x⟯) (RingHom.id R) hDpoly A' D' I hI
    simp only [Polynomial.map_id] at hdec hsq
    have hgd : toPoly I.gd ≠ 0 := by
      simp only [rationalCheck, hermiteCheck, Bool.and_eq_true, Bool.not_eq_true',
        ← Bool.not_eq_true, isZero_iff] at hI
      exact hI.1.1.1.1.2
    refine ⟨hgd, hsq.ne_zero, ?_⟩
    have := congrArg (fun y : R⟮x⟯ ↦ (y : K)) hdec
    simp only [IntermediateField.coe_div, IntermediateField.coe_add, hcoe] at this
    rw [this]
    congr 1
    simp only [← hcoe, ← IntermediateField.coe_div, ← IntermediateField.coe_add]
    rfl
  obtain ⟨hgdf, hsf0, hf⟩ := hdecK A D If hcf
  obtain ⟨hgdη, hsη0, hη⟩ := hdecK En Ed Iη hcη
  have hne : ∀ {P : R[X]}, P ≠ 0 → aeval x P ≠ 0 := fun hP ↦ (map_ne_zero_iff (aeval x) hinjx).mpr hP
  -- the limited-integration identity
  have hcross := limitedCrit_sound hcrit
  have hrs : aeval x (toPoly If.r) / aeval x (toPoly If.s) =
      algebraMap R K c * (aeval x (toPoly Iη.r) / aeval x (toPoly Iη.s)) := by
    have := congrArg (aeval x) hcross
    simp only [map_mul, aeval_C] at this
    have h1 := hne hsf0
    have h2 := hne hsη0
    field_simp
    linear_combination this
  set Gf : K := aeval x (toPoly If.gn) / aeval x (toPoly If.gd) + aeval x (toPoly If.Q) with hGf
  set Gη : K := aeval x (toPoly Iη.gn) / aeval x (toPoly Iη.gd) + aeval x (toPoly Iη.Q) with hGη
  set η : K := aeval x (toPoly En) / aeval x (toPoly Ed) with hηdef
  have hcc : (algebraMap R K c)′ = 0 := by rw [deriv_algebraMap, h0, map_zero]
  set γ : K := algebraMap R K (c / 2) with hγ
  have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, h0, map_zero]
  have hγ2 : γ * 2 = algebraMap R K c := by
    rw [hγ, map_div₀, map_ofNat]
    exact div_mul_cancel₀ _ two_ne_zero
  set p₁ : K := Gf - algebraMap R K c * Gη with hp₁
  have hp₁' : p₁′ = aeval x (toPoly A) / aeval x (toPoly D) - algebraMap R K c * η := by
    rw [hp₁, map_sub, Derivation.leibniz, hcc, hf, hη, hrs]
    simp only [smul_eq_mul]
    ring
  set W : K := p₁ * t + γ * (t * t) with hW
  have hW' : W′ = aeval x (toPoly A) / aeval x (toPoly D) * t + p₁ * η := by
    rw [hW, map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz, hγ', ht, hp₁',
      ← hγ2]
    simp only [smul_eq_mul]
    ring
  -- `p₁ η` as a single fraction of polynomials in `x`
  have hp₁η : p₁ * η =
      aeval x (((toPoly If.gn + toPoly If.Q * toPoly If.gd) * toPoly Iη.gd -
          C c * (toPoly Iη.gn + toPoly Iη.Q * toPoly Iη.gd) * toPoly If.gd) * toPoly En) /
        aeval x (toPoly If.gd * toPoly Iη.gd * toPoly Ed) := by
    have h1 := hne hgdf
    have h2 := hne hgdη
    rw [hp₁, hGf, hGη, hηdef]
    simp only [map_mul, map_sub, map_add, aeval_C]
    by_cases hEd : aeval x (toPoly Ed) = 0
    · simp [hEd]
    · field_simp
  have hform : aeval x (toPoly A) / aeval x (toPoly D) * t =
      W′ + aeval x (-(((toPoly If.gn + toPoly If.Q * toPoly If.gd) * toPoly Iη.gd -
          C c * (toPoly Iη.gn + toPoly Iη.Q * toPoly Iη.gd) * toPoly If.gd) * toPoly En)) /
        aeval x (toPoly If.gd * toPoly Iη.gd * toPoly Ed) := by
    rw [hW', map_neg, neg_div, ← hp₁η]
    ring
  rw [hform]
  by_cases hEd0 : toPoly Ed = 0
  · -- degenerate `η = 0`: the fraction is `0`
    rw [hEd0, mul_zero, map_zero, div_zero, add_zero]
    exact hasElementaryIntegral_of_deriv W
  · exact hasElementaryIntegral_rational_in h0 x hx _ _
      (mul_ne_zero (mul_ne_zero hgdf hgdη) hEd0) W

end CPoly
