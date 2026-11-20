import RischTragerBronstein.Computable.LogCritDecide
import RischTragerBronstein.Rational.IntegrableIn

/-!
# `∫ f(x) log x dx`: the positive answer

`hasElementaryIntegral_logTimes`: in a differential field `K ⊇ R` (constants) with `x′ = 1`,
`t′ = 1 / x`, if the certified Hermite data `f = G′ + r / s` of `f ∈ R(x)` satisfies `LogCrit r s`
— so that `r / s = c / x` for a constant `c` — then `f t` has an elementary integral over `K`:

  `f t = (G t + (c / 2) t²)′ - G / x`,

and `G / x` is a rational function of `x`, integrable over `K` by
`hasElementaryIntegral_rational_in`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [Field K] [Differential K] [Algebra R K] [DifferentialAlgebra R K]

theorem hasElementaryIntegral_logTimes (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (ht : t′ = x⁻¹) (A D : CPoly R) (I : RationalIntegral R)
    (hc : rationalCheck A D I = true) (hcrit : LogCrit (toPoly I.r) (toPoly I.s)) :
    HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  have hx0 : x ≠ 0 := fun h ↦ by rw [h, map_zero] at hx; exact zero_ne_one hx
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
  -- the certified decomposition, in `R(x) ⊆ K`
  obtain ⟨hdec, hsq, -⟩ := rationalCheck_sound_map (K := R⟮x⟯) (RingHom.id R) hDpoly A D I hc
  simp only [Polynomial.map_id] at hdec hsq
  have hgd : toPoly I.gd ≠ 0 := by
    simp only [rationalCheck, hermiteCheck, Bool.and_eq_true, Bool.not_eq_true',
      ← Bool.not_eq_true, isZero_iff] at hc
    exact hc.1.1.1.1.2
  set G : K := aeval x (toPoly I.gn) / aeval x (toPoly I.gd) + aeval x (toPoly I.Q) with hG
  have hdecK : aeval x (toPoly A) / aeval x (toPoly D) =
      G′ + aeval x (toPoly I.r) / aeval x (toPoly I.s) := by
    have := congrArg (fun y : R⟮x⟯ ↦ (y : K)) hdec
    simp only [IntermediateField.coe_div, IntermediateField.coe_add, hcoe] at this
    rw [this, hG]
    congr 1
    simp only [← hcoe, ← IntermediateField.coe_div, ← IntermediateField.coe_add]
    rfl
  -- `r / s = c / x`
  obtain ⟨c, hrs⟩ : ∃ c : R, aeval x (toPoly I.r) / aeval x (toPoly I.s) =
      algebraMap R K c * x⁻¹ := by
    rcases hcrit with ⟨s', c, hs, hr⟩ | hr0
    · have hs'0 : aeval x s' ≠ 0 := (map_ne_zero_iff (aeval x) hinjx).mpr fun h ↦
        hsq.ne_zero (by rw [hs, h, mul_zero])
      refine ⟨c, ?_⟩
      rw [hr, hs, map_mul, map_mul, aeval_C, aeval_X]
      field_simp
    · exact ⟨0, by rw [hr0, map_zero, zero_div, map_zero, zero_mul]⟩
  set γ : K := algebraMap R K (c / 2) with hγ
  have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, h0, map_zero]
  have hγ2 : γ * 2 = algebraMap R K c := by
    rw [hγ, map_div₀, map_ofNat]
    have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap R K).injective
    exact div_mul_cancel₀ _ two_ne_zero
  -- `f t = W′ - G / x`
  set W : K := G * t + γ * (t * t) with hW
  have hW' : W′ = aeval x (toPoly A) / aeval x (toPoly D) * t + G * x⁻¹ := by
    rw [hW, map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz, hγ', ht, hdecK,
      hrs, ← hγ2]
    simp only [smul_eq_mul]
    ring
  have hGx : G * x⁻¹ = aeval x (toPoly I.gn + toPoly I.Q * toPoly I.gd) /
      aeval x (toPoly I.gd * X) := by
    have hgdx : aeval x (toPoly I.gd) ≠ 0 := (map_ne_zero_iff (aeval x) hinjx).mpr hgd
    rw [hG, map_add, map_mul, map_mul, aeval_X]
    field_simp
  have hform : aeval x (toPoly A) / aeval x (toPoly D) * t =
      W′ + aeval x (-(toPoly I.gn + toPoly I.Q * toPoly I.gd)) / aeval x (toPoly I.gd * X) := by
    rw [hW', map_neg, neg_div, ← hGx]
    ring
  rw [hform]
  exact hasElementaryIntegral_rational_in h0 x hx _ _ (mul_ne_zero hgd X_ne_zero) W

end CPoly
