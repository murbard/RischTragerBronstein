import RischTragerBronstein.Computable.Prim2StepGenF0

/-!
# The remainder code of the `t₂`-loop, read in `F₀ = R(x₀)(t₁)`

`normF₂ (gCode k Ak Q)` has a non-zero denominator and the value
`Ak - (k + 1) η₂ Q` in `F₀`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem valG_gCode_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    {Iη₁ Iη₂ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GPoly.isZero (ops₁g R) (normF₂ (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q)).2 = false ∧
    valG x₀ t₁ (normF₂ (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q)) = valG x₀ t₁ Ak -
      ((k + 1 : ℕ) : F₀) * (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) * valG x₀ t₁ Q := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- level one: `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDA' : DifferentialAlgebra R⟮x₀⟯ F₀ :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hchar1 : CharZero R⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap R R⟮x₀⟯).injective
  have hD : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set η₁' : R⟮x₀⟯ := ev R⟮x₀⟯ (RingHom.id R) (En₁, Ed₁) with hη₁'
  set η₂' : R⟮x₀⟯ := ev R⟮x₀⟯ (RingHom.id R) (En₂, Ed₂) with hη₂'
  -- certified Hermite data over `R(x₀)`
  obtain ⟨hdec₁, hsq₁, hdeg₁⟩ :=
    rationalCheck_sound_map (K := R⟮x₀⟯) (RingHom.id R) hD En₁ Ed₁ Iη₁ hcη₁
  obtain ⟨hdec₂, hsq₂, hdeg₂⟩ :=
    rationalCheck_sound_map (K := R⟮x₀⟯) (RingHom.id R) hD En₂ Ed₂ Iη₂ hcη₂
  have hrη0 : (toPoly Iη₁.r).map (RingHom.id R) ≠ 0 := by
    rw [Polynomial.map_id, Ne, ← isZero_iff, hη₁0]
    exact Bool.noConfusion
  have hη₁nd : ∀ y : R⟮x₀⟯, y′ ≠ η₁' := fun y hy ↦ hrη0 <| by
    refine eq_zero_of_deriv_eq_proper_fraction (K := R⟮x₀⟯) hD _ _ hsq₁ hdeg₁
      (y - (algebraMap R[X] R⟮x₀⟯ ((toPoly Iη₁.gn).map (RingHom.id R)) /
        algebraMap R[X] R⟮x₀⟯ ((toPoly Iη₁.gd).map (RingHom.id R)) +
        algebraMap R[X] R⟮x₀⟯ ((toPoly Iη₁.Q).map (RingHom.id R)))) ?_
    rw [deriv_sub', hy, hη₁', ev, hdec₁]
    ring
  have hα : ∀ (c₀ : R) (d₀ : R⟮x₀⟯),
      η₂' ≠ algebraMap R[X] R⟮x₀⟯ (C c₀) * η₁' + d₀′ := by
    intro c₀ d₀ heq
    have hlim := (limited_integral_iff (K := R⟮x₀⟯) hD _ _ _ _ _ _ hsq₂ hsq₁ hdeg₂ hdeg₁ c₀).mp
      ⟨d₀, by
        have h2 : η₂' = _ := hdec₂
        have h1 : η₁' = _ := hdec₁
        rw [← h2, ← h1, heq]; ring⟩
    simp only [Polynomial.map_id] at hlim
    exact limitedCrit_complete hindep ⟨c₀, hlim⟩
  -- level two: `R(x₀)(t₁) ⊆ F₀`
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' := by rw [ht₁, hη₁', hevc]
  have htr1 : Transcendental R⟮x₀⟯ t₁ := transcendental_primitive η₁' ht₁' hη₁nd
  have hw1 : t₁′ = aeval t₁ (C η₁' : (R⟮x₀⟯)[X]) := by rw [aeval_C, ht₁']
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁')
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁') hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁') hw1
  have hST : IsScalarTower R⟮x₀⟯ (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      apply Subtype.ext
      rw [Polynomial.algebraMap_eq, algebraMap_adjoinSimple, aeval_C]
      rfl
  have hDA12 : DifferentialAlgebra R⟮x₀⟯ (R⟮x₀⟯)⟮t₁⟯ := ⟨fun a ↦ Subtype.ext rfl⟩
  have hM : Model2 (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) En₁ Ed₁ En₂ Ed₂ :=
    Model2.of (RingHom.id R) hD (fun _ ↦ rfl) hη₁nd hα
  have hEd₁ : toPoly Ed₁ ≠ 0 := by
    have hc := hcη₁
    rw [rationalCheck, Bool.and_eq_true] at hc
    exact ((hermiteCheck_iff _ _ _).mp hc.1).1
  -- values of codes in `F₀`
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hsemG : ∀ q : GFrac (GFrac R),
      (((M₂In (RingHom.id R) h0 hM).sem q : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valG x₀ t₁ q := fun q ↦ by
    rw [sem_M₂In, IntermediateField.coe_div, hvalP, hvalP, valG]
  obtain ⟨hden, hsem⟩ := normF₂_spec (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hM
    (gCode En₁ Ed₁ En₂ Ed₂ k Ak Q)
  refine ⟨Bool.eq_false_iff.mpr fun hz ↦ hden ((GPoly.isZero_iff _ _).mp hz), ?_⟩
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀))
    (hsem.trans (sem_gCode (RingHom.id R) h0 hM k Ak Q))
  have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  have hnat : (((k + 1 : ℕ) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = ((k + 1 : ℕ) : F₀) := by
    rw [← map_natCast (algebraMap (R⟮x₀⟯)⟮t₁⟯ F₀)]; rfl
  have hη₂F : ((algebraMap R⟮x₀⟯ (R⟮x₀⟯)⟮t₁⟯ η₂' : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂) := hevc (En₂, Ed₂)
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsemG, hnat] at this
  rw [this]
  congr 3

end Tower
