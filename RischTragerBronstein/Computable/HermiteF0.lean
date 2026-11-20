import RischTragerBronstein.Computable.Prim2StepGenF0
import RischTragerBronstein.Computable.GHermiteIn
import RischTragerBronstein.Computable.GResidueTest

/-!
# Hermite reduction of a fraction code, read in `F₀ = R(x₀)(t₁)`

For a fraction code `Gn / Gd` of `R(x)(t₁)` (`Gd ≠ 0`) the executable Hermite reduction followed
by a division gives, in any field `F₀ ⊇ R` containing `x₀` (`x₀′ = 1`) and a primitive `t₁`:

`Gn / Gd = (gn / gd)′ + q(t₁) + rem(t₁) / s(t₁)`

with `s` passing the squarefreeness and coprimality certificates and `rem` shorter than `s`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem hermite_valG_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    {Iη₁ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false) (Gn Gd : GPoly (GFrac R))
    (hGd : GPoly.isZero (ops₁g R) Gd = false) :
    valG x₀ t₁ (Gn, Gd) = (valG x₀ t₁ ((GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).gn, (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).gd))′ +
        (valP x₀ t₁ (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).b (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).s).1 + valP x₀ t₁ (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).b (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).s).2 / valP x₀ t₁ (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).s) ∧
      GPoly.squarefreeCheck (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).s = true ∧
      GPoly.coprimeDerivCheck (ops₁g R) [(En₁, Ed₁)] (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).s = true ∧
      (GPoly.trim (ops₁g R) (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).b (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).s).2).length < (GPoly.trim (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd).s).length := by
  classical
  generalize hh : GPoly.hermite (ops₁g R) [(En₁, Ed₁)] Gn Gd = h
  generalize hqr : GPoly.divMod (ops₁g R) h.b h.s = qr
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
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
  obtain ⟨hdec₁, hsq₁, hdeg₁⟩ :=
    rationalCheck_sound_map (K := R⟮x₀⟯) (RingHom.id R) hD En₁ Ed₁ Iη₁ hcη₁
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
  set M₁ := M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD with hM₁
  have hW : GPoly.toPoly M₁ [(En₁, Ed₁)] = C η₁' := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, sem_M₁In]
  have hD₁ : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) P := fun P ↦ by
    rw [hW]
    rfl
  have hD₁' : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (C η₁') P := fun P ↦ rfl
  have hconstP : ∀ P : (R⟮x₀⟯)[X], P′ = 0 → ∃ e : R⟮x₀⟯, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero η₁' hη₁nd (by rw [← hD₁', hP])
  have hnormal : ∀ p : (R⟮x₀⟯)[X], Irreducible p →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) p := fun p hp ↦ by
    rw [← hD₁]
    exact not_dvd_deriv_of_irreducible_primitive η₁' hD₁' hconstP hp
  have hGd0 : GPoly.toPoly M₁ Gd ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₁ Gd).mpr hz] at hGd
    exact Bool.noConfusion hGd
  have hchk := GPoly.hermiteCheck_hermite M₁ [(En₁, Ed₁)] Gn Gd (fun p hp _ ↦ hnormal p hp) hGd0
  rw [hh] at hchk
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (R⟮x₀⟯)⟮t₁⟯) M₁ [(En₁, Ed₁)] Gn Gd _
    hD₁ hchk
  have hS0 : GPoly.toPoly M₁ h.s ≠ 0 := hsq.ne_zero
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  have hlt := GPoly.divMod_remainder_lt M₁ h.b h.s fun hn ↦ hS0 ((GPoly.trim_eq_nil_iff M₁ _).mp hn)
  rw [hqr] at hdm hlt
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) (GPoly.toPoly M₁ h.s))
      (GPoly.toPoly M₁ h.s) := by
    rw [← hD₁]
    exact isCoprime_deriv_of_squarefree hsq fun p hp _ ↦
      not_dvd_deriv_of_irreducible_primitive η₁' hD₁' hconstP hp
  refine ⟨?_, GPoly.squarefreeCheck_complete M₁ hsq, GPoly.coprimeDerivCheck_complete M₁ hcop,
    hlt⟩
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly M₁ q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, hM₁, sem_M₁In, hevc]
  have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  have hφS : algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ h.s) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hS0
  have hid' : algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ Gn) /
      algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ Gd) =
      (algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ h.gn) /
        algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ h.gd))′ +
      (algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ qr.1) +
        algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ qr.2) /
          algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (GPoly.toPoly M₁ h.s)) := by
    rw [hid, hdm, map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one]
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hid'
  simp only [IntermediateField.coe_add, IntermediateField.coe_div, hderiv, hvalP] at this
  exact this

end Tower
