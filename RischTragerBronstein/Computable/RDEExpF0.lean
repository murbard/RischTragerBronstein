import RischTragerBronstein.Computable.ExpExpBasics
import RischTragerBronstein.Computable.Prim2StepGenF0

/-!
# `rdeExp` read in an abstract field `F₀ = R(x₀)(exp a)`

`rdeExp_sound_F₀`: the solution `Y / (t₁^m D₁)` returned by `rdeExp`, evaluated with `valP`, solves
`y′ + g y = A / (t₁^m D₁)` in any differential field `F₀ ⊇ R` containing `x₀` (`x₀′ = 1`) and
`t₁ ≠ 0` with `t₁′ = a′(x₀) t₁`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem rdeExp_sound_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a : CPoly R) (ha : trim (deriv a) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a)) * t₁)
    (g : CPoly R) (A D₁ : GPoly (GFrac R)) (m : ℕ)
    (hD0 : GPoly.isZero (ops₁g R) D₁ = false) {Y : GPoly (GFrac R)}
    (h : rdeExp a g A D₁ m = some Y) :
    (valP x₀ t₁ Y / (t₁ ^ m * valP x₀ t₁ D₁))′ +
        aeval x₀ (toPoly g) * (valP x₀ t₁ Y / (t₁ ^ m * valP x₀ t₁ D₁)) =
      valP x₀ t₁ A / (t₁ ^ m * valP x₀ t₁ D₁) := by
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
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (derivative (toPoly a)) with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (derivative (toPoly a)) := hcoe _
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have hA'0 : derivative (toPoly a) ≠ 0 := fun h' ↦ ha ((trim_eq_nil_iff _).mpr (by
    rw [toPoly_deriv, h']))
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := R⟮x₀⟯) hD (-(C (n : R) * derivative (toPoly a)))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap R[X] R⟮x₀⟯ (C (n : R)) = (n : R⟮x₀⟯) := by
          rw [show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hηa : ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a = η₁' := by
    rw [ηa, Polynomial.map_id]
  have hD₂ : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (C (ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hD0' : GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) D₁ ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) D₁).mpr hz] at hD0
    exact Bool.noConfusion hD0
  have hsound := rdeExp_sound (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hD a hD₂ g A D₁
    m hD0' h
  -- values of codes in `F₀`
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hXF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ X : (R⟮x₀⟯)⟮t₁⟯) : F₀) = t₁ := by
    rw [algebraMap_adjoinSimple, aeval_X]
  have hgF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (C (algebraMap R[X] R⟮x₀⟯ ((toPoly g).map (RingHom.id R)))) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      aeval x₀ (toPoly g) := by
    rw [algebraMap_adjoinSimple, aeval_C, Polynomial.map_id]
    exact hcoe _
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsound
  have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  simp only [hderiv, IntermediateField.coe_add, IntermediateField.coe_div, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, hvalP, hgF, hXF] at this
  exact this

end Tower
