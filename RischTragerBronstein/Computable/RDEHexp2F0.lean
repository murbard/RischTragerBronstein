import RischTragerBronstein.Computable.RDEHexp2Complete
import RischTragerBronstein.Computable.Prim2StepGenF0

/-!
# `rdeHexp₂` read in an abstract field `F₀ = R(x₀)(t₁)`, `t₁′ = η t₁`

`rdeHexp₂_sound_F₀`: the solution `Y / (t₁^m D₁)` returned by `rdeHexp₂` (rational coefficient `g = Gn / Gd`), evaluated with `valP`, solves
`y′ + g y = A / (t₁^m D₁)` in any differential field `F₀ ⊇ R` containing `x₀` (`x₀′ = 1`) and
`t₁ ≠ 0` with `t₁′ = η(x₀) t₁`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀] [CPoly.HasRatRoots R] [HasNatTest R]

set_option maxHeartbeats 1600000 in
theorem rdeHexp₂_sound_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁)
    (Gn Gd : CPoly R) (hGd0 : toPoly Gd ≠ 0) (A D₁ : GPoly (GFrac R)) (m : ℕ)
    (hD0 : GPoly.isZero (ops₁g R) D₁ = false) {Y : GPoly (GFrac R)}
    (h : rdeHexp₂ Hn Hd Gn Gd A D₁ m = some Y) :
    (valP x₀ t₁ Y / (t₁ ^ m * valP x₀ t₁ D₁))′ +
        aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd) * (valP x₀ t₁ Y / (t₁ ^ m * valP x₀ t₁ D₁)) =
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
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (toPoly Hn) / algebraMap R[X] R⟮x₀⟯ (toPoly Hd)
    with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) := by
    rw [hη₁', map_div₀]
    change ((algebraMap R[X] R⟮x₀⟯ (toPoly Hn) : R⟮x₀⟯) : F₀) /
      ((algebraMap R[X] R⟮x₀⟯ (toPoly Hd) : R⟮x₀⟯) : F₀) = _
    rw [hcoe, hcoe]
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine CPoly.hyperexpW_homogeneous (K := R⟮x₀⟯) (RingHom.id R) hD hHn0 hHd0 hcop hcert (n : ℤ)
      (by exact_mod_cast hn) b (by
        rw [hb, hη₁', Polynomial.map_id, Polynomial.map_id,
          show algebraMap R[X] R⟮x₀⟯ (C (((n : ℕ) : ℤ) : R)) = (n : R⟮x₀⟯) by
            rw [Int.cast_natCast, show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n,
              map_natCast]])
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hηa : ηh (K₁ := R⟮x₀⟯) (RingHom.id R) Hn Hd = η₁' := by
    rw [ηh, Polynomial.map_id, Polynomial.map_id]
  have hD₂ : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (C (ηh (K₁ := R⟮x₀⟯) (RingHom.id R) Hn Hd) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hD0' : GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) D₁ ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) D₁).mpr hz] at hD0
    exact Bool.noConfusion hD0
  have hsound := rdeHexp₂_sound (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hD Hn Hd hD₂
    hHd0 Gn Gd hGd0 A D₁ m hD0' h
  -- values of codes in `F₀`
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hXF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ X : (R⟮x₀⟯)⟮t₁⟯) : F₀) = t₁ := by
    rw [algebraMap_adjoinSimple, aeval_X]
  have hgF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (C (ev R⟮x₀⟯ (RingHom.id R) (Gn, Gd))) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd) := by
    rw [algebraMap_adjoinSimple, aeval_C]
    exact hevc (Gn, Gd)
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsound
  have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  simp only [hderiv, IntermediateField.coe_add, IntermediateField.coe_div, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, hvalP, hgF, hXF] at this
  exact this

end Tower
