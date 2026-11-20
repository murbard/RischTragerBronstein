import RischTragerBronstein.Computable.Prim2LoopWPositive
import RischTragerBronstein.Computable.NestedLogBaseFull
import RischTragerBronstein.Computable.Prim2PolyWStrong

/-!
# Nested logarithm: polynomials in `t₂ = log u` with arbitrary coefficients in `R(x)(t₁)` — decided

`integrateNestedLogPoly` runs the loop `prim2LoopW` (one limited integration problem with
parameter function `W = u′ / u` per power of `t₂`) and hands the level-0 remainder
`A₀ - W Q₁ ∈ R(x)(t₁)` to the height-two integrator.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section F0

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem valG_gCodeW_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    {Iη₁ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false) (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GPoly.isZero (ops₁g R) (gCodeW En₁ Ed₁ W k Ak Q).2 = false ∧
    valG x₀ t₁ (gCodeW En₁ Ed₁ W k Ak Q) = valG x₀ t₁ Ak -
      ((k + 1 : ℕ) : F₀) * valG x₀ t₁ W * valG x₀ t₁ Q := by
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
  have hM : ModelW (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) En₁ Ed₁ :=
    ModelW.of (RingHom.id R) hD (fun _ ↦ rfl) hη₁nd
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
      (((hM.cf (RingHom.id R) h0).sem q : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valG x₀ t₁ q := fun q ↦ by
    rw [sem_M₂W, IntermediateField.coe_div, hvalP, hvalP, valG]
  obtain ⟨hden, hsem⟩ := sem_gCodeW (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hM W k Ak Q
  refine ⟨Bool.eq_false_iff.mpr fun hz ↦ hden ((GPoly.isZero_iff _ _).mp hz), ?_⟩
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsem
  have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  have hnat : (((k + 1 : ℕ) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = ((k + 1 : ℕ) : F₀) := by
    rw [← map_natCast (algebraMap (R⟮x₀⟯)⟮t₁⟯ F₀)]; rfl
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsemG, hnat] at this
  exact this

end F0

section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- The integrator for `∑ₖ Aₖ t₂ ^ k`, `t₂′ = W`. -/
def integrateNestedLogPoly (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (W : GFrac (GFrac R))
    (A : ℕ → GFrac (GFrac R)) (d₂ : ℕ) : Bool :=
  match prim2LoopW En₁ Ed₁ Iη₁ W A d₂ ([], [(ops₁g R).one]) with
  | none => false
  | some L =>
    let G := gCodeW En₁ Ed₁ W 0 (A 0) (lastGen ([], [(ops₁g R).one]) L)
    integratePrim En₁ Ed₁ Iη₁ G.1 G.2

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **Nested logarithm, polynomial part: decided**, both directions. -/
theorem integrateNestedLogPoly_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W U : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hrW : GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 = false)
    (hWnd : isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 = false)
    (hU0 : (ops₂p En₁ Ed₁).isZero U = false)
    (hlog : (ops₂p En₁ Ed₁).isZero ((ops₂p En₁ Ed₁).add ((ops₂p En₁ Ed₁).mul W U)
      ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).deriv U))) = true)
    (d₂ : ℕ) (A : ℕ → GFrac (GFrac R)) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valG x₀ t₁ (A k)) * t ^ k) ↔
      integrateNestedLogPoly En₁ Ed₁ Iη₁ W A d₂ = true := by
  unfold integrateNestedLogPoly
  cases hL : prim2LoopW En₁ Ed₁ Iη₁ W A d₂ ([], [(ops₁g R).one]) with
  | none =>
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨E, _, _, _, _, hE, g, hg⟩
    exact not_elementary_prim2PolyW hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ W t hgen ht Iη₁ hcη₁ hη₁0
      hW0 hrW hWnd d₂ A hL E hE g hg
  | some L =>
    simp only
    have hanti := prim2LoopW_antiderivative (K := K) hR x₀ t₁ hx₀ ht₁ W t ht hcη₁ hη₁0 A d₂ _ hL
    have hQ0 : valG x₀ t₁ (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by
      simp [valG, valP]
    rw [hQ0, map_zero, map_zero, zero_mul, zero_add] at hanti
    obtain ⟨hden, hval⟩ := valG_gCodeW_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 W 0 (A 0)
      (lastGen ([], [(ops₁g R).one]) L)
    rw [hanti, hasElementaryIntegral_deriv_add_iff,
      ← nestedLogBaseGen_decides (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ W U t hgen ht Iη₁
        hcη₁ hη₁0 hW0 hWnd hU0 hlog _ _ hden, Prod.mk.eta, hval]
    simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]

end Tower
