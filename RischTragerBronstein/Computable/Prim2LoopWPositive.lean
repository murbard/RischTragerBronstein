import RischTragerBronstein.Computable.Prim2StepW
import RischTragerBronstein.Computable.Prim2StepGenF0
import RischTragerBronstein.Computable.Prim2LoopGenPositive

/-!
# The nested `t₂`-loop read in `F₀ = R(x₀)(t₁)`, and the antiderivative it produces

* `Tower.ModelW.of`: the model hypotheses from `η₁` not being a derivative;
* `Tower.prim2StepW_sound_F₀`: one level, for the values `valG` in an abstract field `F₀`;
* `Tower.prim2LoopW_antiderivative`: with `t′ = W` in `K ⊇ F₀`,
  `∑ Aₖ tᵏ = (prim2WGen …)′ + (A₀ - W · Q₁)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section Of

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

theorem ModelW.of (ι : R →+* S) {En₁ Ed₁ : CPoly R} (hD : ∀ P : S[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ev K₁ ι (En₁, Ed₁))) P)
    (hη₁nd : ∀ y : K₁, y′ ≠ ev K₁ ι (En₁, Ed₁)) :
    ModelW (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ := by
  have hKconst := const_of_model (K₁ := K₁) hD
  have hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero _ hη₁nd (by rw [← hD₂, hP])
  have hnorm₂ : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive _ hD₂ hconst₂ hp
  refine ⟨hD, hKconst, hD₂, hconst₂, fun y hy ↦ ?_⟩
  obtain ⟨-, P, rfl, hP⟩ := deriv_eq_poly_add_proper (K := K₂) hnorm₂ 0 0 1 squarefree_one
    (by simp) y (by rw [hy]; simp)
  obtain ⟨e, rfl⟩ := hconst₂ P hP
  have he : e′ = 0 := by
    rw [hD₂, implicitDeriv_C] at hP
    exact C_eq_zero.mp hP
  obtain ⟨b, rfl⟩ := hKconst e he
  exact ⟨b, rfl⟩

end Of

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem prim2StepW_sound_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    {Iη₁ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false) (W : GFrac (GFrac R))
    (k : ℕ) (Ak Q : GFrac (GFrac R)) {c : R} {Q' : GFrac (GFrac R)}
    (h : prim2StepW En₁ Ed₁ Iη₁ W k Ak Q = some (c, Q')) :
    (valG x₀ t₁ Q')′ = valG x₀ t₁ Ak - ((k + 1 : ℕ) : F₀) * valG x₀ t₁ W * valG x₀ t₁ Q -
      algebraMap R F₀ c * valG x₀ t₁ W := by
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
  have hsound := prim2StepW_sound (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hM hcη₁
    hEd₁ W k Ak Q h
  -- values of codes in `F₀`
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hsemG : ∀ q : GFrac (GFrac R),
      (((hM.cf (RingHom.id R) h0).sem q : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valG x₀ t₁ q := fun q ↦ by
    rw [sem_M₂W, IntermediateField.coe_div, hvalP, hvalP, valG]
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsound
  have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  have hnat : (((k + 1 : ℕ) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = ((k + 1 : ℕ) : F₀) := by
    rw [← map_natCast (algebraMap (R⟮x₀⟯)⟮t₁⟯ F₀)]; rfl
  have hcF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (C (algebraMap R[X] R⟮x₀⟯ (C c))) :
      (R⟮x₀⟯)⟮t₁⟯) : F₀) = algebraMap R F₀ c := by
    rw [algebraMap_adjoinSimple, aeval_C]
    change ((algebraMap R[X] R⟮x₀⟯ (C c) : R⟮x₀⟯) : F₀) = _
    rw [hcoe, aeval_C]
  simp only [hderiv, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsemG, hnat,
    RingHom.id_apply, hcF] at this
  exact this

variable {K : Type*} [Field K] [Algebra F₀ K] [Differential K] [DifferentialAlgebra F₀ K]

/-- **The result is an antiderivative** (nested primitive, polynomial part). -/
theorem prim2LoopW_antiderivative (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁)) (W : GFrac (GFrac R)) (t : K)
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    {Iη₁ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (A : ℕ → GFrac (GFrac R)) (k : ℕ)
    (Q : GFrac (GFrac R)) {L : List (R × GFrac (GFrac R))}
    (hL : prim2LoopW En₁ Ed₁ Iη₁ W A k Q = some L) :
      (algebraMap F₀ K (valG x₀ t₁ Q))′ * t ^ (k + 1) +
          ∑ j ∈ Finset.range (k + 1), algebraMap F₀ K (valG x₀ t₁ (A j)) * t ^ j =
        (prim2WGen x₀ t₁ t (k + 1) Q L)′ + (algebraMap F₀ K (valG x₀ t₁ (A 0)) -
          algebraMap F₀ K (valG x₀ t₁ W) * algebraMap F₀ K (valG x₀ t₁ (lastGen Q L))) := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap F₀ K).injective
  induction k generalizing Q L with
  | zero =>
    simp only [prim2LoopW, Option.some.injEq] at hL
    subst hL
    rw [prim2WGen, lastGen, Derivation.leibniz, ht]
    simp only [smul_eq_mul, zero_add, pow_one, Finset.range_one, Finset.sum_singleton, pow_zero,
      mul_one]
    ring
  | succ k ih =>
    simp only [prim2LoopW] at hL
    cases hstep : prim2StepW En₁ Ed₁ Iη₁ W (k + 1) (A (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      obtain ⟨c, Q'⟩ := cQ
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      have hsol := prim2StepW_sound_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 W (k + 1) (A (k + 1)) Q hstep
      have hrec := ih Q' hL'
      set γ : K := algebraMap F₀ K (algebraMap R F₀ (c / ((k + 1 + 1 : ℕ) : R))) with hγ
      have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, hR, map_zero]
      have hγc : ((k + 1 + 1 : ℕ) : K) * γ = algebraMap F₀ K (algebraMap R F₀ c) := by
        rw [hγ, map_div₀, map_div₀, map_natCast, map_natCast]
        exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
      set q : K := algebraMap F₀ K (valG x₀ t₁ Q) with hq
      set η₂ : K := algebraMap F₀ K (valG x₀ t₁ W) with hη₂
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
