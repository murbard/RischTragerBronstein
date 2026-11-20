import RischTragerBronstein.Computable.LiBaseConst
import RischTragerBronstein.Computable.IntegratePrimIn
import RischTragerBronstein.Computable.NestedLogPolyDecision

/-!
# Non-elementary nested primitives (`li x`-type): every element of `R(x)(t₁)` at level `0`

`ρ ∈ R(x)(t₁)`, viewed in `K = R(x)(t₁)(t₂)` with `t₂′ = W` (simple part failing the residue test),
has an elementary integral iff `nestedConst` finds a constant `c` and the height-two integrator
accepts `ρ - c W`; then `∫ ρ = c t₂ + ∫ (ρ - c W)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section F0

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem valG_subSmulCode_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    {Iη₁ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false) (ρ W : GFrac (GFrac R)) (c : R) :
    GPoly.isZero (ops₁g R) (subSmulCode En₁ Ed₁ ρ W c).2 = false ∧
    valG x₀ t₁ (subSmulCode En₁ Ed₁ ρ W c) = valG x₀ t₁ ρ -
      algebraMap R F₀ c * valG x₀ t₁ W := by
  have k : ℕ := 0
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
  obtain ⟨hden, hsem⟩ := subSmulCode_spec (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0
    hM.hD hM.hD₂ ρ W c
  refine ⟨Bool.eq_false_iff.mpr fun hz ↦ hden ((GPoly.isZero_iff _ _).mp hz), ?_⟩
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsem
  have hcF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (C (algebraMap R[X] R⟮x₀⟯ (C c))) :
      (R⟮x₀⟯)⟮t₁⟯) : F₀) = algebraMap R F₀ c := by
    rw [algebraMap_adjoinSimple, aeval_C]
    change ((algebraMap R[X] R⟮x₀⟯ (C c) : R⟮x₀⟯) : F₀) = _
    rw [hcoe, aeval_C]
  have hsemG' : ∀ q : GFrac (GFrac R),
      (((M₂W (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hM.hD hM.hD₂).sem q : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
        valG x₀ t₁ q := hsemG
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsemG', RingHom.id_apply, hcF]
    at this
  exact this

end F0

section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- The level-`0` decision under a non-elementary nested primitive. -/
def integrateLiBase (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (W ρ : GFrac (GFrac R)) :
    Bool :=
  match nestedConst En₁ Ed₁ ρ W with
  | none => false
  | some c =>
    integratePrim En₁ Ed₁ Iη₁ (subSmulCode En₁ Ed₁ ρ W c).1 (subSmulCode En₁ Ed₁ ρ W c).2

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **Level `0` under a non-elementary nested primitive: decided.** -/
theorem integrateLiBase_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 = false)
    (hresW : GPoly.residueCheck (ops₁g R) [(En₁, Ed₁)]
      (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s = false)
    (ρ : GFrac (GFrac R)) (hρ0 : GPoly.isZero (ops₁g R) ρ.2 = false) :
    HasElementaryIntegral (algebraMap F₀ K (valG x₀ t₁ ρ)) ↔
      integrateLiBase En₁ Ed₁ Iη₁ W ρ = true := by
  have hsplit : ∀ c : R, algebraMap F₀ K (valG x₀ t₁ ρ) =
      (algebraMap F₀ K (algebraMap R F₀ c) * t)′ +
        algebraMap F₀ K (valG x₀ t₁ (subSmulCode En₁ Ed₁ ρ W c)) := fun c ↦ by
    obtain ⟨-, hval⟩ := valG_subSmulCode_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 ρ W c
    rw [Derivation.leibniz, deriv_algebraMap, hR, map_zero, ht, hval]
    simp only [smul_eq_mul, mul_zero, add_zero, map_sub, map_mul]
    ring
  unfold integrateLiBase
  constructor
  · rintro ⟨E, _, _, _, _, hE, g, hg⟩
    obtain ⟨c, hc, hres⟩ := liBase_const_residue hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ W t hgen ht Iη₁
      hcη₁ hη₁0 hW0 hWnd hresW ρ hρ0 E hE g hg
    rw [hc]
    simp only
    have hG' : HasElementaryIntegral
        (algebraMap F₀ K (valG x₀ t₁ (subSmulCode En₁ Ed₁ ρ W c))) := by
      have h1 : HasElementaryIntegral (algebraMap F₀ K (valG x₀ t₁ ρ)) :=
        ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hE, g, hg⟩
      rw [hsplit c] at h1
      exact (hasElementaryIntegral_deriv_add_iff _ _).mp h1
    obtain ⟨hden, -⟩ := valG_subSmulCode_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 ρ W c
    generalize subSmulCode En₁ Ed₁ ρ W c = G' at hG' hres hden ⊢
    obtain ⟨hid, hsqc, hcopc, hlen⟩ := hermite_valG_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 G'.1 G'.2 hden
    rw [Prod.mk.eta] at hid
    simp only [integratePrim, Bool.and_eq_true]
    refine ⟨hres, ?_⟩
    by_contra hnone
    rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
    rw [hid, map_add, ← deriv_algebraMap, hasElementaryIntegral_deriv_add_iff, map_add] at hG'
    have hq := hG'.sub_in (hasElementaryIntegralIn_prim2BaseResidue (K := K) hR x₀ t₁ hx₀ ht₁ hcη₁
      hη₁0 _ _ hsqc hcopc hlen hres)
    rw [add_sub_cancel_right, valP_eq_sum_poly] at hq
    obtain ⟨E', _, _, _, _, hE', g', hg'⟩ := hq
    exact not_elementary_liBase hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ W t hgen ht Iη₁ hcη₁ hη₁0 hW0 hWnd
      hresW _ _ _ (fun j _ ↦ normFrac_den_ne_zero _) hnone E' hE' g' hg'
  · intro h
    cases hc : nestedConst En₁ Ed₁ ρ W with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      simp only at h
      obtain ⟨hden, -⟩ := valG_subSmulCode_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 ρ W c
      rw [hsplit c, hasElementaryIntegral_deriv_add_iff]
      have := hasElementaryIntegral_valG_of_integratePrim (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ Iη₁
        hcη₁ hη₁0 _ _ hden h
      rwa [Prod.mk.eta] at this

end Tower
