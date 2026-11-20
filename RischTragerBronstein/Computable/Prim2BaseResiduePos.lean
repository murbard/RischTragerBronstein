import RischTragerBronstein.Computable.Prim2BaseResidue
import RischTragerBronstein.Liouville.ResidueTestSufficient

/-!
# Simple poles at the first primitive, seen from a larger field: the positive answer

For `b(t₁) / s(t₁) ∈ R(x₀)(t₁) = F₀` (generic codes, `s` certified squarefree and coprime to `s′`,
`deg b < deg s`) and any differential field `K ⊇ F₀`: if the residue test passes, `b / s` has an
elementary integral over `K`, and over every elementary extension of `K`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

set_option maxHeartbeats 1600000 in
theorem hasElementaryIntegralIn_prim2BaseResidue (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    {Iη₁ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false) (bc sc : GPoly (GFrac R))
    (hsqc : GPoly.squarefreeCheck (Tower.ops₁g R) sc = true)
    (hcopc : GPoly.coprimeDerivCheck (Tower.ops₁g R) [(En₁, Ed₁)] sc = true)
    (hlen : (GPoly.trim (Tower.ops₁g R) bc).length < (GPoly.trim (Tower.ops₁g R) sc).length)
    (hres : GPoly.residueCheck (Tower.ops₁g R) [(En₁, Ed₁)] bc sc = true) :
    HasElementaryIntegralIn
      (algebraMap F₀ K (Tower.valP x₀ t₁ bc / Tower.valP x₀ t₁ sc)) := by
  classical
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
  -- `K` as an `R(x₀)`-algebra
  have hST : IsScalarTower R⟮x₀⟯ F₀ K := inferInstance
  have hDAK : DifferentialAlgebra R⟮x₀⟯ K := ⟨fun a ↦ by
    change (algebraMap F₀ K (algebraMap R⟮x₀⟯ F₀ a))′ = algebraMap F₀ K (algebraMap R⟮x₀⟯ F₀ a′)
    rw [deriv_algebraMap, deriv_algebraMap]⟩
  set M₁ := Tower.M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD with hM₁
  have hvalP : ∀ q : GPoly (GFrac R), aeval t₁ (GPoly.toPoly M₁ q) = Tower.valP x₀ t₁ q :=
    fun q ↦ by
      rw [GPoly.toPoly_eq_sum_range _ q ([], [1])]
      simp only [Tower.valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, hM₁, Tower.sem_M₁In,
        hevc]
  have hvalK : ∀ q : GPoly (GFrac R), aeval (algebraMap F₀ K t₁) (GPoly.toPoly M₁ q) =
      algebraMap F₀ K (Tower.valP x₀ t₁ q) := fun q ↦ by
    rw [aeval_algebraMap_apply, hvalP]
  set Sp := GPoly.toPoly M₁ sc with hSp
  have hsq : Squarefree Sp := GPoly.squarefreeCheck_sound M₁ hsqc
  have hS0 : Sp ≠ 0 := hsq.ne_zero
  have hW : GPoly.toPoly M₁ [(En₁, Ed₁)] = C η₁' := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, Tower.sem_M₁In]
  have hcop := GPoly.coprimeDerivCheck_sound M₁ hcopc
  have hr := GPoly.residuePoly_spec M₁ [(En₁, Ed₁)] bc sc hS0 hcop
  rw [hW] at hr
  have hT := (GPoly.residueCheck_iff M₁ [(En₁, Ed₁)] bc sc hS0).mp hres
  have hdeg := GPoly.degree_lt_of_trim_length_lt M₁ hlen
  have hst : aeval (algebraMap F₀ K t₁) Sp ≠ 0 := by
    rw [hvalK, ← hvalP]
    exact (_root_.map_ne_zero _).mpr
      ((map_ne_zero_iff _ (transcendental_iff_injective.mp htr1)).mpr hS0)
  have := hasElementaryIntegralIn_of_residueTest (F := R⟮x₀⟯) (E := K) (algebraMap F₀ K t₁) η₁' 0
    (by
      rw [deriv_algebraMap, ht₁', map_zero, zero_mul, add_zero]
      rfl) 1 one_ne_zero (by rw [logDeriv_one, map_zero]) Sp (GPoly.toPoly M₁ bc) _
    (PerfectField.separable_iff_squarefree.mpr hsq) hst hdeg (by
      have hid : implicitDeriv (C η₁') Sp = mapCoeffs Sp + (C η₁' + C 0 * X) * derivative Sp := by
        simp [implicitDeriv]
      rw [← hid]
      exact hr) hT
  rwa [hvalK, hvalK, ← map_div₀] at this

end CPoly
