import RischTragerBronstein.Liouville.ResidueTest
import RischTragerBronstein.Liouville.PartialFractionsSplit
import RischTragerBronstein.Elementary.Algebraic
import RischTragerBronstein.Elementary.LiouvilleForm
import RischTragerBronstein.Elementary.Trans
import RischTragerBronstein.Elementary.Sum
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Sufficiency of the residue test (Rothstein–Trager, constructive direction)

Let `t ∈ E` with `t′ = η + e t` (`η, e ∈ F`; `e = 0`: primitive, `η = 0`: exponential), and let
`e = θ′ / θ` for some `θ ∈ E` (`θ = 1`, resp. `θ = t`). Let `s ∈ F[X]` be separable, `deg b < deg s`,
`r` a residue polynomial (`r s′ ≡ b mod s`) and suppose the residue test passes: `s ∣ T(r, s)`.
Then `b(t) / s(t)` has an elementary integral over `E`:

  `∫ b / s = ∑_{s(α) = 0} r(α) log (t - α) - (∑ r(α)) log θ`

in the splitting field of `s` over `E`, where all `r(α)` are constants.
-/

open Polynomial

namespace Differential

universe u

variable {F : Type*} {E : Type u} [Field F] [Differential F] [Field E] [CharZero E]
variable [Differential E] [Algebra F E] [DifferentialAlgebra F E]

theorem hasElementaryIntegral_of_residueTest (t : E) (η e : F)
    (ht : t′ = algebraMap F E η + algebraMap F E e * t)
    (θ : E) (hθ0 : θ ≠ 0) (hθ : logDeriv θ = algebraMap F E e)
    (s b r : F[X]) (hsep : s.Separable) (hst : aeval t s ≠ 0) (hdeg : b.degree < s.degree)
    (hr : s ∣ r * (mapCoeffs s + (C η + C e * X) * derivative s) - b)
    (hT : s ∣ residueTest r s) :
    HasElementaryIntegral (aeval t b / aeval t s) := by
  classical
  let L := (s.map (algebraMap F E)).SplittingField
  letI : Differential L := differentialFiniteDimensional E L
  have hDAEL : DifferentialAlgebra E L := differentialAlgebraFiniteDimensional
  have hDAFL : DifferentialAlgebra F L := ⟨fun a ↦ by
    rw [IsScalarTower.algebraMap_apply F E L, deriv_algebraMap, deriv_algebraMap,
      ← IsScalarTower.algebraMap_apply]⟩
  have hEL : IsElementaryExtension E L := isElementaryExtension_of_finiteDimensional
  refine HasElementaryIntegral.of_extension hEL ?_
  set tL : L := algebraMap E L t with htL
  have haev : ∀ P : F[X], algebraMap E L (aeval t P) = aeval tL P := fun P ↦
    (aeval_algebraMap_apply L t P).symm
  have htL' : tL′ = algebraMap F L η + algebraMap F L e * tL := by
    rw [htL, deriv_algebraMap, ht, map_add, map_mul, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  set θL : L := algebraMap E L θ with hθL
  have hθL0 : θL ≠ 0 := (_root_.map_ne_zero _).mpr hθ0
  have hθL' : logDeriv θL = algebraMap F L e := by
    rw [hθL, logDeriv_algebraMap, hθ, ← IsScalarTower.algebraMap_apply]
  -- the denominator splits in `L`
  set sL : L[X] := s.map (algebraMap F L) with hsL
  have hsplit : sL.Splits := by
    have := SplittingField.splits (s.map (algebraMap F E))
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  have hsepL : sL.Separable := hsep.map
  have hstL : eval tL sL ≠ 0 := by
    rw [hsL, eval_map_algebraMap, ← haev]
    exact (_root_.map_ne_zero _).mpr hst
  have hpf := eval_div_eq_sum_roots (q := b.map (algebraMap F L)) hsplit hsepL
    (by rw [hsL, degree_map, degree_map]; exact hdeg) hstL
  simp only [hsL, eval_map_algebraMap, derivative_map] at hpf
  -- the residues
  set Rts := sL.roots.toFinset with hRts
  have hroot : ∀ α ∈ Rts, aeval α s = 0 := fun α hα ↦ by
    rw [hRts, Multiset.mem_toFinset, mem_roots hsepL.ne_zero, IsRoot.def, hsL,
      eval_map_algebraMap] at hα
    exact hα
  have hkey : ∀ α ∈ Rts, (aeval α r)′ = 0 ∧ tL - α ≠ 0 ∧
      aeval α b / aeval α (derivative s) * (tL - α)⁻¹ =
        aeval α r * logDeriv (tL - α) + -aeval α r * logDeriv θL := by
    intro α hα
    have hα0 := hroot α hα
    have hd : aeval α (derivative s) ≠ 0 := hsep.aeval_derivative_ne_zero hα0
    have hα' : aeval α (mapCoeffs s) + aeval α (derivative s) * α′ = 0 := by
      rw [← deriv_aeval_eq, hα0, map_zero]
    have hTα : aeval α (mapCoeffs r) * aeval α (derivative s) -
        aeval α (derivative r) * aeval α (mapCoeffs s) = 0 := by
      obtain ⟨q, hq⟩ := hT
      have := congrArg (aeval α) hq
      rw [residueTest, map_sub, map_mul, map_mul, map_mul, hα0, zero_mul] at this
      exact this
    have hN : (aeval α r)′ = 0 := by
      have h1 : (aeval α r)′ * aeval α (derivative s) = 0 := by
        rw [deriv_aeval_eq]
        linear_combination hTα + aeval α (derivative r) * hα'
      exact (mul_eq_zero.mp h1).resolve_right hd
    have hrα : aeval α r * (aeval α (mapCoeffs s) +
        (algebraMap F L η + algebraMap F L e * α) * aeval α (derivative s)) = aeval α b := by
      obtain ⟨q, hq⟩ := hr
      have := congrArg (aeval α) hq
      simp only [map_sub, map_mul, map_add, aeval_C, aeval_X, hα0, zero_mul] at this
      linear_combination this
    have hne : tL - α ≠ 0 := fun h0 ↦ by
      rw [sub_eq_zero] at h0
      rw [hsL, eval_map_algebraMap, h0] at hstL
      exact hstL hα0
    refine ⟨hN, hne, ?_⟩
    have hlog : logDeriv (tL - α) =
        (algebraMap F L η + algebraMap F L e * α - α′) / (tL - α) + algebraMap F L e := by
      rw [logDeriv, map_sub, htL', div_add' _ _ _ hne, div_left_inj' hne]
      ring
    rw [hlog, hθL', ← hrα]
    have hα'' : aeval α (mapCoeffs s) = -(aeval α (derivative s) * α′) := by
      linear_combination hα'
    rw [hα'']
    have hcancel : aeval α (derivative s) / aeval α (derivative s) = 1 := div_self hd
    calc aeval α r * (-(aeval α (derivative s) * α′) +
            (algebraMap F L η + algebraMap F L e * α) * aeval α (derivative s)) /
          aeval α (derivative s) * (tL - α)⁻¹
        = aeval α r * (algebraMap F L η + algebraMap F L e * α - α′) * (tL - α)⁻¹ *
            (aeval α (derivative s) / aeval α (derivative s)) := by ring
      _ = _ := by rw [hcancel]; ring
  -- assemble the Liouville form
  have hsum : algebraMap E L (aeval t b / aeval t s) =
      (0 : L)′ + (((-∑ α ∈ Rts, aeval α r, θL) ::
        Rts.toList.map fun α ↦ (aeval α r, tL - α)).map fun p ↦ p.1 * logDeriv p.2).sum := by
    rw [map_div₀, haev, haev, hpf, map_zero, zero_add, List.map_cons, List.sum_cons,
      List.map_map, Finset.sum_map_toList]
    rw [Finset.sum_congr rfl fun α hα ↦ (hkey α hα).2.2, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    simp only [Function.comp, Finset.sum_neg_distrib]
    ring
  rw [hsum]
  refine hasElementaryIntegral_of_liouville_form _ _ fun p hp ↦ ?_
  rw [List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨α, hα, rfl⟩
  · refine ⟨?_, hθL0⟩
    simp only
    rw [map_neg, map_sum, Finset.sum_eq_zero fun α hα ↦ (hkey α hα).1, neg_zero]
  · rw [Finset.mem_toList] at hα
    exact ⟨(hkey α hα).1, (hkey α hα).2.1⟩

/-- The same, stable under elementary extensions of `E` (so that it can be added to other
integrals, `HasElementaryIntegral.add_in`). -/
theorem hasElementaryIntegralIn_of_residueTest (t : E) (η e : F)
    (ht : t′ = algebraMap F E η + algebraMap F E e * t)
    (θ : E) (hθ0 : θ ≠ 0) (hθ : logDeriv θ = algebraMap F E e)
    (s b r : F[X]) (hsep : s.Separable) (hst : aeval t s ≠ 0) (hdeg : b.degree < s.degree)
    (hr : s ∣ r * (mapCoeffs s + (C η + C e * X) * derivative s) - b)
    (hT : s ∣ residueTest r s) :
    HasElementaryIntegralIn (aeval t b / aeval t s) := by
  intro E' _ _ _ _ _
  let _ : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra F E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap F E a))′ = algebraMap E E' (algebraMap F E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hchar : CharZero E' := charZero_of_injective_algebraMap (algebraMap E E').injective
  have haev : ∀ P : F[X], algebraMap E E' (aeval t P) = aeval (algebraMap E E' t) P := fun P ↦
    (aeval_algebraMap_apply E' t P).symm
  rw [map_div₀, haev, haev]
  refine hasElementaryIntegral_of_residueTest (algebraMap E E' t) η e ?_ (algebraMap E E' θ)
    ((_root_.map_ne_zero _).mpr hθ0) ?_ s b r hsep ?_ hdeg hr hT
  · rw [deriv_algebraMap, ht, map_add, map_mul]
    rfl
  · rw [logDeriv_algebraMap, hθ]
    rfl
  · rw [← haev]
    exact (_root_.map_ne_zero _).mpr hst

end Differential
