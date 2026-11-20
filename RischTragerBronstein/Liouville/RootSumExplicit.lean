import RischTragerBronstein.Liouville.ResidueTestSufficient

/-!
# The logarithmic part, explicitly

Under the hypotheses of `hasElementaryIntegral_of_residueTest` (`t′ = η + e t`, `s` separable,
`deg b < deg s`, `r` the residue polynomial, residue test passed), in **any** differential
extension `L` of `E` in which `s` splits (e.g. the algebraic closure):

  `b(t) / s(t) = ∑_{s(α) = 0} r(α) · (t − α)′/(t − α) − (∑_{s(α)=0} r(α)) · e`,

with every `r(α)` a constant and `t ≠ α` (`rootSum_explicit`). So
`∫ b/s = ∑ r(α) log (t − α) − (∑ r(α)) log θ` for any `θ` with `θ′/θ = e` (`θ = 1` below a
logarithm, `θ = t` below an exponential).
-/

open Polynomial

namespace Differential

variable {F : Type*} {E : Type*} {L : Type*} [Field F] [Differential F] [Field E] [Differential E]
variable [Algebra F E] [DifferentialAlgebra F E] [Field L] [Differential L] [Algebra E L]
variable [DifferentialAlgebra E L] [Algebra F L] [IsScalarTower F E L]

theorem rootSum_explicit [DecidableEq L] (t : E) (η e : F)
    (ht : t′ = algebraMap F E η + algebraMap F E e * t)
    (s b r : F[X]) (hsep : s.Separable) (hst : aeval t s ≠ 0) (hdeg : b.degree < s.degree)
    (hr : s ∣ r * (mapCoeffs s + (C η + C e * X) * derivative s) - b)
    (hT : s ∣ residueTest r s) (hsplit : (s.map (algebraMap F L)).Splits) :
    (∀ α ∈ (s.map (algebraMap F L)).roots.toFinset,
      (aeval α r)′ = 0 ∧ algebraMap E L t - α ≠ 0) ∧
    algebraMap E L (aeval t b / aeval t s) =
      ∑ α ∈ (s.map (algebraMap F L)).roots.toFinset,
        aeval α r * logDeriv (algebraMap E L t - α) -
      (∑ α ∈ (s.map (algebraMap F L)).roots.toFinset, aeval α r) * algebraMap F L e := by
  classical
  have hDAFL : DifferentialAlgebra F L := ⟨fun a ↦ by
    rw [IsScalarTower.algebraMap_apply F E L, deriv_algebraMap, deriv_algebraMap,
      ← IsScalarTower.algebraMap_apply]⟩
  set tL : L := algebraMap E L t with htL
  have haev : ∀ P : F[X], algebraMap E L (aeval t P) = aeval tL P := fun P ↦
    (aeval_algebraMap_apply L t P).symm
  have htL' : tL′ = algebraMap F L η + algebraMap F L e * tL := by
    rw [htL, deriv_algebraMap, ht, map_add, map_mul, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  set sL : L[X] := s.map (algebraMap F L) with hsL
  have hsepL : sL.Separable := hsep.map
  have hstL : eval tL sL ≠ 0 := by
    rw [hsL, eval_map_algebraMap, ← haev]
    exact (_root_.map_ne_zero _).mpr hst
  have hpf := eval_div_eq_sum_roots (q := b.map (algebraMap F L)) hsplit hsepL
    (by rw [hsL, degree_map, degree_map]; exact hdeg) hstL
  simp only [hsL, eval_map_algebraMap, derivative_map] at hpf
  set Rts := sL.roots.toFinset with hRts
  have hroot : ∀ α ∈ Rts, aeval α s = 0 := fun α hα ↦ by
    rw [hRts, Multiset.mem_toFinset, mem_roots hsepL.ne_zero, IsRoot.def, hsL,
      eval_map_algebraMap] at hα
    exact hα
  have hkey : ∀ α ∈ Rts, (aeval α r)′ = 0 ∧ tL - α ≠ 0 ∧
      aeval α b / aeval α (derivative s) * (tL - α)⁻¹ =
        aeval α r * logDeriv (tL - α) + -aeval α r * algebraMap F L e := by
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
    rw [hlog, ← hrα]
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
  refine ⟨fun α hα ↦ ⟨(hkey α hα).1, (hkey α hα).2.1⟩, ?_⟩
  rw [map_div₀, haev, haev, hpf, Finset.sum_congr rfl fun α hα ↦ (hkey α hα).2.2,
    Finset.sum_add_distrib, Finset.sum_mul]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

end Differential
