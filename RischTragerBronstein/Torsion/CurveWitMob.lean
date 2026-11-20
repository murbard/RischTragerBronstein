import RischTragerBronstein.Torsion.CurveWitLoop
import RischTragerBronstein.Torsion.MobWit

/-!
# Curve antiderivatives from Möbius certificates

A witness found for the transform `P'` of the problem at `t = 1/(x − e)`, `w = y tᵏ⁰` is valid on
the transformed curve `S'` for the derivation rescaled by `dx/dt = −1/t²`. Multiplying back,
it is an antiderivative for the original derivation (`CurveWQ.validMob`):
`f = v′ + ∑ⱼ cⱼ uⱼ′/uⱼ` with `v`, `uⱼ` the functions of the witness evaluated at `(t, w)`.
-/

open Polynomial IntermediateField

namespace Curves

open CPoly Sup EllQuad.QCoords Differential

section V

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

lemma CurveProb.valid_of_decideLogW {P : CurveProb F} {ws : List (LogWit F)} {w : CurveW F}
    (h : P.decideLogW ws = some (some w)) : P.valid = true := by
  unfold CurveProb.decideLogW at h
  by_contra hv
  rw [if_neg hv] at h
  exact absurd h (by simp)

end V

section Mob

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 4000000 in
/-- **The curve antiderivative of a Möbius witness, explicitly.** -/
theorem CurveWQ.validMob (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (P0 : CurveProb ℚ) (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc)))
    (W : CurveWQ) (hsrc : W.Src P0) (e : NFC.NF W.M.1) (k₀ DA k' : ℕ)
    (hmob : W.mob = some (e, k₀, DA, k')) :
    haveI : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
    ∀ ι : NFC.NF W.M.1 →+* Kc, ∃ S' : CurveData Kc E,
      S'.x = 1 / (S.x - algebraMap Kc E (ι e)) ∧ S'.y = S.y * S'.x ^ k₀ ∧
      (S.fE P0 (algebraMap ℚ Kc) : E) = (S'.vvE W.P ι W.w.cs : E)′ +
        (if W.w.logs then ∑ j : Fin (dim (NFC.NF W.M.1)),
          algebraMap Kc E (CurveData.cj ι W.w.ws j) *
            ((S'.uE ι (CurveProb.witAt W.w.ws j) : E)′ / (S'.uE ι (CurveProb.witAt W.w.ws j) : E))
          else 0) ∧
      (W.w.logs = true → ∀ j, (S'.uE ι (CurveProb.witAt W.w.ws j) : E) ≠ 0) := by
  have : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
  intro ι
  obtain ⟨ws, hw⟩ := hsrc.2.2
  have hV' := W.P.valid_spec (CurveProb.valid_of_decideLogW hw)
  set P := P0.baseChange (algebraMap ℚ (NFC.NF W.M.1)) P0.k [] ⟨1, [], 0⟩ with hP
  have hι : ι.comp (algebraMap ℚ (NFC.NF W.M.1)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have hSF' : S.F = (toB P.Fc).map (mapRingHom ι) := by
    rw [hP, hSF, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]
  obtain ⟨S', hx', hy', hS'F, hid⟩ := mob_curve S P W.P ι hSF' e k₀ DA
    (hsrc.2.1 e k₀ DA k' hmob) hV'
  set c : Kc := ι e with hc
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxc : S.x - algebraMap Kc E c ≠ 0 := x_sub_ne S c
  have ht0 : S'.x ≠ 0 := by rw [hx']; exact one_div_ne_zero hxc
  have ht' : (S'.x)′ = -S'.x ^ 2 := by
    rw [hx', Derivation.leibniz_div, map_sub, hx, hconstE]
    simp only [Derivation.map_one_eq_zero, smul_eq_mul, mul_zero, sub_zero, mul_one, zero_sub]
    field_simp
  set τ : E := -S'.x ^ 2 with hτ
  have hτ0 : τ ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ht0)
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hD : ∀ z : E, (rescale ⟨d0⟩ (1 / τ)).deriv z = 1 / τ * z′ := fun z ↦ by
    rw [rescale_deriv]
  have hT' : (rescale ⟨d0⟩ (1 / τ)).deriv S'.x = 1 := by
    rw [hD, ht']; exact one_div_mul_cancel hτ0
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ (rescale ⟨d0⟩ (1 / τ)) :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ (rescale ⟨d0⟩ (1 / τ)) (fun r ↦ by
      rw [hD, hconstE, hC, map_zero, mul_zero])
  have key := @CurveProb.decideLogW_valid Kc E _ _ _ _ _ _ (rescale ⟨d0⟩ (1 / τ)) hDA' _ _ _ _ _
    S' hC hT' W.P ι hS'F ws W.w hw
  obtain ⟨k1, k2⟩ := key
  refine ⟨S', hx', hy', ?_, k2⟩
  have hfP : (S.fE P0 (algebraMap ℚ Kc) : E) = (S.fE P ι : E) := by
    rw [hP, S.fE_baseChange, hι]
  rw [hfP]
  have hS : (S.fE P ι : E) = τ * (S'.fE W.P ι : E) := by
    rw [hid]; field_simp
  rw [hS, k1]
  simp only [hD]
  split_ifs
  · rw [mul_add, Finset.mul_sum]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      field_simp
  · rw [mul_add, mul_zero, add_zero, add_zero, one_div, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]

end Mob

end Curves
