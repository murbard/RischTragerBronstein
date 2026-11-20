import RischTragerBronstein.Torsion.MobP

/-!
# The transformed curve of a Möbius certificate

`mob_curve`: for `mobCheck P P' e k₀ DA`, the curve `S'` with `x' = t = 1/(x − e)`,
`y' = y tᵏ⁰` carries the problem `P'`, and its integrand is `f / (−t²)` — the integrand of `P`
for the derivation rescaled by `dx/dt`. (The algebraic part of `decideLogTP_mob_spec`.)
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries GTors

section MobCurveEx

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

set_option maxHeartbeats 4000000 in
/-- **The transformed curve.** -/
theorem mob_curve (S : CurveData Kc E) (P P' : CurveProb F) (ι : F →+* Kc)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ι)) (e : F) (k0 DA : ℕ)
    (hmob : mobCheck P P' e k0 DA = true) (hV' : P'.ValidFacts) :
    ∃ S' : CurveData Kc E, S'.x = 1 / (S.x - algebraMap Kc E (ι e)) ∧
      S'.y = S.y * S'.x ^ k0 ∧ S'.F = (toB P'.Fc).map (mapRingHom ι) ∧
      (S'.fE P' ι : E) = 1 / (-S'.x ^ 2) * (S.fE P ι : E) := by
  classical
  simp only [mobCheck, Bool.and_eq_true, decide_eq_true_eq] at hmob
  obtain ⟨⟨⟨⟨⟨⟨⟨hn', hFc'⟩, hokF⟩, hA'⟩, hokA⟩, hsDl⟩, hdD⟩, hD'⟩ := hmob
  set c : Kc := ι e with hc
  -- the transformed curve
  have hFs : shiftP S.F c = (shiftP (toB P.Fc) e).map (mapRingHom ι) := by rw [hSF, shiftP_map]
  have hInvF : InvOK k0 (k0 * P.n) 0 (shiftB P.Fc e) := invOKb_spec hokF
  have hG : invP (shiftP S.F c) k0 (k0 * P.n) = (toB P'.Fc).map (mapRingHom ι) := by
    rw [hFs, ← invP_map, ← toB_shiftB, ← toB_invB _ _ _ hInvF, ← hFc']
  have hGdeg : (invP (shiftP S.F c) k0 (k0 * P.n)).natDegree = P.n := by
    rw [hG, hV'.mon.natDegree_map, hV'.deg, hn']
  have hGm : (invP (shiftP S.F c) k0 (k0 * P.n)).Monic := by rw [hG]; exact hV'.mon.map _
  have hnP : S.F.natDegree = P.n := by
    refine le_antisymm ?_ (by
      have := (natDegree_invP_le (shiftP S.F c) k0 (k0 * P.n)).trans (natDegree_shiftP_le _ _)
      rwa [hGdeg] at this)
    have hcoef : (invP (shiftP S.F c) k0 (k0 * P.n)).coeff S.F.natDegree ≠ 0 := by
      rw [coeff_invP, coeff_shiftP, S.monic.coeff_natDegree, one_comp]
      intro h0
      exact one_ne_zero ((reflect_eq_zero_iff).mp h0)
    have := le_natDegree_of_ne_zero hcoef
    rwa [hGdeg] at this
  have hM : ∀ i ≤ (shiftP S.F c).natDegree,
      ((shiftP S.F c).coeff i).natDegree + k0 * i ≤ k0 * P.n := by
    intro i hi
    have hb := invBound_of_invOK _ _ _ hInvF i (by
      rw [toB_shiftB]
      refine le_trans hi ?_
      rw [hFs]; exact natDegree_map_le)
    rw [hFs, coeff_map, ← toB_shiftB, coe_mapRingHom]
    have h2 := natDegree_map_le (f := ι) (p := (toB (shiftB P.Fc e)).coeff i)
    omega
  set S' := mobCurve S c k0 (k0 * P.n) hM hGm (by rw [hGdeg, hnP]) with hS'
  have hS'F : S'.F = (toB P'.Fc).map (mapRingHom ι) := hG
  set t : E := 1 / (S.x - algebraMap Kc E c) with ht
  set w : E := S.y * t ^ k0 with hw
  have hxc : S.x - algebraMap Kc E c ≠ 0 := x_sub_ne S c
  have ht0 : t ≠ 0 := one_div_ne_zero hxc
  have hxt : 1 / t + algebraMap Kc E c = S.x := by rw [ht, one_div_one_div, sub_add_cancel]
  have hwt : w / t ^ k0 = S.y := by rw [hw]; exact mul_div_cancel_right₀ _ (pow_ne_zero _ ht0)
  set τ : E := -t ^ 2 with hτ
  -- the transformed integrand
  have hInvA : InvOK k0 DA 0 (shiftB P.A e) := invOKb_spec hokA
  have hAm : (toB P'.A).map (mapRingHom ι) = Polynomial.C (Polynomial.C (-1)) *
      invP (shiftP ((toB P.A).map (mapRingHom ι)) c) k0 DA := by
    rw [hA', toB_mobA, toB_smulB, Polynomial.map_mul, toB_invB _ _ _ hInvA, invP_map, toB_shiftB,
      shiftP_map]
    simp [CPoly.toPoly]
    rfl
  have hAb : ∀ i ≤ (shiftP ((toB P.A).map (mapRingHom ι)) c).natDegree,
      ((shiftP ((toB P.A).map (mapRingHom ι)) c).coeff i).natDegree + k0 * i ≤ DA := by
    intro i hi
    have hsm : shiftP ((toB P.A).map (mapRingHom ι)) c = (toB (shiftB P.A e)).map (mapRingHom ι) := by
      rw [toB_shiftB, shiftP_map]
    rw [hsm] at hi ⊢
    have hb := invBound_of_invOK _ _ _ hInvA i (le_trans hi natDegree_map_le)
    rw [coeff_map, coe_mapRingHom]
    have h2 := natDegree_map_le (f := ι) (p := (toB (shiftB P.A e)).coeff i)
    omega
  have hevA : S'.evXY ((toB P'.A).map (mapRingHom ι)) =
      -(t ^ DA * S.evXY ((toB P.A).map (mapRingHom ι))) := by
    show ev _ t w = _
    rw [hAm]
    have e1 : ev (Polynomial.C (Polynomial.C (-1)) *
        invP (shiftP ((toB P.A).map (mapRingHom ι)) c) k0 DA) t w =
        -ev (invP (shiftP ((toB P.A).map (mapRingHom ι)) c) k0 DA) t w := by
      simp [ev, Polynomial.map_mul]
    rw [e1, ev_invP _ k0 DA hAb t w ht0, ev_shiftP, hxt, hwt]
    rfl
  set dD := P.D.length - 1 with hdDdef
  have hevD : aeval S'.x ((toPoly P'.D).map ι) =
      t ^ dD * aeval S.x ((toPoly P.D).map ι) * t ^ (DA + 2 - dD) := by
    show aeval t _ = _
    rw [hD', toPoly_mul, toPoly_reflectC _ _ hsDl, toPoly_xPowC, toPoly_compC, toPoly_shiftC,
      Polynomial.map_mul, map_mul, Polynomial.map_pow, map_X, map_pow, aeval_X, ← reflect_map,
      aeval_reflect _ _ _ t ht0]
    · rw [Polynomial.map_comp, aeval_comp]
      congr 2
      simp [← hxt, add_comm]
      rfl
    · refine natDegree_map_le.trans ?_
      rw [← toPoly_shiftC, ← toPoly_compC]
      refine (natDegree_toPoly_le_length _).trans ?_
      omega
  have hid : (S'.fE P' ι : E) = 1 / τ * (S.fE P ι : E) := by
    show S'.evXY _ / aeval S'.x _ = 1 / τ * (S.evXY _ / aeval S.x _)
    rw [hevA, hevD, hτ]
    have hm : dD + (DA + 2 - dD) = DA + 2 := by omega
    by_cases hDx : aeval S.x ((toPoly P.D).map ι) = 0
    · rw [hDx]; simp
    · rw [show t ^ dD * aeval S.x ((toPoly P.D).map ι) * t ^ (DA + 2 - dD) =
        aeval S.x ((toPoly P.D).map ι) * t ^ (dD + (DA + 2 - dD)) by ring, hm, pow_add]
      field_simp
  exact ⟨S', rfl, rfl, hS'F, hid⟩

end MobCurveEx

end Curves
