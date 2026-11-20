import RischTragerBronstein.Mixed.CurveLiouvilleForm
import RischTragerBronstein.Torsion.MobP

/-!
# Positive answers through `decideLogTP` and Möbius transformations are Liouville forms

* `decideLog_of_decideLogTP_true`: a positive answer of `decideLogTP` comes from `decideLog`;
* `liouvilleFormE_of_rescale`: a Liouville form for the rescaled derivation `φ D` gives one for
  `D` (of `f / φ`);
* `decideLogTP_mob_true`: a positive answer after a Möbius transformation is a Liouville form of
  the original integrand.
-/

open Polynomial IntermediateField Differential

namespace Curves

open CPoly Sup

section Pass

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

lemma decideLog_of_decideLogTP_true {redAt : (p : ℕ) → Option (RedFns p F)} {P : CurveProb F}
    {ws : List (LogWit F)} {tws : List (TorsWit F)} {twps : List (TorsWitP F)}
    (h : decideLogTP redAt P ws tws twps = some true) : P.decideLog ws = some true := by
  unfold decideLogTP at h
  split at h
  · rename_i b hb
    obtain rfl := Option.some.inj h
    unfold decideLogT at hb
    split at hb
    · rename_i b' hb'; obtain rfl := Option.some.inj hb; exact hb'
    · split_ifs at hb <;> simp at hb
  · split_ifs at h <;> simp at h

end Pass

section Rescale

variable {E : Type*} [Field E]

lemma liouvilleFormE_of_rescale (d0 : Derivation ℤ E E) (φ : E) (hφ : φ ≠ 0) (f : E)
    (h : @LiouvilleFormE E _ (rescale ⟨d0⟩ φ) f) : @LiouvilleFormE E _ ⟨d0⟩ (φ⁻¹ * f) := by
  obtain ⟨v, l, hl, rfl⟩ := h
  refine ⟨v, l, fun p hp ↦ ⟨?_, (hl p hp).2⟩, ?_⟩
  · have := (hl p hp).1
    change φ * d0 p.1 = 0 at this
    exact (mul_eq_zero.mp this).resolve_left hφ
  · change φ⁻¹ * (φ * d0 v + (l.map fun p ↦ p.1 * (φ * d0 p.2 / p.2)).sum) =
      d0 v + (l.map fun p ↦ p.1 * (d0 p.2 / p.2)).sum
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul, ← List.sum_map_mul_left]
    congr 2
    refine List.map_congr_left fun p _ ↦ ?_
    field_simp

end Rescale

section MobMain

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

set_option maxHeartbeats 4000000 in
/-- **A positive answer after a Möbius transformation is a Liouville form.** -/
theorem decideLogTP_mob_true (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P P' : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι)) (e : F)
    (k0 DA : ℕ) (hmob : mobCheck P P' e k0 DA = true) (ws : List (LogWit F))
    (tws : List (TorsWit F)) (twps : List (TorsWitP F))
    (h : decideLogTP redAt P' ws tws twps = some true) :
    LiouvilleFormE ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  classical
  simp only [mobCheck, Bool.and_eq_true, decide_eq_true_eq] at hmob
  obtain ⟨⟨⟨⟨⟨⟨⟨hn', hFc'⟩, hokF⟩, hA'⟩, hokA⟩, hsDl⟩, hdD⟩, hD'⟩ := hmob
  have hV' := P'.valid_spec (valid_of_decideLogTP h)
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
  -- the variables and the rescaled derivation
  set t : E := 1 / (S.x - algebraMap Kc E c) with ht
  set w : E := S.y * t ^ k0 with hw
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxc : S.x - algebraMap Kc E c ≠ 0 := x_sub_ne S c
  have ht0 : t ≠ 0 := one_div_ne_zero hxc
  have hxt : 1 / t + algebraMap Kc E c = S.x := by rw [ht, one_div_one_div, sub_add_cancel]
  have hwt : w / t ^ k0 = S.y := by rw [hw]; exact mul_div_cancel_right₀ _ (pow_ne_zero _ ht0)
  have ht' : t′ = -t ^ 2 := by
    rw [ht, Derivation.leibniz_div, map_sub, hx, hconstE]
    simp only [Derivation.map_one_eq_zero, smul_eq_mul, mul_zero, sub_zero, mul_one, zero_sub]
    field_simp
  set τ : E := -t ^ 2 with hτ
  have hτ0 : τ ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ht0)
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hconst : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ hconstE r
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hT' : D'.deriv S'.x = 1 := by
    show 1 / τ * d0 t = 1
    rw [hd0, ht']; exact one_div_mul_cancel hτ0
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hconst, hC, map_zero, mul_zero])
  have hgen' : ∀ z : E, z ∈ Kc⟮S'.x⟯⟮S'.y⟯ := by
    intro z
    have hz := hgen z
    rw [← IntermediateField.mem_restrictScalars Kc, adjoin_simple_adjoin_simple] at hz ⊢
    refine (adjoin_le_iff.mpr ?_) hz
    have htm : t ∈ Kc⟮S'.x, S'.y⟯ := subset_adjoin _ _ (Set.mem_insert _ _)
    have hwm : w ∈ Kc⟮S'.x, S'.y⟯ := subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
    intro v hv
    rcases hv with hv | hv
    · rw [hv, ← hxt]
      exact add_mem (div_mem (one_mem _) htm) (IntermediateField.algebraMap_mem _ _)
    · rw [Set.mem_singleton_iff] at hv
      rw [hv, ← hwt]
      exact div_mem hwm (pow_mem htm _)
  have key := @decideLog_true Kc E _ _ _ _ D' hDA' _ _ _ F _ _ _ _ hC S' hT' P' ι hS'F ws
    (decideLog_of_decideLogTP_true h)
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
  rw [hid] at key
  have := liouvilleFormE_of_rescale d0 (1 / τ) (one_div_ne_zero hτ0) _ key
  rwa [one_div, inv_inv, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul] at this

end MobMain

end Curves
