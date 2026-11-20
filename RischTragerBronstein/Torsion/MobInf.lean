import RischTragerBronstein.Torsion.MobCurve
import RischTragerBronstein.Torsion.LSpace
import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# No residues above infinity after a Möbius transformation

**`resInf_mob_eq_zero`**: if `P'` is the Möbius transform of `P` at `e` (`mobCheck`) with
`D(e) ≠ 0`, then all residues of `P'` computed above infinity vanish: above `t = ∞` (that is,
`x = e`) the transformed integrand is `−t⁻² · A(x, y)/D(x)`, with `x = e + Tᴺ` and `y` integral
over `K⟦T⟧`, so it vanishes to order `≥ 2N` in the local parameter `T` (`t = T⁻ᴺ`).

* `orderTop_nonneg_of_monic_root`: a root of a monic polynomial with coefficients of
  non-negative order has non-negative order.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Val

variable {K : Type*} [Field K]

/-- **Roots of monic polynomials over `K⟦T⟧` lie in `K⟦T⟧`.** -/
lemma orderTop_nonneg_of_monic_root (p : (LaurentSeries K)[X]) (hp : p.Monic)
    (hc : ∀ i, 0 ≤ (p.coeff i).orderTop) (z : LaurentSeries K) (hz : p.eval z = 0) :
    0 ≤ z.orderTop := by
  set v := HahnSeries.addVal ℤ K with hv
  have hvx : ∀ x : LaurentSeries K, v x = x.orderTop := fun x ↦ HahnSeries.addVal_apply
  by_contra hneg
  push Not at hneg
  have hz0 : z ≠ 0 := by rintro rfl; simp at hneg
  obtain ⟨m, hm⟩ : ∃ m : ℤ, z.orderTop = m := ⟨z.order, (HahnSeries.order_eq_orderTop_of_ne_zero hz0).symm⟩
  have hm0 : m < 0 := by rw [hm] at hneg; exact_mod_cast hneg
  set n := p.natDegree
  rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at hz
  have hzn : z ^ n = -∑ i ∈ Finset.range n, p.coeff i * z ^ i := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hz
  have h1 : v (z ^ n) = ((n * m : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_pow, hvx, hm]; push_cast; rfl
  have h2 : ((n * m : ℤ) : WithTop ℤ) < v (∑ i ∈ Finset.range n, p.coeff i * z ^ i) := by
    refine AddValuation.map_lt_sum' v (WithTop.coe_lt_top _) fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [AddValuation.map_mul, AddValuation.map_pow, hvx, hvx, hm]
    have hlt : ((n * m : ℤ) : WithTop ℤ) < ((i * m : ℤ) : WithTop ℤ) := by
      have : (i : ℤ) < n := by exact_mod_cast hi'
      exact_mod_cast (by nlinarith : (n : ℤ) * m < i * m)
    refine lt_of_lt_of_le hlt ?_
    have e : (i • (m : WithTop ℤ)) = ((i * m : ℤ) : WithTop ℤ) := by push_cast; rfl
    rw [e]
    exact le_add_of_nonneg_left (hc i)
  rw [← h1, hzn, AddValuation.map_neg] at h2
  exact lt_irrefl _ h2

lemma orderTop_ofPS_nonneg (p : PowerSeries K) : 0 ≤ (ofPowerSeries ℤ K p).orderTop := by
  by_cases h : ofPowerSeries ℤ K p = 0
  · rw [h, HahnSeries.orderTop_zero]; exact le_top
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero h]
  exact_mod_cast order_ofPS_nonneg p

end Val

section BS

variable {C : Type*} [Field C]

lemma orderTop_branchSub_nonneg (N : ℕ) (c : C) (Q : C[X]) :
    0 ≤ (branchSub (C := C) (K := C) N c Q).orderTop := by
  rw [branchSub_apply]; exact orderTop_ofPS_nonneg _

lemma branchSub_X' (N : ℕ) (c : C) :
    branchSub (C := C) (K := C) N c X = HahnSeries.C c + single (N : ℤ) 1 := by
  rw [branchSub_apply, Polynomial.map_X, X_comp, Polynomial.coe_add, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X, map_add, ofPowerSeries_C, ← ofPowerSeries_X_pow]

lemma infSub_X' (N : ℕ) : infSub (C := C) (K := C) N X = single (-(N : ℤ)) 1 := by
  rw [infSub, coe_eval₂RingHom, eval₂_X]

lemma single_neg_inv (N : ℕ) : (single (-(N : ℤ)) (1 : C))⁻¹ = single (N : ℤ) 1 :=
  inv_eq_of_mul_eq_one_right (by rw [single_mul_single, neg_add_cancel, mul_one]; rfl)

end BS

section Mob

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]

set_option maxHeartbeats 4000000 in
/-- **No residues above infinity after a Möbius transformation at a point with `D(e) ≠ 0`.** -/
theorem resInf_mob_eq_zero (S : CurveData C L) (P P' : CurveProb F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (e : F) (k0 DA : ℕ)
    (hmob : mobCheck P P' e k0 DA = true) (hV' : P'.ValidFacts)
    (hDe : (toPoly P.D).eval e ≠ 0) : ∀ wt ∈ P'.inf.ys, P'.resInf wt = 0 := by
  classical
  simp only [mobCheck, Bool.and_eq_true, decide_eq_true_eq] at hmob
  obtain ⟨⟨⟨⟨⟨⟨⟨hn', hFc'⟩, hokF⟩, hA'⟩, hokA⟩, hsDl⟩, hdD⟩, hD'⟩ := hmob
  set c : C := ψ₀ e with hc
  -- the transformed curve
  have hFs : shiftP S.F c = (shiftP (toB P.Fc) e).map (mapRingHom ψ₀) := by rw [hSF, shiftP_map]
  have hInvF : InvOK k0 (k0 * P.n) 0 (shiftB P.Fc e) := invOKb_spec hokF
  have hG : invP (shiftP S.F c) k0 (k0 * P.n) = (toB P'.Fc).map (mapRingHom ψ₀) := by
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
    have h2 := natDegree_map_le (f := ψ₀) (p := (toB (shiftB P.Fc e)).coeff i)
    omega
  set S' := mobCurve S c k0 (k0 * P.n) hM hGm (by rw [hGdeg, hnP]) with hS'
  have hS'F : S'.F = (toB P'.Fc).map (mapRingHom ψ₀) := hG
  set t : L := 1 / (S.x - algebraMap C L c) with ht
  set w : L := S.y * t ^ k0 with hw
  have hxc : S.x - algebraMap C L c ≠ 0 := x_sub_ne S c
  have ht0 : t ≠ 0 := one_div_ne_zero hxc
  have hxt : 1 / t + algebraMap C L c = S.x := by rw [ht, one_div_one_div, sub_add_cancel]
  have hwt : w / t ^ k0 = S.y := by rw [hw]; exact mul_div_cancel_right₀ _ (pow_ne_zero _ ht0)
  -- the transformed integrand
  have hInvA : InvOK k0 DA 0 (shiftB P.A e) := invOKb_spec hokA
  have hAm : (toB P'.A).map (mapRingHom ψ₀) = Polynomial.C (Polynomial.C (-1)) *
      invP (shiftP ((toB P.A).map (mapRingHom ψ₀)) c) k0 DA := by
    rw [hA', toB_mobA, toB_smulB, Polynomial.map_mul, toB_invB _ _ _ hInvA, invP_map, toB_shiftB,
      shiftP_map]
    simp [CPoly.toPoly]
    rfl
  have hAb : ∀ i ≤ (shiftP ((toB P.A).map (mapRingHom ψ₀)) c).natDegree,
      ((shiftP ((toB P.A).map (mapRingHom ψ₀)) c).coeff i).natDegree + k0 * i ≤ DA := by
    intro i hi
    have hsm : shiftP ((toB P.A).map (mapRingHom ψ₀)) c =
        (toB (shiftB P.A e)).map (mapRingHom ψ₀) := by
      rw [toB_shiftB, shiftP_map]
    rw [hsm] at hi ⊢
    have hb := invBound_of_invOK _ _ _ hInvA i (le_trans hi natDegree_map_le)
    rw [coeff_map, coe_mapRingHom]
    have h2 := natDegree_map_le (f := ψ₀) (p := (toB (shiftB P.A e)).coeff i)
    omega
  have hevA : S'.evXY ((toB P'.A).map (mapRingHom ψ₀)) =
      -(t ^ DA * S.evXY ((toB P.A).map (mapRingHom ψ₀))) := by
    show ev _ t w = _
    rw [hAm]
    have e1 : ev (Polynomial.C (Polynomial.C (-1)) *
        invP (shiftP ((toB P.A).map (mapRingHom ψ₀)) c) k0 DA) t w =
        -ev (invP (shiftP ((toB P.A).map (mapRingHom ψ₀)) c) k0 DA) t w := by
      simp [ev, Polynomial.map_mul]
    rw [e1, ev_invP _ k0 DA hAb t w ht0, ev_shiftP, hxt, hwt]
    rfl
  set dD := P.D.length - 1 with hdDdef
  have hevD : aeval S'.x ((toPoly P'.D).map ψ₀) =
      t ^ dD * aeval S.x ((toPoly P.D).map ψ₀) * t ^ (DA + 2 - dD) := by
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
  have hDx : aeval S.x ((toPoly P.D).map ψ₀) ≠ 0 := S.aeval_x_ne_zero _ (fun h0 ↦ by
    rw [Polynomial.map_eq_zero_iff ψ₀.injective] at h0
    rw [h0, eval_zero] at hDe; exact hDe rfl)
  have hid : (S'.fE P' ψ₀ : L) = (-t ^ 2)⁻¹ *
      (S.evXY ((toB P.A).map (mapRingHom ψ₀)) * (aeval S.x ((toPoly P.D).map ψ₀))⁻¹) := by
    show S'.evXY _ / aeval S'.x _ = _
    rw [hevA, hevD]
    have hm : dD + (DA + 2 - dD) = DA + 2 := by omega
    rw [show t ^ dD * aeval S.x ((toPoly P.D).map ψ₀) * t ^ (DA + 2 - dD) =
      aeval S.x ((toPoly P.D).map ψ₀) * t ^ (dD + (DA + 2 - dD)) by ring, hm, pow_add]
    field_simp
  -- the expansion above `t = ∞`
  intro wt hwt'
  obtain ⟨hl0, -⟩ := CurveProb.length_ys_of_cert hV'.certInf
  obtain ⟨ws, hws, hs0⟩ := S'.certInfSys (K := C) P' ψ₀ hS'F hV'
  obtain ⟨k, rfl⟩ := S'.index_of_mem P' ψ₀ hS'F hV' _ hl0 wt hwt'
  set N := P'.inf.N with hNdef
  have hN : 0 < N := hV'.infN
  set Y : LaurentSeries C := single (-((P'.k * N : ℕ) : ℤ)) (1 : C) * ofPowerSeries ℤ C (ws k)
    with hYdef
  have hY : (S'.F.map (infSub N)).eval Y = 0 := S'.root_of_split _ _ hs0 k
  have hres := S'.resInf_sem (K := C) P' ψ₀ hS'F hN (ws k) hY _ (hws k) hV'.sf hV'.Dl hV'.okA _
    (S'.fE_spec P' ψ₀ hV')
  -- the elements `x = 1/t + c`, `y = w t^{-k₀}` of the function field
  letI := algebraAdjoinSimple (F := C) S'.x
  set ρ : C⟮S'.x⟯⟮S'.y⟯ →+* L := (C⟮S'.x⟯⟮S'.y⟯).val.toRingHom with hρ
  have hρinj : Function.Injective ρ := ρ.injective
  have hρv : ∀ z : C⟮S'.x⟯⟮S'.y⟯, ρ z = (z : L) := fun _ ↦ rfl
  set pF : C[X] →+* C⟮S'.x⟯⟮S'.y⟯ := (algebraMap C⟮S'.x⟯ C⟮S'.x⟯⟮S'.y⟯).comp (algebraMap C[X] C⟮S'.x⟯) with hpF
  have hpF' : ∀ Q, pF Q = S'.polyF Q := fun _ ↦ rfl
  set t' : C⟮S'.x⟯⟮S'.y⟯ := pF X with ht'
  set w' : C⟮S'.x⟯⟮S'.y⟯ := S'.evT X with hw'
  set X0 : C⟮S'.x⟯⟮S'.y⟯ := t'⁻¹ + pF (Polynomial.C c) with hX0
  set Y0 : C⟮S'.x⟯⟮S'.y⟯ := w' * (t'⁻¹) ^ k0 with hY0
  set f0 : C[X] →+* C⟮S'.x⟯⟮S'.y⟯ := eval₂RingHom (pF.comp Polynomial.C) X0 with hf0
  have hρt : ρ t' = t := by rw [hρv, ht', hpF', S'.coe_polyF, aeval_X]; rfl
  have hρw : ρ w' = w := by rw [hρv, hw', S'.coe_evT]; simp [CurveData.evXY]; rfl
  have hρC : ∀ a : C, ρ (pF (Polynomial.C a)) = algebraMap C L a := fun a ↦ by
    rw [hρv, hpF', S'.coe_polyF, aeval_C]
  have hρf0 : ρ.comp f0 = (aeval S.x).toRingHom := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, hf0, coe_eval₂RingHom, eval₂_C]
      rw [hρC]; simp
    · simp only [RingHom.comp_apply, hf0, coe_eval₂RingHom, eval₂_X, hX0, map_add, map_inv₀, hρt,
        hρC]
      simp [← hxt, one_div]
  have hρY0 : ρ Y0 = S.y := by
    rw [hY0, map_mul, map_pow, map_inv₀, hρt, hρw, ← hwt, div_eq_mul_inv, inv_pow]
  have hρev : ∀ Q : C[X][X], ρ ((Q.map f0).eval Y0) = S.evXY Q := fun Q ↦ by
    rw [eval_map, Polynomial.hom_eval₂, hρf0, hρY0, CurveData.evXY, eval_map]
  set φ := S'.embG (infSub N) (infSub_injective N hN) Y hY with hφ
  have hφt : φ t' = single (-(N : ℤ)) 1 := by
    rw [hφ, ht', hpF', S'.embG_polyF, infSub_X']
  have hφw : φ w' = Y := by rw [hφ, hw', S'.embG_evT]; simp
  have hφC : ∀ a : C, φ (pF (Polynomial.C a)) = HahnSeries.C a := fun a ↦ by
    rw [hφ, hpF', S'.embG_polyF, is_C]; rfl
  have hφf0 : φ.comp f0 = branchSub (C := C) (K := C) N c := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, hf0, coe_eval₂RingHom, eval₂_C]
      rw [hφC, bs_C]; rfl
    · simp only [RingHom.comp_apply, hf0, coe_eval₂RingHom, eval₂_X, hX0, map_add, map_inv₀, hφt,
        hφC]
      rw [single_neg_inv, branchSub_X', add_comm]
  set Z : LaurentSeries C := φ Y0 with hZ
  have hφev : ∀ Q : C[X][X], φ ((Q.map f0).eval Y0) = (Q.map (branchSub N c)).eval Z := fun Q ↦ by
    rw [eval_map, Polynomial.hom_eval₂, hφf0, eval_map]
  -- `y` is integral above `x = c`
  have hZ0 : 0 ≤ Z.orderTop := by
    refine orderTop_nonneg_of_monic_root ((S.F).map (branchSub N c)) (S.monic.map _)
      (fun i ↦ by rw [coeff_map]; exact orderTop_branchSub_nonneg _ _ _) Z ?_
    rw [← hφev]
    have h0 : (S.F.map f0).eval Y0 = 0 := hρinj (by rw [hρev, map_zero]; exact S.root)
    rw [h0, map_zero]
  -- the integrand in the function field
  have hfK : S'.fE P' ψ₀ = (-t' ^ 2)⁻¹ *
      (((toB P.A).map (mapRingHom ψ₀)).map f0).eval Y0 * (f0 ((toPoly P.D).map ψ₀))⁻¹ := by
    refine hρinj ?_
    rw [hρv, hid, map_mul, map_mul, map_inv₀, map_neg, map_pow, hρt, hρev, map_inv₀,
      ← RingHom.comp_apply, hρf0]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring
  -- its order is at least `2N`
  set v := HahnSeries.addVal ℤ C with hv
  have hvx : ∀ x : LaurentSeries C, v x = x.orderTop := fun x ↦ HahnSeries.addVal_apply
  have hT : (-(single (-(N : ℤ)) (1 : C)) ^ 2)⁻¹ = -(single (N : ℤ) (1 : C)) ^ 2 := by
    rw [inv_neg, ← inv_pow, single_neg_inv]
  have hvT : v (-(single (N : ℤ) (1 : C)) ^ 2) = ((2 * N : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_neg, AddValuation.map_pow, hvx, HahnSeries.orderTop_single one_ne_zero]
    push_cast; rfl
  have hA0 : 0 ≤ v ((((toB P.A).map (mapRingHom ψ₀)).map (branchSub N c)).eval Z) := by
    rw [eval_eq_sum_range]
    refine AddValuation.map_le_sum v fun i _ ↦ ?_
    rw [AddValuation.map_mul, AddValuation.map_pow, hvx, hvx, coeff_map]
    exact add_nonneg (orderTop_branchSub_nonneg _ _ _) (nsmul_nonneg hZ0 _)
  have hD0 : v (branchSub (C := C) (K := C) N c ((toPoly P.D).map ψ₀)) = 0 := by
    have hne : branchSub (C := C) (K := C) N c ((toPoly P.D).map ψ₀) ≠ 0 := fun h0 ↦ by
      have := branchSub_injective (C := C) (K := C) N hN c (h0.trans (map_zero _).symm)
      rw [Polynomial.map_eq_zero_iff ψ₀.injective] at this
      rw [this, eval_zero] at hDe; exact hDe rfl
    rw [hvx, ← HahnSeries.order_eq_orderTop_of_ne_zero hne, CurveData.order_branchSub_eq_zero _ _ _ hN]
    · rfl
    · rw [Polynomial.map_map, eval_map, Algebra.algebraMap_self, RingHom.id_comp, hc,
        eval₂_at_apply]
      exact fun h ↦ hDe (ψ₀.injective (by rw [h, map_zero]))
  have hφf : φ (S'.fE P' ψ₀) = -(single (N : ℤ) (1 : C)) ^ 2 *
      (((toB P.A).map (mapRingHom ψ₀)).map (branchSub N c)).eval Z *
      (branchSub (C := C) (K := C) N c ((toPoly P.D).map ψ₀))⁻¹ := by
    rw [hfK, map_mul, map_mul, map_inv₀, map_inv₀, map_neg, map_pow, hφt, hφev,
      ← RingHom.comp_apply φ f0, hφf0, hT]
  have hord : ((2 * N : ℤ) : WithTop ℤ) ≤ (φ (S'.fE P' ψ₀)).orderTop := by
    rw [← hvx, hφf, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv, hD0,
      neg_zero, add_zero, hvT]
    exact le_add_of_nonneg_right hA0
  have hcoef : (φ (S'.fE P' ψ₀)).coeff (N : ℤ) = 0 := by
    refine HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le ?_ hord)
    exact_mod_cast (by omega : (N : ℤ) < 2 * N)
  rw [LaurentSeries.res, SuperData.derivation_infX, mul_comm, coeff_single_mul',
    show (-1 : ℤ) - (-(N : ℤ) - 1) = N by ring, hcoef, mul_zero] at hres
  exact ((algebraMap C C).comp ψ₀).injective (by rw [← hres, map_zero])

end Mob

end Curves
