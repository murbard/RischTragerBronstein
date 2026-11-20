import RischTragerBronstein.Curves.ProcLog

/-!
# Orders along certified branches

* `order_ofPS_eq`: the order of a power series from its first coefficients;
* `ordWFin_spec`: if `ordWFin W a c yt = some o`, then `W(x, y)` has order `o` along the certified
  branch; `ordQFin_spec`: `Q(x)` has order `ordC (Q(a + Tᴺ))`;
* `ordWInf_spec`, `order_Q_inf`: the same above infinity.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

lemma order_ofPS_eq {K : Type*} [Field K] (V : PowerSeries K) (o : ℕ)
    (h0 : ∀ j < o, PowerSeries.coeff j V = 0) (h1 : PowerSeries.coeff o V ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ K V).order = o := by
  have hne : HahnSeries.ofPowerSeries ℤ K V ≠ 0 := fun h ↦ h1 (by
    have := congrArg (fun z : LaurentSeries K ↦ z.coeff (o : ℤ)) h
    simpa [LaurentSeries.coeff_ofPS] using this)
  have hc : (HahnSeries.ofPowerSeries ℤ K V).coeff (o : ℤ) ≠ 0 := by
    simpa [LaurentSeries.coeff_ofPS] using h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra hlt
  push Not at hlt
  have hco : (HahnSeries.ofPowerSeries ℤ K V).coeff (HahnSeries.ofPowerSeries ℤ K V).order ≠ 0 :=
    HahnSeries.coeff_order_eq_zero.not.mpr hne
  have hnn : 0 ≤ (HahnSeries.ofPowerSeries ℤ K V).order := by
    by_contra hneg
    push Not at hneg
    exact hco (by rw [LaurentSeries.coeff_ofPS, if_neg (by omega)])
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le hnn
  apply hco
  rw [ht] at hlt ⊢
  rw [LaurentSeries.coeff_ofPS, if_pos (by omega)]
  simp only [Int.toNat_natCast]
  exact h0 t (by omega)

lemma le_foldr_max' (g : ℕ → ℕ) : ∀ (l : List ℕ) (j : ℕ), j ∈ l →
    g j ≤ l.foldr (fun j m ↦ max m (g j)) 0
  | [], _, h => by simp at h
  | a :: l, j, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_right _ _
    · exact (le_foldr_max' g l j h).trans (le_max_left _ _)

lemma invOK_invDeg {F : Type*} [Field F] [DecidableEq F] (W : BPoly F) (k : ℕ) :
    InvOK k (invDeg W k) 0 W := by
  intro j hj
  have : (W.getD j []).length + k * j - 1 ≤ invDeg W k :=
    le_foldr_max' (fun j ↦ (W.getD j []).length + k * j - 1) _ j (List.mem_range.mpr hj)
  simp only [zero_add]
  omega

section Sem

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- The element `W(x, y)`. -/
noncomputable def wE (ψ₀ : F →+* C) (W : BPoly F) : C⟮S.x⟯⟮S.y⟯ :=
  ⟨S.evXY ((toB W).map (mapRingHom ψ₀)), S.evXY_mem _⟩

/-- The element `Q(x)`. -/
noncomputable def qE (ψ₀ : F →+* C) (Q : CPoly F) : C⟮S.x⟯⟮S.y⟯ :=
  ⟨aeval S.x ((toPoly Q).map ψ₀), S.aeval_mem _⟩

lemma embG_qE (ψ₀ : F →+* C) (Q : CPoly F) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    S.embG g hg Y hY (S.qE ψ₀ Q) = g ((toPoly Q).map ψ₀) :=
  S.embG_polyX g hg Y hY _ _

lemma embG_wE (ψ₀ : F →+* C) (W : BPoly F) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    S.embG g hg Y hY (S.wE ψ₀ W) = (((toB W).map (mapRingHom ψ₀)).map g).eval Y := by
  have := S.eval_W_branch g hg Y hY (S.wE ψ₀ W) ((toB W).map (mapRingHom ψ₀)) 1
    (by rw [map_one, mul_one]; rfl)
  rw [this, map_one, mul_one]

/-- **The order of `W(x, y)` along a certified finite branch.** -/
theorem ordWFin_spec (ψ₀ : F →+* C) (W : BPoly F) (a : F) (c : BranchCert F) (hN : 0 < c.N)
    (Y : PowerSeries K)
    (hY : (S.F.map (branchSub c.N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0) (yt : CPoly F)
    (hy : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (o : ℕ) (ho : ordWFin W a c yt = some o) :
    (S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
      (HahnSeries.ofPowerSeries ℤ K Y) hY (S.wE ψ₀ W)).order = o := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set Wk := bivEval W (shiftC a c.N) yt with hWk
  simp only [ordWFin] at ho
  split_ifs at ho with hlt
  obtain rfl := Option.some.inj ho
  set G := (toB W).map (thetaN ψ a c.N) with hG
  have hGmap : ((toB W).map (mapRingHom ψ₀)).map (branchSub c.N (algebraMap C K (ψ₀ a))) =
      G.map (HahnSeries.ofPowerSeries ℤ K) := by
    rw [hG, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun P ↦ (ofPS_thetaN ψ₀ a c.N P).symm
  rw [S.embG_wE, hGmap, eval_map, eval₂_at_apply]
  have h2 : (PowerSeries.X : PowerSeries K) ^ c.prec ∣ G.eval Y - thetaT ψ (toPoly Wk) := by
    rw [hWk, thetaT_bivEval, ← hG]
    exact hy.trans (sub_dvd_eval_sub _ _ _)
  have hco : ∀ j < c.prec, PowerSeries.coeff j (G.eval Y) = ψ (Wk.getD j 0) := fun j hj ↦ by
    have := (PowerSeries.X_pow_dvd_iff.mp h2) j hj
    rw [map_sub, coeff_thetaT, sub_eq_zero] at this
    exact this
  refine order_ofPS_eq _ _ (fun j hj ↦ ?_) ?_
  · rw [hco j (by omega), getD_lt_ordC Wk j hj, map_zero]
  · rw [hco _ hlt.1]
    exact (map_ne_zero_iff ψ ((algebraMap C K).injective.comp ψ₀.injective)).mpr
      (getD_ordC Wk hlt.2)

/-- **The order of `Q(x)` along a finite branch.** -/
theorem ordQFin_spec (ψ₀ : F →+* C) (Q : CPoly F) (hQ : toPoly Q ≠ 0) (a : F) (N : ℕ)
    (hN : 0 < N) :
    (branchSub (K := K) N (algebraMap C K (ψ₀ a)) ((toPoly Q).map ψ₀)).order = ordQFin Q a N := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set Qa := compC Q (shiftC a N) with hQa
  have hQmap : branchSub N (algebraMap C K (ψ₀ a)) ((toPoly Q).map ψ₀) =
      HahnSeries.ofPowerSeries ℤ K (thetaT ψ (toPoly Qa)) := by
    rw [← ofPS_thetaN, hQa, toPoly_compC, toPoly_shiftC]
    rfl
  have hne : branchSub (K := K) N (algebraMap C K (ψ₀ a)) ((toPoly Q).map ψ₀) ≠ 0 :=
    (map_ne_zero_iff _ (branchSub_injective N hN _)).mpr
      (by rw [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact hQ)
  have hlt : ordC Qa < Qa.length := by
    by_contra hge
    apply hne
    rw [hQmap]
    have : thetaT ψ (toPoly Qa) = 0 := by
      ext j
      rw [coeff_thetaT, map_zero]
      by_cases hj : j < Qa.length
      · rw [getD_lt_ordC Qa j (by omega), map_zero]
      · rw [List.getD_eq_default _ _ (by omega), map_zero]
    rw [this, map_zero]
  rw [hQmap, ordQFin]
  refine order_ofPS_eq _ _ (fun j hj ↦ ?_) ?_
  · rw [coeff_thetaT, getD_lt_ordC Qa j hj, map_zero]
  · rw [coeff_thetaT]
    exact (map_ne_zero_iff ψ ((algebraMap C K).injective.comp ψ₀.injective)).mpr
      (getD_ordC Qa hlt)

/-- **The order of `W(x, y)` along a certified branch above infinity.** -/
theorem ordWInf_spec (ψ₀ : F →+* C) (W : BPoly F) (k : ℕ) (c : BranchCert F) (hN : 0 < c.N)
    (w : PowerSeries K)
    (hY : (S.F.map (infSub c.N)).eval
      (single (-((k * c.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F)
    (hw : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt))
    (o : ℤ) (ho : ordWInf W k c wt = some o) :
    (S.embG (infSub c.N) (infSub_injective c.N hN)
      (single (-((k * c.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY
        (S.wE ψ₀ W)).order = o := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set DW := invDeg W k with hDW
  set Wk := bivEval (invB W k DW) (shiftC 0 c.N) wt with hWk
  simp only [ordWInf] at ho
  split_ifs at ho with hlt
  obtain rfl := Option.some.inj ho
  set G := (toB (invB W k DW)).map (thetaN ψ 0 c.N) with hG
  rw [S.embG_wE, eval_invB ψ₀ c.N hN k DW w W (invOK_invDeg W k), ← hG]
  have h2 : (PowerSeries.X : PowerSeries K) ^ c.prec ∣ G.eval w - thetaT ψ (toPoly Wk) := by
    rw [hWk, thetaT_bivEval, ← hG]
    exact hw.trans (sub_dvd_eval_sub _ _ _)
  have hco : ∀ j < c.prec, PowerSeries.coeff j (G.eval w) = ψ (Wk.getD j 0) := fun j hj ↦ by
    have := (PowerSeries.X_pow_dvd_iff.mp h2) j hj
    rw [map_sub, coeff_thetaT, sub_eq_zero] at this
    exact this
  have hV : (HahnSeries.ofPowerSeries ℤ K (G.eval w)).order = ordC Wk := by
    refine order_ofPS_eq _ _ (fun j hj ↦ ?_) ?_
    · rw [hco j (lt_trans hj hlt.1), getD_lt_ordC Wk j hj, map_zero]
    · rw [hco _ hlt.1]
      exact (map_ne_zero_iff ψ ((algebraMap C K).injective.comp ψ₀.injective)).mpr
        (getD_ordC Wk hlt.2)
  have hV0 : HahnSeries.ofPowerSeries ℤ K (G.eval w) ≠ 0 := fun h ↦ by
    have := getD_ordC Wk hlt.2
    apply this
    have h' := congrArg (fun z : LaurentSeries K ↦ z.coeff (ordC Wk : ℤ)) h
    simp only [LaurentSeries.coeff_ofPS, HahnSeries.coeff_zero] at h'
    rw [if_pos (by omega), Int.toNat_natCast, hco _ hlt.1] at h'
    exact (map_eq_zero_iff ψ ((algebraMap C K).injective.comp ψ₀.injective)).mp h'
  rw [HahnSeries.order_mul (single_ne_zero one_ne_zero) hV0, HahnSeries.order_single one_ne_zero,
    hV]

omit [CharZero F] [DecidableEq F] in
/-- The order of `Q(x)` above infinity. -/
theorem order_Q_inf (ψ₀ : F →+* C) (Q : F[X]) (hQ : Q ≠ 0) (N : ℕ) (hN : 0 < N) :
    (infSub (C := C) (K := K) N (Q.map ψ₀)).order = -((N * Q.natDegree : ℕ) : ℤ) := by
  rw [order_infSub N hN _ ((Polynomial.map_ne_zero_iff ψ₀.injective).mpr hQ),
    natDegree_map_eq_of_injective ψ₀.injective]
  push_cast; ring

end CurveData

end Sem

end Curves
