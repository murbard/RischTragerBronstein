import RischTragerBronstein.Curves.PoleBounds

/-!
# Evaluating functions along certified branches above infinity

Above infinity (`x = T⁻ᴺ`) the roots are `Y = T^{−kN} w` with `w` the roots of the inverted
equation `F'(Tᴺ, w) = 0` (`invF F 0 k`, certified at `a = 0`). For `z = W(x, y)/Q(x)`:

  `W(T⁻ᴺ, T^{−kN} w) = T^{−N D_W} W'(Tᴺ, w)`,  `W' = invB W k D_W` (`Wᵢ` reflected at `D_W − k i`),

  `Q(T⁻ᴺ) = T^{−N deg Q} rev(Q)(Tᴺ)`,  `rev(Q)(0) = lc Q ≠ 0`,

so (`phi_repr_inf`) `φ(z) = T^{−N(D_W − deg Q)} V` with
`V ≡ divTrunc (W'(Tᴺ, w̃)) (rev Q (Tᴺ)) prec (mod T^prec)`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Refl

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Tᴹ P(1/T)` for `P` of length `≤ M + 1`. -/
def reflectC (M : ℕ) (P : CPoly F) : CPoly F := List.ofFn fun j : Fin (M + 1) ↦ P.getD (M - j) 0

/-- The inverted bivariate polynomial: `Wᵢ` reflected at `D − k i`. -/
def invBAux (k D : ℕ) : ℕ → BPoly F → BPoly F
  | _, [] => []
  | i, c :: W => reflectC (D - k * i) c :: invBAux k D (i + 1) W

/-- `invB W k D`. -/
def invB (W : BPoly F) (k D : ℕ) : BPoly F := invBAux k D 0 W

lemma toPoly_reflectC (M : ℕ) (P : CPoly F) (hP : P.length ≤ M + 1) :
    toPoly (reflectC M P) = reflect M (toPoly P) := by
  ext j
  rw [coeff_toPoly, coeff_reflect, coeff_toPoly, reflectC]
  by_cases hj : j ≤ M
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn,
      revAt_le hj]
  · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
      revAt_eq_self_of_lt (by omega), List.getD_eq_default _ _ (by omega)]

end Refl

section InfSem

variable {F : Type*} [Field F] [DecidableEq F]
variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The size condition on `W` for `invBAux`. -/
def InvOK (k D : ℕ) (i : ℕ) (W : BPoly F) : Prop :=
  ∀ j < W.length, (W.getD j []).length + k * (i + j) ≤ D + 1

lemma infSub_term (ψ₀ : F →+* C) (N : ℕ) (hN : 0 < N) (k D i : ℕ) (c : CPoly F)
    (hc : c.length + k * i ≤ D + 1) (w : PowerSeries K) :
    infSub N ((toPoly c).map ψ₀) * (single (-((k * N : ℕ) : ℤ)) (1 : K) *
      ofPowerSeries ℤ K w) ^ i =
      single (-((N * D : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (thetaN ((algebraMap C K).comp ψ₀) 0 N (toPoly (reflectC (D - k * i) c)) *
          w ^ i) := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  by_cases hc0 : c = []
  · subst hc0
    have h0 : toPoly (reflectC (D - k * i) ([] : CPoly F)) = 0 := by
      rw [toPoly_reflectC _ _ (by simp), toPoly_nil, reflect_zero]
    rw [h0, map_zero, zero_mul, map_zero, mul_zero, toPoly_nil, Polynomial.map_zero, map_zero,
      zero_mul]
  have hlen : 1 ≤ c.length := List.length_pos_iff.mpr hc0
  have hki : k * i ≤ D := by omega
  set M := D - k * i with hM
  have hdeg : (toPoly c).natDegree ≤ M := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_
    rw [coeff_toPoly, List.getD_eq_default _ _ (by have : M < j := by exact_mod_cast hj
                                                   omega)]
  have hdeg' : ((toPoly c).map ψ₀).natDegree ≤ M := by
    rw [natDegree_map_eq_of_injective ψ₀.injective]; exact hdeg
  rw [toPoly_reflectC _ _ (by omega), infSub_reflect N _ M hdeg', reflect_map]
  have hb := ofPS_thetaN (K := K) ψ₀ 0 N (reflect M (toPoly c))
  rw [map_zero, map_zero] at hb
  rw [← hb, mul_pow, single_pow, one_pow, ← map_pow, map_mul]
  rw [show ofPowerSeries ℤ K (thetaN ψ 0 N (reflect M (toPoly c))) *
      single (-((N : ℕ) * M : ℤ)) (1 : K) *
      (single (i • -((k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K (w ^ i)) =
      (single (-((N : ℕ) * M : ℤ)) (1 : K) * single (i • -((k * N : ℕ) : ℤ)) (1 : K)) *
        (ofPowerSeries ℤ K (thetaN ψ 0 N (reflect M (toPoly c))) *
          ofPowerSeries ℤ K (w ^ i)) by ring, single_mul_single, one_mul]
  congr 2
  rw [nsmul_eq_mul, hM]
  push_cast [Nat.cast_sub hki]
  ring

lemma eval_invBAux (ψ₀ : F →+* C) (N : ℕ) (hN : 0 < N) (k D : ℕ) (w : PowerSeries K) :
    ∀ (W : BPoly F) (i : ℕ), InvOK k D i W →
      (((toB W).map (mapRingHom ψ₀)).map (infSub N)).eval
          (single (-((k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K w) *
        (single (-((k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K w) ^ i =
      single (-((N * D : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (((toB (invBAux k D i W)).map
          (thetaN ((algebraMap C K).comp ψ₀) 0 N)).eval w * w ^ i) := by
  intro W
  induction W with
  | nil => intro i _; simp [invBAux]
  | cons c W ih =>
    intro i hok
    have h0 : c.length + k * i ≤ D + 1 := by
      have := hok 0 (by simp); simpa using this
    have hW : InvOK k D (i + 1) W := fun j hj ↦ by
      have := hok (j + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
    have hih := ih (i + 1) hW
    simp only [invBAux, toB_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, eval_add, eval_mul, eval_C, eval_X, coe_mapRingHom]
    set Y := single (-((k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K w with hY
    rw [add_mul, infSub_term ψ₀ N hN k D i c h0 w]
    rw [show Y * (((toB W).map (mapRingHom ψ₀)).map (infSub N)).eval Y * Y ^ i =
      (((toB W).map (mapRingHom ψ₀)).map (infSub N)).eval Y * Y ^ (i + 1) by ring, hih, add_mul,
      map_add, mul_add]
    congr 2
    ring

/-- `W(T⁻ᴺ, T^{−kN} w) = T^{−N D} W'(Tᴺ, w)`. -/
lemma eval_invB (ψ₀ : F →+* C) (N : ℕ) (hN : 0 < N) (k D : ℕ) (w : PowerSeries K) (W : BPoly F)
    (hW : InvOK k D 0 W) :
    (((toB W).map (mapRingHom ψ₀)).map (infSub N)).eval
        (single (-((k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K w) =
      single (-((N * D : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (((toB (invB W k D)).map (thetaN ((algebraMap C K).comp ψ₀) 0 N)).eval w) := by
  have := eval_invBAux ψ₀ N hN k D w W 0 hW
  rwa [pow_zero, mul_one, pow_zero, mul_one] at this

end InfSem

section InfCert

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- **Certified branches above infinity.** -/
theorem certInf_spec (Fc : BPoly F) (n : ℕ) (hmon : (toB Fc).Monic) (hn : (toB Fc).natDegree = n)
    (k : ℕ) (hok : InvOK k (k * n) 0 Fc) (hmon' : (toB (invB Fc k (k * n))).Monic)
    (hn' : (toB (invB Fc k (k * n))).natDegree = n) (c : BranchCert F)
    (h : certCheck (invB Fc k (k * n)) n 0 c = true) (ψ₀ : F →+* C) :
    ∃ w : Fin n → PowerSeries K,
      (∀ j : Fin n, (PowerSeries.X : PowerSeries K) ^ c.prec ∣
        w j - thetaT ((algebraMap C K).comp ψ₀) (toPoly (c.ys.getD j []))) ∧
      ((toB Fc).map (mapRingHom ψ₀)).map (infSub c.N) =
        ∏ j, (X - Polynomial.C (single (-((k * c.N : ℕ) : ℤ)) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (w j))) := by
  classical
  have hN : 0 < c.N := by
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1
  obtain ⟨w, hw, hwinj, hsplit⟩ :=
    certCheck_spec (K := K) (invB Fc k (k * n)) n hmon' hn' 0 c h ψ₀
  refine ⟨w, hw, ?_⟩
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  have hroot : ∀ j, (((toB Fc).map (mapRingHom ψ₀)).map (infSub c.N)).eval
      (single (-((k * c.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K (w j)) = 0 := by
    intro j
    rw [eval_invB ψ₀ c.N hN k (k * n) (w j) Fc hok]
    have h1 : (((toB (invB Fc k (k * n))).map (mapRingHom ψ₀)).map
        (branchSub c.N (algebraMap C K (ψ₀ 0)))).eval (HahnSeries.ofPowerSeries ℤ K (w j)) = 0 := by
      rw [hsplit, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    rw [Polynomial.map_map] at h1
    have e : (branchSub (C := C) (K := K) c.N (algebraMap C K (ψ₀ 0))).comp (mapRingHom ψ₀) =
        (HahnSeries.ofPowerSeries ℤ K).comp (thetaN ψ 0 c.N) :=
      RingHom.ext fun P ↦ (ofPS_thetaN ψ₀ 0 c.N P).symm
    rw [e, ← Polynomial.map_map, eval_map, eval₂_at_apply] at h1
    rw [(map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h1, map_zero, mul_zero]
  have hinj : Function.Injective fun j ↦
      single (-((k * c.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K (w j) := by
    intro i j hij
    have h1 : HahnSeries.ofPowerSeries ℤ K (w i) = HahnSeries.ofPowerSeries ℤ K (w j) := by
      have hs : single (-((k * c.N : ℕ) : ℤ)) (1 : K) ≠ 0 := single_ne_zero one_ne_zero
      exact mul_left_cancel₀ hs hij
    exact hwinj (HahnSeries.ofPowerSeries_injective h1)
  exact eq_prod_of_distinct_roots _ ((hmon.map _).map _)
    (by rw [(hmon.map _).natDegree_map, hmon.natDegree_map, hn]) _ hinj hroot

end InfCert

section InfRepr

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- The approximation step shared by all branch evaluations. -/
lemma approx_div (ψ : F →+* K) (W : BPoly F) (a : F) (N : ℕ) (y : PowerSeries K) (yt : CPoly F)
    (prec : ℕ) (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ y - thetaT ψ (toPoly yt))
    (U : CPoly F) (hU0 : U.getD 0 0 ≠ 0) :
    (PowerSeries.X : PowerSeries K) ^ prec ∣
      ((toB W).map (thetaN ψ a N)).eval y * (thetaT ψ (toPoly U))⁻¹ -
        thetaT ψ (toPoly (divTrunc (bivEval W (shiftC a N) yt) U prec)) := by
  set U' := thetaT ψ (toPoly U) with hU'
  have hUc : PowerSeries.constantCoeff U' ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hU', coeff_thetaT]
    exact (map_ne_zero_iff ψ ψ.injective).mpr hU0
  set G := (toB W).map (thetaN ψ a N)
  set Wk := bivEval W (shiftC a N) yt
  refine X_pow_dvd_of_mul_unit hUc ?_
  have h1 : G.eval y * U'⁻¹ * U' = G.eval y := by
    rw [mul_assoc, PowerSeries.inv_mul_cancel U' hUc, mul_one]
  have h2 : (PowerSeries.X : PowerSeries K) ^ prec ∣ G.eval y - thetaT ψ (toPoly Wk) := by
    rw [thetaT_bivEval]
    exact hy.trans (sub_dvd_eval_sub _ _ _)
  have h3 : (PowerSeries.X : PowerSeries K) ^ prec ∣ thetaT ψ (toPoly Wk) -
      thetaT ψ (toPoly (divTrunc Wk U prec)) * U' := by
    rw [hU', ← map_mul, PowerSeries.X_pow_dvd_iff]
    intro j hj
    rw [map_sub, coeff_thetaT, thetaT_apply, Polynomial.coeff_coe, coeff_map,
      mul_comm (toPoly (divTrunc Wk U prec)), coeff_mul_divTrunc Wk U hU0 prec j hj, sub_self]
  have := dvd_add h2 h3
  rw [sub_mul, h1]
  convert this using 1
  ring

lemma thetaN_zero_eq (ψ : F →+* K) (N : ℕ) (R : CPoly F) :
    thetaN ψ 0 N (toPoly R) = thetaT ψ (toPoly (compC R (shiftC 0 N))) := by
  rw [toPoly_compC, toPoly_shiftC]; rfl

lemma compC_shift_getD_zero (R : CPoly F) (N : ℕ) (hN : 0 < N) :
    (compC R (shiftC 0 N)).getD 0 0 = R.getD 0 0 := by
  rw [← coeff_toPoly, ← coeff_toPoly, toPoly_compC, toPoly_shiftC, coeff_zero_eq_eval_zero,
    coeff_zero_eq_eval_zero, eval_comp]
  simp [zero_pow hN.ne']

namespace CurveData

variable (S : CurveData C L)

/-- **A function along a certified branch above infinity.** -/
theorem phi_repr_inf (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (k N : ℕ) (hN : 0 < N) (w : PowerSeries K)
    (hY : (S.F.map (infSub N)).eval
      (single (-((k * N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F) (prec : ℕ)
    (hw : (PowerSeries.X : PowerSeries K) ^ prec ∣ w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt))
    (z : C⟮S.x⟯⟮S.y⟯) (W : BPoly F) (Q : CPoly F)
    (hz : (z : L) * aeval S.x ((toPoly Q).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀)))
    (DW : ℕ) (hWok : InvOK k DW 0 W) (hQ : 0 < Q.length) (hQl : Q.getD (Q.length - 1) 0 ≠ 0) :
    ∃ V : PowerSeries K,
      S.embG (infSub N) (infSub_injective N hN)
          (single (-((k * N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY z =
        single (-((N * DW : ℕ) : ℤ) + ((N * (Q.length - 1) : ℕ) : ℤ)) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K V ∧
      (PowerSeries.X : PowerSeries K) ^ prec ∣ V - thetaT ((algebraMap C K).comp ψ₀)
        (toPoly (divTrunc (bivEval (invB W k DW) (shiftC 0 N) wt)
          (compC (reflectC (Q.length - 1) Q) (shiftC 0 N)) prec)) := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set dQ := Q.length - 1 with hdQ
  set Y := single (-((k * N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w with hYdef
  set U := compC (reflectC dQ Q) (shiftC 0 N) with hU
  set U' := thetaT ψ (toPoly U) with hU'
  have hU0 : U.getD 0 0 ≠ 0 := by
    rw [hU, compC_shift_getD_zero _ _ hN, reflectC, List.getD_eq_getElem _ _ (by simp),
      List.getElem_ofFn]
    simpa using hQl
  have hUc : PowerSeries.constantCoeff U' ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hU', coeff_thetaT]
    exact (map_ne_zero_iff ψ ψ.injective).mpr hU0
  set φ := S.embG (infSub N) (infSub_injective N hN) Y hY with hφ
  have hWbr := S.eval_W_branch (infSub N) (infSub_injective N hN) Y hY z
    ((toB W).map (mapRingHom ψ₀)) ((toPoly Q).map ψ₀) hz
  rw [eval_invB ψ₀ N hN k DW w W hWok] at hWbr
  have hQt := infSub_term (K := K) ψ₀ N hN 0 dQ 0 Q (by omega) w
  rw [pow_zero, mul_one, pow_zero, mul_one, zero_mul, Nat.sub_zero, thetaN_zero_eq, ← hU,
    ← hU'] at hQt
  rw [hQt] at hWbr
  set G := (toB (invB W k DW)).map (thetaN ψ 0 N) with hG
  refine ⟨G.eval w * U'⁻¹, ?_, approx_div ψ (invB W k DW) 0 N w wt prec hw U hU0⟩
  have hU'inv : HahnSeries.ofPowerSeries ℤ K U' * HahnSeries.ofPowerSeries ℤ K U'⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel U' hUc, map_one]
  have hs : single (((N * dQ : ℕ) : ℤ)) (1 : K) * single (-((N * dQ : ℕ) : ℤ)) (1 : K) = 1 := by
    rw [single_mul_single, add_neg_cancel, one_mul]; rfl
  calc φ z = φ z * (single (((N * dQ : ℕ) : ℤ)) (1 : K) * single (-((N * dQ : ℕ) : ℤ)) (1 : K)) *
        (HahnSeries.ofPowerSeries ℤ K U' * HahnSeries.ofPowerSeries ℤ K U'⁻¹) := by
        rw [hs, hU'inv, mul_one, mul_one]
    _ = single (((N * dQ : ℕ) : ℤ)) (1 : K) *
        (φ z * (single (-((N * dQ : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K U')) *
        HahnSeries.ofPowerSeries ℤ K U'⁻¹ := by ring
    _ = _ := by
        rw [← hWbr, map_mul]
        rw [show single (((N * dQ : ℕ) : ℤ)) (1 : K) * (single (-((N * DW : ℕ) : ℤ)) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (G.eval w)) * HahnSeries.ofPowerSeries ℤ K U'⁻¹ =
          (single (-((N * DW : ℕ) : ℤ)) (1 : K) * single (((N * dQ : ℕ) : ℤ)) (1 : K)) *
          (HahnSeries.ofPowerSeries ℤ K (G.eval w) * HahnSeries.ofPowerSeries ℤ K U'⁻¹) by ring,
          single_mul_single, one_mul]

end CurveData

end InfRepr

end Curves
