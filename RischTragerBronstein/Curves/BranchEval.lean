import RischTragerBronstein.Curves.CertBranch

/-!
# Evaluating functions along certified branches

`divTrunc W U m`: the first `m` coefficients of the power series `W / U` (`U(0) ≠ 0`), by the
triangular recursion; `divTrunc_spec`, and `thetaT_divTrunc`: modulo `Tᵐ` it agrees with any
power series `V` with `V · U ≡ W`.

For `z = W(x, y)/Q(x)` and a certified branch `yₖ ≡ ỹₖ (mod T^prec)` above `x = a`:
`Q(a + Tᴺ) = T^μ U(T)` (`U(0) ≠ 0`), and (`phi_repr`)

  `φₖ(z) = T^{−μ} · V`,  `V ≡ divTrunc (W(a + Tᴺ, ỹₖ)) U prec  (mod T^prec)`.
-/

open Polynomial IntermediateField

namespace Curves

open CPoly Sup Differential

section Div

variable {F : Type*} [Field F] [DecidableEq F]

/-- The first `m` coefficients of `W / U`. -/
def divTrunc (W U : CPoly F) : ℕ → CPoly F
  | 0 => []
  | m + 1 =>
    let V := divTrunc W U m
    V ++ [(W.getD m 0 - ∑ i ∈ Finset.range m, U.getD (m - i) 0 * V.getD i 0) / U.getD 0 0]

lemma divTrunc_length (W U : CPoly F) (m : ℕ) : (divTrunc W U m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [divTrunc, ih]

lemma divTrunc_getD_succ (W U : CPoly F) (m j : ℕ) (hj : j < m) :
    (divTrunc W U (m + 1)).getD j 0 = (divTrunc W U m).getD j 0 := by
  simp only [divTrunc]
  rw [List.getD_append _ _ _ _ (by rw [divTrunc_length]; exact hj)]

lemma divTrunc_getD_le (W U : CPoly F) (m m' j : ℕ) (hj : j < m) (hm : m ≤ m') :
    (divTrunc W U m').getD j 0 = (divTrunc W U m).getD j 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, divTrunc_getD_succ _ _ _ _ (by omega), ih (by omega)]

lemma divTrunc_getD_last (W U : CPoly F) (m : ℕ) :
    (divTrunc W U (m + 1)).getD m 0 =
      (W.getD m 0 - ∑ i ∈ Finset.range m, U.getD (m - i) 0 * (divTrunc W U m).getD i 0) /
        U.getD 0 0 := by
  simp only [divTrunc]
  rw [List.getD_append_right _ _ _ _ (by rw [divTrunc_length])]
  simp [divTrunc_length]

/-- **The triangular identity**: `∑_{i ≤ j} U_{j−i} Vᵢ = W_j` for `j < m`. -/
lemma divTrunc_spec (W U : CPoly F) (hU : U.getD 0 0 ≠ 0) (m j : ℕ) (hj : j < m) :
    ∑ i ∈ Finset.range (j + 1), U.getD (j - i) 0 * (divTrunc W U m).getD i 0 = W.getD j 0 := by
  rw [Finset.sum_range_succ, Nat.sub_self, divTrunc_getD_le W U (j + 1) m j (Nat.lt_succ_self j) hj,
    divTrunc_getD_last]
  rw [Finset.sum_congr rfl (g := fun i ↦ U.getD (j - i) 0 * (divTrunc W U j).getD i 0) (fun i hi ↦
    by rw [divTrunc_getD_le W U j m i (Finset.mem_range.mp hi) (by omega)])]
  field_simp
  ring

end Div

section DivSem

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

lemma coeff_mul_divTrunc (W U : CPoly F) (hU : U.getD 0 0 ≠ 0) (m j : ℕ) (hj : j < m) :
    (toPoly U * toPoly (divTrunc W U m)).coeff j = W.getD j 0 := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b ↦ (toPoly (divTrunc W U m)).coeff a * (toPoly U).coeff b), ← divTrunc_spec W U hU m j hj]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_toPoly, coeff_toPoly, mul_comm]

lemma X_pow_dvd_thetaT_sub (ψ : F →+* K) (P P' : CPoly F) (m : ℕ)
    (h : ∀ j < m, (toPoly P).coeff j = (toPoly P').coeff j) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ thetaT ψ (toPoly P) - thetaT ψ (toPoly P') := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  rw [map_sub, coeff_thetaT, coeff_thetaT, ← coeff_toPoly, ← coeff_toPoly, h j hj, sub_self]

/-- Cancelling a unit modulo `Tᵐ`. -/
lemma X_pow_dvd_of_mul_unit {V V' U : PowerSeries K} (hU : PowerSeries.constantCoeff U ≠ 0)
    {m : ℕ} (h : (PowerSeries.X : PowerSeries K) ^ m ∣ (V - V') * U) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ V - V' := by
  have e : V - V' = (V - V') * U * U⁻¹ := by
    rw [mul_assoc, PowerSeries.mul_inv_cancel U hU, mul_one]
  rw [e]; exact Dvd.dvd.mul_right h _

end DivSem

section Repr

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **A function along a certified branch**: `φ(z) = T^{−μ} V` with `V ≡ divTrunc Wₖ U prec`. -/
theorem phi_repr (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (a : F) (N : ℕ) (hN : 0 < N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0)
    (yt : CPoly F) (prec : ℕ)
    (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (z : C⟮S.x⟯⟮S.y⟯) (W : BPoly F) (Q : CPoly F)
    (hz : (z : L) * aeval S.x ((toPoly Q).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀)))
    (hμ : ordC (compC Q (shiftC a N)) < (compC Q (shiftC a N)).length) :
    ∃ V : PowerSeries K,
      S.embG (branchSub N (algebraMap C K (ψ₀ a))) (branchSub_injective N hN _)
          (HahnSeries.ofPowerSeries ℤ K Y) hY z =
        HahnSeries.single (-(ordC (compC Q (shiftC a N)) : ℤ)) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K V ∧
      (PowerSeries.X : PowerSeries K) ^ prec ∣ V - thetaT ((algebraMap C K).comp ψ₀)
        (toPoly (divTrunc (bivEval W (shiftC a N) yt)
          ((compC Q (shiftC a N)).drop (ordC (compC Q (shiftC a N)))) prec)) := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set Qa := compC Q (shiftC a N) with hQa
  set μ := ordC Qa with hμdef
  set U := Qa.drop μ with hU
  set Wk := bivEval W (shiftC a N) yt with hWk
  set G := (toB W).map (thetaN ψ a N) with hG
  set φ := S.embG (branchSub N (algebraMap C K (ψ₀ a))) (branchSub_injective N hN _)
    (HahnSeries.ofPowerSeries ℤ K Y) hY with hφ
  obtain ⟨hθQ, hUc⟩ := thetaT_ordC ψ Qa hμ
  -- the numerator along the branch
  have hWbr := S.eval_W_branch (branchSub N (algebraMap C K (ψ₀ a))) (branchSub_injective N hN _)
    (HahnSeries.ofPowerSeries ℤ K Y) hY z ((toB W).map (mapRingHom ψ₀)) ((toPoly Q).map ψ₀) hz
  have hGmap : ((toB W).map (mapRingHom ψ₀)).map (branchSub N (algebraMap C K (ψ₀ a))) =
      G.map (HahnSeries.ofPowerSeries ℤ K) := by
    rw [hG, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun P ↦ (ofPS_thetaN ψ₀ a N P).symm
  have hQmap : branchSub N (algebraMap C K (ψ₀ a)) ((toPoly Q).map ψ₀) =
      HahnSeries.ofPowerSeries ℤ K (thetaT ψ (toPoly Qa)) := by
    rw [← ofPS_thetaN, hQa, toPoly_compC, toPoly_shiftC]
    rfl
  rw [hGmap, eval_map, eval₂_at_apply, hQmap, hθQ] at hWbr
  set U' := thetaT ψ (toPoly U) with hU'
  have hU'inv : HahnSeries.ofPowerSeries ℤ K U' * HahnSeries.ofPowerSeries ℤ K U'⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel U' hUc, map_one]
  refine ⟨G.eval Y * U'⁻¹, ?_, ?_⟩
  · have hs : HahnSeries.single (-(μ : ℤ)) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.X ^ μ) = 1 := by
      rw [HahnSeries.ofPowerSeries_X_pow, HahnSeries.single_mul_single, neg_add_cancel, one_mul]
      rfl
    calc φ z = φ z * (HahnSeries.single (-(μ : ℤ)) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.X ^ μ)) *
          (HahnSeries.ofPowerSeries ℤ K U' * HahnSeries.ofPowerSeries ℤ K U'⁻¹) := by
          rw [hs, hU'inv, mul_one, mul_one]
      _ = HahnSeries.single (-(μ : ℤ)) (1 : K) *
          (φ z * HahnSeries.ofPowerSeries ℤ K (PowerSeries.X ^ μ * U')) *
          HahnSeries.ofPowerSeries ℤ K U'⁻¹ := by rw [map_mul]; ring
      _ = _ := by rw [← hWbr, map_mul]; ring
  · refine X_pow_dvd_of_mul_unit hUc ?_
    have h1 : G.eval Y * U'⁻¹ * U' = G.eval Y := by
      rw [mul_assoc, PowerSeries.inv_mul_cancel U' hUc, mul_one]
    have h2 : (PowerSeries.X : PowerSeries K) ^ prec ∣ G.eval Y - thetaT ψ (toPoly Wk) := by
      rw [hWk, thetaT_bivEval, ← hG]
      exact hy.trans (sub_dvd_eval_sub _ _ _)
    have h3 : (PowerSeries.X : PowerSeries K) ^ prec ∣ thetaT ψ (toPoly Wk) -
        thetaT ψ (toPoly (divTrunc Wk U prec)) * U' := by
      rw [hU', ← map_mul]
      have hU0 : U.getD 0 0 ≠ 0 := by
        rw [hU, List.getD_eq_getElem?_getD, List.getElem?_drop, add_zero,
          ← List.getD_eq_getElem?_getD]
        exact getD_ordC Qa hμ
      rw [PowerSeries.X_pow_dvd_iff]
      intro j hj
      rw [map_sub, coeff_thetaT, thetaT_apply, Polynomial.coeff_coe, coeff_map,
        mul_comm (toPoly (divTrunc Wk U prec)), coeff_mul_divTrunc Wk U hU0 prec j hj, sub_self]
    have := dvd_add h2 h3
    rw [sub_mul, h1]
    convert this using 1
    ring

end CurveData

end Repr

end Curves
