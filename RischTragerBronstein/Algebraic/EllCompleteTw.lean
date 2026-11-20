import RischTragerBronstein.Algebraic.EllAlgoTw

/-!
# Completeness of `ellDecideTw`

The existence of `u` on the curve `Ỹ² = p/d` comes from the twist `Y² = X³ + adX² + bd²X + cd³`
(`exists_relation`) by the substitution `X = d x`, `Y = d² Ỹ`: local vanishing is preserved
(`locVal_twist`, via uniqueness of Hensel lifts).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace EllAlgo

open CPoly

/-- **Uniqueness of the Hensel lift** mod `Xᵐ`. -/
lemma hensel_unique (P Y₁ Y₂ : ℚ[X]) (m : ℕ) (h1 : X ^ m ∣ P - Y₁ ^ 2) (h2 : X ^ m ∣ P - Y₂ ^ 2)
    (h0 : Y₁.coeff 0 = Y₂.coeff 0) (hne : Y₁.coeff 0 ≠ 0) : X ^ m ∣ Y₁ - Y₂ := by
  have hprod : X ^ m ∣ (Y₁ - Y₂) * (Y₁ + Y₂) := by
    have : (Y₁ - Y₂) * (Y₁ + Y₂) = (P - Y₂ ^ 2) - (P - Y₁ ^ 2) := by ring
    rw [this]; exact dvd_sub h2 h1
  have hcop : IsCoprime (X ^ m) (Y₁ + Y₂) := by
    refine IsCoprime.pow_left ?_
    refine (irreducible_X.coprime_iff_not_dvd).mpr ?_
    rw [X_dvd_iff, coeff_add, ← h0]
    intro h; apply hne; linear_combination h / 2
  exact hcop.dvd_of_dvd_mul_right hprod

lemma dvd_comp_scale (f : ℚ[X]) (d : ℚ) (m : ℕ) (h : X ^ m ∣ f) : X ^ m ∣ f.comp (C d * X) := by
  obtain ⟨g, rfl⟩ := h
  rw [mul_comp, pow_comp, X_comp, mul_pow, ← C_pow, mul_assoc]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

lemma coeff_zero_comp_scale (f : ℚ[X]) (d : ℚ) : (f.comp (C d * X)).coeff 0 = f.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, eval_comp]; simp

/-- **Local vanishing on the twist gives local vanishing on `Ỹ² = p/d`.** -/
lemma locVal_twist (a b c d : ℤ) (hd : d ≠ 0) (α y₀ : ℚ) (m : ℕ) (hm : 1 ≤ m) (hy₀ : y₀ ≠ 0)
    (hcurve : (d : ℚ) * y₀ ^ 2 = α ^ 3 + a * α ^ 2 + b * α + c) (A B : ℚ[X])
    (h : X ^ m ∣ locVal (pOf (a * d) (b * d ^ 2) (c * d ^ 3)) A B (d * α, d ^ 2 * y₀, m)) :
    X ^ m ∣ locVal (smul (1 / (d : ℚ)) (pOf a b c)) (A.comp (C (d : ℚ) * X))
      (C ((d : ℚ) ^ 2) * B.comp (C (d : ℚ) * X)) (α, y₀, m) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  set pW := pOf (a * d) (b * d ^ 2) (c * d ^ 3)
  set pT := smul (1 / (d : ℚ)) (pOf a b c)
  set Yw := toPoly (Yq pW (d * α, d ^ 2 * y₀, m))
  set Yt := toPoly (Yq pT (α, y₀, m))
  -- the two Hensel lifts
  have hpW : toPoly pW = X ^ 3 + C ((a * d : ℤ) : ℚ) * X ^ 2 + C ((b * d ^ 2 : ℤ) : ℚ) * X +
      C ((c * d ^ 3 : ℤ) : ℚ) := toPoly_pOf _ _ _
  have hpT : toPoly pT = C (1 / (d : ℚ)) * (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X +
      C (c : ℚ)) := by rw [toPoly_smul, toPoly_pOf]
  have hW0 : (toPoly (shiftPoly pW (d * α))).coeff 0 = (d ^ 2 * y₀) ^ 2 := by
    rw [toPoly_shiftPoly, coeff_zero_eq_eval_zero, eval_comp, hpW]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, zero_add]
    push_cast
    linear_combination -(d : ℚ) ^ 3 * hcurve
  have hT0 : (toPoly (shiftPoly pT α)).coeff 0 = y₀ ^ 2 := by
    rw [toPoly_shiftPoly, coeff_zero_eq_eval_zero, eval_comp, hpT]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, zero_add]
    field_simp
    linear_combination -hcurve
  have hdW := sqrtSeries_dvd (shiftPoly pW (d * α)) (d ^ 2 * y₀)
    (mul_ne_zero (pow_ne_zero _ hdq) hy₀) hW0 m hm
  have hdT := sqrtSeries_dvd (shiftPoly pT α) y₀ hy₀ hT0 m hm
  rw [toPoly_shiftPoly] at hdW hdT
  -- `Yw(d t) ≡ d² Yt(t)`
  have hcomp : ((toPoly pW).comp (X + C ((d : ℚ) * α))).comp (C (d : ℚ) * X) =
      C ((d : ℚ) ^ 4) * (toPoly pT).comp (X + C α) := by
    apply Polynomial.funext
    intro t
    simp only [eval_comp, eval_mul, eval_add, eval_C, eval_X, eval_pow, hpW, hpT]
    push_cast
    field_simp
  have hZ : X ^ m ∣ Yw.comp (C (d : ℚ) * X) - C ((d : ℚ) ^ 2) * Yt := by
    refine hensel_unique (C ((d : ℚ) ^ 4) * (toPoly pT).comp (X + C α)) _ _ m ?_ ?_ ?_ ?_
    · rw [← hcomp]
      have := dvd_comp_scale _ (d : ℚ) m hdW
      rwa [sub_comp, pow_comp] at this
    · have : C ((d : ℚ) ^ 4) * (toPoly pT).comp (X + C α) - (C ((d : ℚ) ^ 2) * Yt) ^ 2 =
          C ((d : ℚ) ^ 4) * ((toPoly pT).comp (X + C α) - Yt ^ 2) := by
        rw [mul_pow, ← C_pow]; ring
      rw [this]
      exact dvd_mul_of_dvd_right hdT _
    · rw [coeff_zero_comp_scale, coeff_C_mul]
      simp only [Yw, Yt, Yq, coeff_zero_sqrtSeries]
    · rw [coeff_zero_comp_scale]
      simp only [Yw, Yq, coeff_zero_sqrtSeries]
      exact mul_ne_zero (pow_ne_zero _ hdq) hy₀
  -- compare the two local values
  have hL := dvd_comp_scale _ (d : ℚ) m h
  simp only [locVal] at hL ⊢
  have e1 : (A.comp (X + C ((d : ℚ) * α))).comp (C (d : ℚ) * X) =
      (A.comp (C (d : ℚ) * X)).comp (X + C α) := by
    rw [comp_assoc, comp_assoc]; congr 1; simp only [add_comp, mul_comp, X_comp, C_comp]
    rw [C_mul]; ring
  have e2 : (B.comp (X + C ((d : ℚ) * α))).comp (C (d : ℚ) * X) =
      (B.comp (C (d : ℚ) * X)).comp (X + C α) := by
    rw [comp_assoc, comp_assoc]; congr 1; simp only [add_comp, mul_comp, X_comp, C_comp]
    rw [C_mul]; ring
  rw [add_comp, mul_comp, e1, e2] at hL
  have : (A.comp (C (d : ℚ) * X)).comp (X + C α) +
      (C ((d : ℚ) ^ 2) * B.comp (C (d : ℚ) * X)).comp (X + C α) * Yt =
      ((A.comp (C (d : ℚ) * X)).comp (X + C α) + (B.comp (C (d : ℚ) * X)).comp (X + C α) *
        Yw.comp (C (d : ℚ) * X)) -
        (B.comp (C (d : ℚ) * X)).comp (X + C α) * (Yw.comp (C (d : ℚ) * X) - C ((d : ℚ) ^ 2) * Yt) := by
    rw [mul_comp, C_comp]; ring
  rw [this]
  exact dvd_sub hL (dvd_mul_of_dvd_right hZ _)

/-- The twist of a squarefree cubic is squarefree. -/
lemma twist_squarefree (a b c d : ℤ) (hd : d ≠ 0)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    Squarefree (X ^ 3 + C ((a * d : ℤ) : ℚ) * X ^ 2 + C ((b * d ^ 2 : ℤ) : ℚ) * X +
      C ((c * d ^ 3 : ℤ) : ℚ)) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  set f : ℚ[X] := X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)
  have hsep : f.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
  have hcomp : (f.comp (C (1 / (d : ℚ)) * X)).Separable := by
    have hsep' : IsCoprime f (derivative f) := hsep
    have h1 : IsCoprime (f.comp (C (1 / (d : ℚ)) * X)) ((derivative f).comp (C (1 / (d : ℚ)) * X)) :=
      hsep'.map (Polynomial.compRingHom (C (1 / (d : ℚ)) * X))
    have hu : IsUnit (C (1 / (d : ℚ))) := isUnit_C.mpr (Ne.isUnit (one_div_ne_zero hdq))
    show IsCoprime (f.comp (C (1 / (d : ℚ)) * X)) (derivative (f.comp (C (1 / (d : ℚ)) * X)))
    have hL : derivative (C (1 / (d : ℚ)) * X) = C (1 / (d : ℚ)) := by
      rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one]
    rw [derivative_comp, hL]
    exact (isCoprime_mul_unit_left_right hu _ _).mpr h1
  have heq : X ^ 3 + C ((a * d : ℤ) : ℚ) * X ^ 2 + C ((b * d ^ 2 : ℤ) : ℚ) * X +
      C ((c * d ^ 3 : ℤ) : ℚ) = f.comp (C (1 / (d : ℚ)) * X) * C ((d : ℚ) ^ 3) := by
    apply Polynomial.funext
    intro t
    simp only [f, eval_comp, eval_mul, eval_add, eval_C, eval_X, eval_pow]
    push_cast
    field_simp
  rw [heq]
  exact (hcomp.mul_unit (isUnit_C.mpr (Ne.isUnit (pow_ne_zero 3 hdq)))).squarefree

lemma disc_twist (a b c d : ℤ) :
    EllNL.disc (a * d) (b * d ^ 2) (c * d ^ 3) = d ^ 6 * EllNL.disc a b c := by
  unfold EllNL.disc; ring

/-- The twisted points, as rational points of the twist. -/
def ptsTw (d : ℤ) (pts : List (ℚ × ℚ × ℤ)) : List (ℚ × ℚ × ℤ) :=
  pts.map fun q ↦ ((d : ℚ) * q.1, (d : ℚ) ^ 2 * q.2.1, q.2.2)

/-- **A relation exists on `Ỹ² = p/d`** when the twisted divisor is torsion. -/
lemma exists_relation_twist (a b c d : ℤ) (hd : d ≠ 0)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, (d : ℚ) * q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (hnS : n • (pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum = 0) :
    ∃ cs : List ℚ, cs.length = (ellCols (smul (1 / (d : ℚ)) (pOf a b c)) (ptsQ pts n)
      (ellNa (ptsQ pts n)) (ellNb (ptsQ pts n))).length ∧
      CPoly.lcomb cs (ellCols (smul (1 / (d : ℚ)) (pOf a b c)) (ptsQ pts n) (ellNa (ptsQ pts n))
        (ellNb (ptsQ pts n))) = 0 ∧ CPoly.toPoly cs ≠ 0 := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  -- the relation on the twist
  have hsqT : Squarefree (CPoly.toPoly (pOf (a * d) (b * d ^ 2) (c * d ^ 3))) := by
    rw [toPoly_pOf]; exact twist_squarefree a b c d hd hsq
  have honT : ∀ q ∈ ptsTw d pts, q.2.1 ^ 2 = q.1 ^ 3 + ((a * d : ℤ) : ℚ) * q.1 ^ 2 +
      ((b * d ^ 2 : ℤ) : ℚ) * q.1 + ((c * d ^ 3 : ℤ) : ℚ) ∧ q.2.1 ≠ 0 := by
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    have := twist_nonsingular a b c d hd (hon q0 hq0)
    exact ⟨this.2.1, this.2.2⟩
  have hnST : n • ((ptsTw d pts).map fun q ↦ q.2.2 • ptOf (a * d) (b * d ^ 2) (c * d ^ 3) q).sum
      = 0 := by
    rw [ptsTw, List.map_map]; exact hnS
  obtain ⟨csT, hlT, hrelT, hneT⟩ := exists_relation (a * d) (b * d ^ 2) (c * d ^ 3) hsqT
    (ptsTw d pts) honT n hn hnST
  -- sizes agree
  have hQ : (ptsQ (ptsTw d pts) n).map (fun q ↦ q.2.2) = (ptsQ pts n).map (fun q ↦ q.2.2) := by
    simp [ptsQ, ptsTw, List.map_map, Function.comp_def]
  have hna : ellNa (ptsQ (ptsTw d pts) n) = ellNa (ptsQ pts n) := by simp only [ellNa, hQ]
  have hnb : ellNb (ptsQ (ptsTw d pts) n) = ellNb (ptsQ pts n) := by simp only [ellNb, hQ]
  set na := ellNa (ptsQ pts n)
  set nb := ellNb (ptsQ pts n)
  rw [hna, hnb] at hrelT hlT
  rw [length_ellCols] at hlT
  have hlocT := (lcomb_ellCols _ na nb csT _).mp hrelT
  set Ah := CPoly.toPoly (csT.take na)
  set Bh := CPoly.toPoly ((csT.drop na).take nb)
  set A := Ah.comp (C (d : ℚ) * X)
  set Bt := C ((d : ℚ) ^ 2) * Bh.comp (C (d : ℚ) * X)
  -- degrees
  have hdegC : (C (d : ℚ) * X).natDegree = 1 := by
    rw [natDegree_C_mul_X _ hdq]
  have hAd : A = 0 ∨ A.natDegree < na := by
    right
    rw [natDegree_comp, hdegC, mul_one]
    have hA1 : Ah.natDegree ≤ (csT.take na).length - 1 := CPoly.natDegree_toPoly_le_length _
    have hl : (csT.take na).length ≤ na := by simp
    have hna1 : 1 ≤ na := by simp [na, ellNa]
    omega
  have hBd : Bt = 0 ∨ Bt.natDegree < nb := by
    rcases Nat.eq_zero_or_pos nb with h0 | h0
    · left
      simp only [Bt, Bh, h0, List.take_zero, CPoly.toPoly_nil, zero_comp, mul_zero]
    · right
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [natDegree_comp, hdegC, mul_one]
      have hB1 : Bh.natDegree ≤ ((csT.drop na).take nb).length - 1 :=
        CPoly.natDegree_toPoly_le_length _
      have hl : ((csT.drop na).take nb).length ≤ nb := by simp
      omega
  refine ⟨(List.range na).map A.coeff ++ (List.range nb).map Bt.coeff, ?_, ?_, ?_⟩
  · rw [length_ellCols]; simp
  · have h1 : ((List.range na).map A.coeff ++ (List.range nb).map Bt.coeff).take na =
        (List.range na).map A.coeff := by rw [List.take_left' (by simp)]
    have h2 : (((List.range na).map A.coeff ++ (List.range nb).map Bt.coeff).drop na).take nb =
        (List.range nb).map Bt.coeff := by
      rw [List.drop_left' (by simp), List.take_of_length_le (by simp)]
    rw [lcomb_ellCols, h1, h2, toPoly_range_coeff A na hAd, toPoly_range_coeff Bt nb hBd]
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    by_cases hz : q0.2.2 = 0
    · simp [hz]
    have hm : 1 ≤ n * q0.2.2.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (Int.natAbs_ne_zero.mpr hz))
    have hs2 : ((q0.2.2.sign : ℤ) : ℚ) ^ 2 = 1 := sign_sq_eq_one hz
    have hy0 : ((q0.2.2.sign : ℤ) : ℚ) * q0.2.1 ≠ 0 :=
      mul_ne_zero (fun h ↦ by rw [h] at hs2; norm_num at hs2) (hon q0 hq0).2
    have hcurve : (d : ℚ) * (((q0.2.2.sign : ℤ) : ℚ) * q0.2.1) ^ 2 =
        q0.1 ^ 3 + a * q0.1 ^ 2 + b * q0.1 + c := by
      rw [mul_pow, hs2, one_mul]; exact (hon q0 hq0).1
    refine locVal_twist a b c d hd q0.1 _ _ hm hy0 hcurve Ah Bh ?_
    have hqT : ((d : ℚ) * q0.1, ((q0.2.2.sign : ℤ) : ℚ) * ((d : ℚ) ^ 2 * q0.2.1),
        n * q0.2.2.natAbs) ∈ ptsQ (ptsTw d pts) n := by
      simp only [ptsQ, ptsTw, List.map_map, List.mem_map, Function.comp_apply]
      exact ⟨q0, hq0, rfl⟩
    have := hlocT _ hqT
    rwa [show ((q0.2.2.sign : ℤ) : ℚ) * ((d : ℚ) ^ 2 * q0.2.1) =
      (d : ℚ) ^ 2 * (((q0.2.2.sign : ℤ) : ℚ) * q0.2.1) by ring] at this
  · -- non-zero
    have hABh : Ah ≠ 0 ∨ Bh ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hneT
      have hsplit : csT = csT.take na ++ (csT.drop na).take nb := by
        rw [List.take_of_length_le (show (csT.drop na).length ≤ nb by simp; omega),
          List.take_append_drop]
      rw [hsplit, CPoly.toPoly_append]
      change Ah + X ^ _ * Bh = 0
      rw [hc.1, hc.2]; ring
    rw [CPoly.toPoly_append, toPoly_range_coeff A na hAd, toPoly_range_coeff Bt nb hBd]
    simp only [List.length_map, List.length_range]
    intro h0
    have hBz : Bt = 0 := by
      by_contra hB0
      have e : A = -(X ^ na * Bt) := by linear_combination h0
      have hdeg := congrArg natDegree e
      rw [natDegree_neg, natDegree_mul (pow_ne_zero _ X_ne_zero) hB0, natDegree_X_pow] at hdeg
      rcases hAd with hA0 | hAd
      · rw [hA0] at e
        have : X ^ na * Bt = 0 := by linear_combination e
        exact hB0 ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ X_ne_zero))
      · omega
    rw [hBz, mul_zero, add_zero] at h0
    have hcompinj : ∀ F : ℚ[X], F.comp (C (d : ℚ) * X) = 0 → F = 0 := by
      intro F hF
      have := congrArg (fun G ↦ G.comp (C (1 / (d : ℚ)) * X)) hF
      simp only [comp_assoc, mul_comp, C_comp, X_comp, zero_comp] at this
      rwa [← mul_assoc, ← C_mul, mul_one_div_cancel hdq, C_1, one_mul, comp_X] at this
    rcases hABh with h | h
    · exact h (hcompinj _ h0)
    · apply h
      apply hcompinj
      have : C ((d : ℚ) ^ 2) * Bh.comp (C (d : ℚ) * X) = 0 := hBz
      exact (mul_eq_zero.mp this).resolve_left (C_ne_zero.mpr (pow_ne_zero _ hdq))

/-- **With a torsion relation, the twisted certificate step answers.** -/
theorem ellCertTw_ne_none (a b c d : ℤ) (hd : d ≠ 0)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, (d : ℚ) * q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (hnS : n • (pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum = 0) :
    ellCertTw a b c d B pts D n ≠ none := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  obtain ⟨cs, hl, hrel, hne⟩ := exists_relation_twist a b c d hd hsq pts hon n hn hnS
  obtain ⟨w, hw, hwne⟩ := exists_good_basis _ cs hl hrel hne
  rw [length_ellCols] at hwne
  set pT := smul (1 / (d : ℚ)) (pOf a b c)
  have hsome : ((CPoly.nullBasis (ellCols pT (ptsQ pts n) (ellNa (ptsQ pts n))
      (ellNb (ptsQ pts n)))).find? fun w ↦
        !CPoly.isZero (w.take (ellNa (ptsQ pts n) + ellNb (ptsQ pts n)))).isSome := by
    rw [List.find?_isSome]
    refine ⟨w, hw, ?_⟩
    have : CPoly.isZero (w.take (ellNa (ptsQ pts n) + ellNb (ptsQ pts n))) = false := by
      rcases h : CPoly.isZero (w.take (ellNa (ptsQ pts n) + ellNb (ptsQ pts n))) with _ | _
      · rfl
      · exact absurd ((CPoly.isZero_iff _).mp h) hwne
    simp [this]
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp hsome
  have hw'mem := List.mem_of_find?_eq_some hw'
  have hw'p := List.find?_some hw'
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw'p
  have hw'ne : CPoly.toPoly (w'.take (ellNa (ptsQ pts n) + ellNb (ptsQ pts n))) ≠ 0 := by
    intro h0; rw [← CPoly.isZero_iff] at h0; rw [h0] at hw'p; exact Bool.noConfusion hw'p
  have hpT : CPoly.toPoly pT = C (1 / (d : ℚ)) * (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X +
      C (c : ℚ)) := by rw [CPoly.toPoly_smul, toPoly_pOf]
  have hp3 : (CPoly.toPoly pT).natDegree = 3 := by
    rw [hpT, natDegree_C_mul (one_div_ne_zero hdq)]; compute_degree!
  have hcheck := certCheck_ok_gen pT hp3 pts (fun q hq ↦ ⟨by
      rw [hpT]; simp only [eval_mul, eval_C, eval_add, eval_pow, eval_X]
      rw [← (hon q hq).1]; field_simp, (hon q hq).2⟩) hnd D hD n hn w'
    (CPoly.nullBasis_sound _ w' hw'mem) hw'ne (CPoly.smul (1 / (d : ℚ)) B)
  unfold ellCertTw ellSolve
  rw [hw']
  simp only
  rw [if_pos hcheck]
  simp

/-- **Completeness of `ellDecideTw`.** -/
theorem ellDecideTw_ne_none (a b c d : ℤ) (hd : d ≠ 0)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, (d : ℚ) * q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) (fuel : ℕ)
    (hfuel : EllNL.fuelBound (a * d) (b * d ^ 2) (c * d ^ 3) ≤ fuel) :
    ellDecideTw a b c d B pts D fuel ≠ none := by
  have hdisc : EllNL.disc (a * d) (b * d ^ 2) (c * d ^ 3) ≠ 0 := by
    rw [disc_twist]
    exact mul_ne_zero (pow_ne_zero _ hd) (disc_ne_zero_of_squarefree a b c hsq)
  have hval : (decide (d ≠ 0) && pts.all (fun q ↦ decide ((d : ℚ) * q.2.1 ^ 2 =
      q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)) &&
      decide (pts.map Prod.fst).Nodup && decide (D ≠ 0)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hd, hon⟩, hnd⟩, hD⟩
  unfold ellDecideTw
  rw [if_pos hval]
  dsimp only
  have hT := EllNL.torsionTest_isSome' _ _ _ hdisc
    ((pts.map fun q ↦ q.2.2 • ptTw a b c d q).sum) fuel hfuel
  split
  · simp
  · rename_i hT'
    obtain ⟨hn, hnS⟩ := ordOf_spec _ fuel (torsionTest_true _ _ _ hT')
    exact ellCertTw_ne_none a b c d hd hsq B pts hon hnd D hD _ hn hnS
  · rename_i hT'
    exact absurd hT' hT

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for residues at twisted points `(αᵢ, γᵢ√d)`** (any constant field): `ellDecideTw` with `fuelBound` fuel of the twist returns `some b`, and `b = true` iff
`∫ (B(x) + ∑ (zᵢ/D) γᵢ d / (x − αᵢ)) dx / y` is elementary. -/
theorem ellDecideTw_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (d : ℤ) (hd : d ≠ 0) (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, (d : ℚ) * q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) :
    ∃ ans : Bool, ellDecideTw a b c d B pts D (EllNL.fuelBound (a * d) (b * d ^ 2) (c * d ^ 3)) =
      some ans ∧ (ans = true ↔ HasElementaryIntegral ((aeval x (CPoly.toPoly B) + (pts.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 * d : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y)) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideTw_ne_none a b c d hd hsq B pts hon hnd D hD _ le_rfl)
  exact ⟨ans, hans, ellDecideTw_spec hC hCall x y hx a b c hsq hy hgen d B pts D _ ans hans⟩

end Decision

end EllAlgo
