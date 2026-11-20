import RischTragerBronstein.Algebraic.EllExist
import RischTragerBronstein.Elliptic.NLFuel

/-!
# Completeness of `ellDecide`

`ellDecide_ne_none`: on valid input (squarefree cubic, points on the curve with `β ≠ 0` and
distinct `α`, `D ≠ 0`) with at least `EllNL.fuelBound a b c` fuel, `ellDecide` always answers.
Together with `ellDecide_spec` this makes it a **decision procedure**.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace EllAlgo


/-- A squarefree cubic has non-zero discriminant. -/
lemma disc_ne_zero_of_squarefree (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    EllNL.disc a b c ≠ 0 := by
  intro hd
  set A : ℚ := (a : ℚ) with hA
  set B : ℚ := (b : ℚ) with hB
  set Cc : ℚ := (c : ℚ) with hC
  have hdQ : A ^ 2 * B ^ 2 - 4 * B ^ 3 - 4 * A ^ 3 * Cc - 27 * Cc ^ 2 + 18 * A * B * Cc = 0 := by
    have := congrArg (fun t : ℤ ↦ (t : ℚ)) hd
    simp only [EllNL.disc] at this
    push_cast at this
    exact this
  set f : ℚ[X] := X ^ 3 + C A * X ^ 2 + C B * X + C Cc with hf
  set r : ℚ[X] := C (-6 * A ^ 2 + 18 * B) * X + C (-4 * A ^ 3 + 15 * A * B - 27 * Cc)
  set s : ℚ[X] := C (2 * A ^ 2 - 6 * B) * X ^ 2 + C (2 * A ^ 3 - 7 * A * B + 9 * Cc) * X +
    C (A ^ 2 * B + 3 * A * Cc - 4 * B ^ 2)
  have hbez : C (A ^ 2 * B ^ 2 - 4 * B ^ 3 - 4 * A ^ 3 * Cc - 27 * Cc ^ 2 + 18 * A * B * Cc) =
      r * f + s * derivative f := by
    simp only [r, s, f, derivative_add, derivative_X_pow, derivative_mul, derivative_C,
      derivative_X, zero_mul, zero_add, mul_one, map_add, map_sub, map_mul, map_pow, map_neg,
      map_ofNat, map_natCast]
    push_cast
    ring
  rw [hdQ, map_zero] at hbez
  have hsep : f.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
  have hf3 : f.natDegree = 3 := by rw [hf]; compute_degree!
  -- `f ∣ s`, hence `s = 0` by degree
  have hfs : f ∣ s * derivative f := ⟨-r, by linear_combination -hbez⟩
  have hcop : IsCoprime f (derivative f) := hsep
  have hfs' : f ∣ s := hcop.dvd_of_dvd_mul_right hfs
  have hsdeg : s.natDegree ≤ 2 := natDegree_quadratic_le
  have hs0 : s = 0 := by
    by_contra h0
    have := natDegree_le_of_dvd hfs' h0
    omega
  have hr0 : r = 0 := by
    have hf0 : f ≠ 0 := by intro h; rw [h] at hf3; simp at hf3
    have : r * f = 0 := by rw [hs0, zero_mul, add_zero] at hbez; exact hbez.symm
    exact (mul_eq_zero.mp this).resolve_right hf0
  -- then `f = (X + a/3)³`
  have h1 : -6 * A ^ 2 + 18 * B = 0 := by
    have := congrArg (fun q ↦ q.coeff 1) hr0
    simp only [r, coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at this
    simpa using this
  have h2 : -4 * A ^ 3 + 15 * A * B - 27 * Cc = 0 := by
    have := congrArg (fun q ↦ q.coeff 0) hr0
    simp only [r, coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at this
    simpa using this
  have hcube : f = (X + C (A / 3)) ^ 3 := by
    have hb : B = 3 * (A / 3) ^ 2 := by linear_combination h1 / 18
    have hc : Cc = (A / 3) ^ 3 := by linear_combination -h2 / 27 + (5 * A / 162) * h1
    have ha : A = 3 * (A / 3) := by ring
    rw [hf, hb, hc]
    conv_lhs => rw [ha]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [hcube] at hsq
  have := hsq (X + C (A / 3)) ⟨X + C (A / 3), by ring⟩
  exact not_isUnit_X_add_C _ this

/-- `some true` from the torsion test gives a torsion multiple within the fuel. -/
lemma torsionTest_true (a b c : ℤ) {P : (EllNL.W a b c).toAffine.Point} :
    ∀ {F : ℕ}, EllNL.torsionTest a b c P F = some true → ∃ k < F, (k + 1) • P = 0
  | 0, h => by simp [EllNL.torsionTest] at h
  | F + 1, h => by
    unfold EllNL.torsionTest at h
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨k, hk, hk'⟩ := torsionTest_true a b c hr
      exact ⟨k, by omega, hk'⟩
    · split_ifs at h with h1 h2
      · exact ⟨F, by omega, h1⟩
      · simp at h

lemma ordOf_spec {a b c : ℤ} (S : (EllNL.W a b c).toAffine.Point) (fuel : ℕ)
    (h : ∃ k < fuel, (k + 1) • S = 0) : 1 ≤ ordOf S fuel ∧ ordOf S fuel • S = 0 := by
  obtain ⟨k, hk, hk'⟩ := h
  have hsome : ((List.range fuel).find? fun k ↦ decide ((k + 1) • S = 0)).isSome := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_range.mpr hk, by simpa using hk'⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
  have hj' := List.find?_some hj
  simp only [decide_eq_true_eq] at hj'
  simp only [ordOf, hj, Option.map_some, Option.getD_some]
  exact ⟨by omega, hj'⟩

section LinAlg

variable {K : Type*} [Field K] [DecidableEq K]

/-! ### The linear algebra -/

lemma coeff_toPoly_take (w : List K) (L j : ℕ) (hj : j < L) :
    (CPoly.toPoly (w.take L)).coeff j = (CPoly.toPoly w).coeff j := by
  rw [CPoly.coeff_toPoly, CPoly.coeff_toPoly, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

lemma coeff_lcomb_eq_zero (j : ℕ) : ∀ (β : List K) (ws : List (CPoly K)),
    (∀ w ∈ ws, (CPoly.toPoly w).coeff j = 0) → (CPoly.lcomb β ws).coeff j = 0
  | [], ws, _ => by simp [CPoly.lcomb]
  | x :: β, [], _ => by simp [CPoly.lcomb]
  | x :: β, w :: ws, h => by
    rw [lcomb_cons_cons, coeff_add, coeff_C_mul, h w (List.mem_cons_self), mul_zero, zero_add]
    exact coeff_lcomb_eq_zero j β ws fun w' hw' ↦ h w' (List.mem_cons_of_mem _ hw')

lemma lcomb_units (cs : List K) :
    CPoly.lcomb cs ((List.range cs.length).map CPoly.unitL) = CPoly.toPoly cs := by
  rw [lcomb_range_comp X 1 CPoly.unitL (fun j ↦ by
    rw [CPoly.unitL, show (List.replicate j (0 : K) ++ [1]) = CPoly.monomial j 1 from rfl,
      CPoly.toPoly_monomial]; simp) cs.length cs]
  simp

/-- **A non-zero relation forces a basis vector with non-zero head.** -/
lemma exists_good_basis (vs : List (CPoly K)) (cs : List K) (hl : cs.length = vs.length)
    (hrel : CPoly.lcomb cs vs = 0) (hne : CPoly.toPoly cs ≠ 0) :
    ∃ w ∈ CPoly.nullBasis vs, CPoly.toPoly (w.take vs.length) ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h0 : CPoly.lcombS (RingHom.id K) cs vs = 0 := by
    have := CPoly.lcombS_map_ns (RingHom.id K) cs vs
    rw [RingHom.coe_id, List.map_id, Polynomial.map_id] at this
    rw [this, hrel]
  obtain ⟨β, -, hβ⟩ := CPoly.nullBasis_complete (RingHom.id K) vs cs hl h0
  have e1 := CPoly.lcombS_map_ns (RingHom.id K) cs ((CPoly.nsItems vs).map Prod.snd)
  have e2 := CPoly.lcombS_map_ns (RingHom.id K) β (CPoly.nullBasis vs)
  rw [RingHom.coe_id, List.map_id, Polynomial.map_id] at e1 e2
  rw [e1, e2] at hβ
  have hns : (CPoly.nsItems vs).map Prod.snd = (List.range cs.length).map CPoly.unitL := by
    simp [CPoly.nsItems, hl]
  rw [hns, lcomb_units] at hβ
  apply hne
  ext j
  rw [coeff_zero]
  rcases Nat.lt_or_ge j vs.length with hj | hj
  · rw [hβ]
    refine coeff_lcomb_eq_zero j β _ fun w hw ↦ ?_
    rw [← coeff_toPoly_take w vs.length j hj, hall w hw, coeff_zero]
  · rw [CPoly.coeff_toPoly, List.getD_eq_default _ _ (by omega)]

lemma toPoly_range_coeff (f : K[X]) (n : ℕ) (h : f = 0 ∨ f.natDegree < n) :
    CPoly.toPoly ((List.range n).map f.coeff) = f := by
  ext k
  rw [CPoly.coeff_toPoly]
  rcases Nat.lt_or_ge k n with hk | hk
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    rcases h with rfl | h
    · simp
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm



lemma length_ellCols (p : CPoly K) (pts : List (K × K × ℕ)) (na nb : ℕ) :
    (ellCols p pts na nb).length = na + nb := by
  simp [ellCols, ellIdx]

end LinAlg

/-! ### Completeness -/

lemma sign_sq_eq_one {z : ℤ} (hz : z ≠ 0) : ((z.sign : ℤ) : ℚ) ^ 2 = 1 := by
  rcases lt_trichotomy z 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
  · exact absurd h hz
  · rw [Int.sign_eq_one_of_pos h]; norm_num

/-- **A relation exists** when `n S = 0`. -/
lemma exists_relation (a b c : ℤ) (hsq : Squarefree (CPoly.toPoly (pOf a b c)))
    (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (hnS : n • (pts.map fun q ↦ q.2.2 • ptOf a b c q).sum = 0) :
    ∃ cs : List ℚ, cs.length = (ellCols (pOf a b c) (ptsQ pts n) (ellNa (ptsQ pts n))
      (ellNb (ptsQ pts n))).length ∧
      CPoly.lcomb cs (ellCols (pOf a b c) (ptsQ pts n) (ellNa (ptsQ pts n)) (ellNb (ptsQ pts n))) = 0 ∧
      CPoly.toPoly cs ≠ 0 := by
  classical
  set L := pts.length
  let α : Fin L → ℚ := fun i ↦ pts[i].1
  let β : Fin L → ℚ := fun i ↦ pts[i].2.1
  let z : Fin L → ℤ := fun i ↦ pts[i].2.2
  let y' : Fin L → ℚ := fun i ↦ if z i = 0 then β i else ((z i).sign : ℚ) * β i
  have honi : ∀ i : Fin L, β i ^ 2 = α i ^ 3 + a * α i ^ 2 + b * α i + c ∧ β i ≠ 0 :=
    fun i ↦ hon _ (List.getElem_mem i.2)
  have hy'sq : ∀ i, y' i ^ 2 = β i ^ 2 := by
    intro i; simp only [y']; split_ifs with h
    · rfl
    · rw [mul_pow, sign_sq_eq_one h, one_mul]
  have hy'0 : ∀ i, y' i ≠ 0 := by
    intro i h0
    have := hy'sq i
    rw [h0] at this
    exact (honi i).2 (pow_eq_zero_iff two_ne_zero |>.mp this.symm)
  have hns : ∀ i, (WQ a b c).Nonsingular (α i) (y' i) := fun i ↦
    nonsingular_of a b c ⟨by rw [hy'sq]; exact (honi i).1, hy'0 i⟩
  have hP : ∀ i, (WQ a b c).Nonsingular (α i) (β i) := fun i ↦ nonsingular_of a b c (honi i)
  let m : Fin L → ℕ := fun i ↦ n * (z i).natAbs
  let s := (Finset.univ : Finset (Fin L)).filter fun i ↦ z i ≠ 0
  -- the relation `∑ mᵢ Qᵢ = 0`
  have hterm : ∀ i, (m i • (Point.some _ _ (hns i) : (WQ a b c).Point)) =
      (n : ℤ) • (z i • (Point.some _ _ (hP i) : (WQ a b c).Point)) := by
    intro i
    rw [smul_smul, ← natCast_zsmul]
    by_cases h0 : z i = 0
    · simp [m, h0]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hQ : (Point.some _ _ (hns i) : (WQ a b c).Point) = -Point.some _ _ (hP i) := by
        rw [Point.neg_some]
        simp only [Point.some.injEq, true_and, y', if_neg h0, Int.sign_eq_neg_one_of_neg hneg]
        simp [negY, WQ, EllNL.W]
      rw [hQ, zsmul_neg, ← neg_zsmul]
      congr 1
      simp only [m]
      push_cast
      rw [abs_of_neg hneg]; ring
    · have hQ : (Point.some _ _ (hns i) : (WQ a b c).Point) = Point.some _ _ (hP i) := by
        simp only [Point.some.injEq, true_and, y', if_neg h0, Int.sign_eq_one_of_pos hpos]
        simp
      rw [hQ]
      congr 1
      simp only [m]
      push_cast
      rw [abs_of_pos hpos]
  have hS : (pts.map fun q ↦ q.2.2 • ptOf a b c q).sum =
      ∑ i : Fin L, z i • (Point.some _ _ (hP i) : (WQ a b c).Point) := by
    rw [sum_map_eq_fin]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [ptOf]
    rw [dif_pos (honi i)]
  have hsum : ∑ i ∈ s, m i • (Point.some _ _ (hns i) : (WQ a b c).Point) = 0 := by
    rw [Finset.sum_filter]
    have : ∀ i, (if z i ≠ 0 then m i • (Point.some _ _ (hns i) : (WQ a b c).Point) else 0) =
        (n : ℤ) • (z i • (Point.some _ _ (hP i) : (WQ a b c).Point)) := by
      intro i
      split_ifs with h
      · exact hterm i
      · push_neg at h; simp only [h, zero_zsmul, smul_zero]
    rw [Finset.sum_congr rfl fun i _ ↦ this i, ← Finset.smul_sum, ← hS, natCast_zsmul, hnS]
  obtain ⟨A, B, hAB, hA, hB, hloc⟩ := exists_local a b c hsq s α y' hns
    (fun i _ ↦ hy'0 i) m hsum
  -- the sizes
  set na := ellNa (ptsQ pts n)
  set nb := ellNb (ptsQ pts n)
  have hM : ((ptsQ pts n).map fun q ↦ q.2.2).sum = ∑ i ∈ s, m i := by
    rw [ptsQ, List.map_map, sum_map_eq_fin, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with h
    · rfl
    · push_neg at h; simp [m, z]; exact Or.inr h
  have hna : na = (∑ i ∈ s, m i) / 2 + 1 := by
    show ellNa (ptsQ pts n) = _; unfold ellNa; rw [hM]
  have hnb : nb = ((∑ i ∈ s, m i) - 1) / 2 := by
    show ellNb (ptsQ pts n) = _; unfold ellNb; rw [hM]
  have hAd : A = 0 ∨ A.natDegree < na := Or.inr (by omega)
  have hBd : B = 0 ∨ B.natDegree < nb := hB.imp_right (by omega)
  refine ⟨(List.range na).map A.coeff ++ (List.range nb).map B.coeff, ?_, ?_, ?_⟩
  · rw [length_ellCols]; simp
  · have h1 : ((List.range na).map A.coeff ++ (List.range nb).map B.coeff).take na =
        (List.range na).map A.coeff := by
      rw [List.take_left' (by simp)]
    have h2 : (((List.range na).map A.coeff ++ (List.range nb).map B.coeff).drop na).take nb =
        (List.range nb).map B.coeff := by
      rw [List.drop_left' (by simp), List.take_of_length_le (by simp)]
    rw [lcomb_ellCols, h1, h2, toPoly_range_coeff A na hAd, toPoly_range_coeff B nb hBd]
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq0
    set i : Fin L := ⟨j, hj⟩
    by_cases h0 : z i = 0
    · have : n * (pts[j].2.2).natAbs = 0 := by
        simp only [z, i] at h0; simp; exact Or.inr h0
      simp only [this, pow_zero, one_dvd]
    · have his : i ∈ s := by simp [s, h0]
      have hm : 1 ≤ m i := by
        simp only [m]
        exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (Int.natAbs_ne_zero.mpr h0))
      have := hloc i his hm
      simp only [y', if_neg h0] at this
      exact this
  · rw [CPoly.toPoly_append, toPoly_range_coeff A na hAd, toPoly_range_coeff B nb hBd]
    simp only [List.length_map, List.length_range]
    intro h0
    have hBz : B = 0 := by
      by_contra hB0
      have e : A = -(X ^ na * B) := by linear_combination h0
      have hdeg := congrArg natDegree e
      rw [natDegree_neg, natDegree_mul (pow_ne_zero _ X_ne_zero) hB0, natDegree_X_pow] at hdeg
      rcases hAd with hA0 | hAd
      · rw [hA0] at e
        have : X ^ na * B = 0 := by linear_combination e
        exact hB0 ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ X_ne_zero))
      · omega
    rw [hBz, mul_zero, add_zero] at h0
    exact hAB.elim (fun h ↦ h h0) (fun h ↦ h hBz)

/-- **With a torsion relation, the certificate step answers.** -/
theorem ellCert_ne_none (a b c : ℤ) (hsq : Squarefree (CPoly.toPoly (pOf a b c)))
    (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (hnS : n • (pts.map fun q ↦ q.2.2 • ptOf a b c q).sum = 0) :
    ellCert a b c B pts D n ≠ none := by
  obtain ⟨cs, hl, hrel, hne⟩ := exists_relation a b c hsq pts hon n hn hnS
  obtain ⟨w, hw, hwne⟩ := exists_good_basis _ cs hl hrel hne
  rw [length_ellCols] at hwne
  have hsome : ((CPoly.nullBasis (ellCols (pOf a b c) (ptsQ pts n) (ellNa (ptsQ pts n))
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
  have hcheck := certCheck_ok a b c hsq pts hon hnd D hD n hn w'
    (CPoly.nullBasis_sound _ w' hw'mem) hw'ne B
  unfold ellCert ellSolve
  rw [hw']
  simp only
  rw [if_pos hcheck]
  simp

/-- **Completeness of `ellDecide`**: with at least `fuelBound` fuel it always answers on valid
input. -/
theorem ellDecide_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) (fuel : ℕ)
    (hfuel : EllNL.fuelBound a b c ≤ fuel) :
    ellDecide a b c B pts D fuel ≠ none := by
  have hdisc := disc_ne_zero_of_squarefree a b c hsq
  have hsqP : Squarefree (CPoly.toPoly (pOf a b c)) := by rw [toPoly_pOf]; exact hsq
  have hval : (pts.all (fun q ↦ decide (q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧
      q.2.1 ≠ 0)) && decide (pts.map Prod.fst).Nodup && decide (D ≠ 0)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨hon, hnd⟩, hD⟩
  unfold ellDecide
  rw [if_pos hval]
  dsimp only
  have hT := EllNL.torsionTest_isSome' a b c hdisc
    ((pts.map fun q ↦ q.2.2 • ptOf a b c q).sum) fuel hfuel
  split
  · simp
  · rename_i hT'
    obtain ⟨hn, hnS⟩ := ordOf_spec _ fuel (torsionTest_true a b c hT')
    exact ellCert_ne_none a b c hsqP B pts hon hnd D hD _ hn hnS
  · rename_i hT'
    exact absurd hT' hT

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for elliptic integrals with rational logarithmic part.** For
`y² = x³ + ax² + bx + c` (squarefree, `a, b, c ∈ ℤ`), `B ∈ ℚ[x]`, rational points
`(αᵢ, βᵢ)` (`βᵢ ≠ 0`, distinct `αᵢ`), `zᵢ ∈ ℤ`, `D ≥ 1`: `ellDecide` with `fuelBound` fuel returns
`some b`, and `b = true` iff `∫ (B(x) + ∑ (zᵢ/D) βᵢ/(x − αᵢ)) dx / y` is elementary. -/
theorem ellDecide_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) :
    ∃ ans : Bool, ellDecide a b c B pts D (EllNL.fuelBound a b c) = some ans ∧
      (ans = true ↔ HasElementaryIntegral ((aeval x (CPoly.toPoly B) + (pts.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y)) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecide_ne_none a b c hsq B pts hon hnd D hD _ le_rfl)
  exact ⟨ans, hans, ellDecide_spec hC hCall x y hx a b c hsq hy hgen B pts D _ ans hans⟩

end Decision

end EllAlgo
