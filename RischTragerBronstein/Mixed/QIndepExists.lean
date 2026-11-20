import RischTragerBronstein.Mixed.QHeightExists
import RischTragerBronstein.Mixed.QPar
import RischTragerBronstein.Mixed.MWPairPos

/-!
# Two-point height certificates over `ℚ` exist for independent points

On `y² = x³ + ax + b` over `ℚ`: the canonical height is `≥ 0` (`canonQ_nonneg`), vanishes only on
torsion (`torsion_of_canonQ_zero`, Northcott for points `finite_hP_le`), and its pairing has
positive Gram determinant on independent points (`gramQ_pos`, via `MWPair.gram_pos_of_finite`).
The approximations of `certG` converge, so **`certG_exists`**: independent points always pass the
two-point certificate at some level.
-/

open FFHeight WeierstrassCurve WeierstrassCurve.Affine Real

namespace QHeight

variable (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)

/-- The canonical height over `ℚ`. -/
noncomputable abbrev canonQ : (qW a b).toAffine.Point → ℝ := MWTate.canon MWPair.dbl (hP a b)

lemma hP_nonneg (R : (qW a b).toAffine.Point) : 0 ≤ hP a b R := by
  cases R with
  | zero => simp [hP]
  | some x y h => exact Real.log_nonneg (by exact_mod_cast one_le_Hq x)

include hΔ

lemma canonQ_par (P Q : (qW a b).toAffine.Point) :
    canonQ a b (P + Q) + canonQ a b (P - Q) = 2 * canonQ a b P + 2 * canonQ a b Q :=
  MWPair.canon_parallelogram (hP_double a b hΔ) (hP_par a b hΔ) P Q

lemma canonQ_approx0 (R : (qW a b).toAffine.Point) :
    |canonQ a b R - hP a b R| ≤ Real.log (Cq a b) / 3 := by
  have := MWPair.canon_approx (h := hP a b) (hP_double a b hΔ) 0 R
  simpa using this

lemma canonQ_nonneg (R : (qW a b).toAffine.Point) : 0 ≤ canonQ a b R := by
  by_contra hneg
  push_neg at hneg
  set C := Real.log (Cq a b)
  obtain ⟨k, hk⟩ := exists_nat_gt (C / 3 / (-canonQ a b R))
  have happ := MWPair.canon_approx (h := hP a b) (hP_double a b hΔ) k R
  have h0 := hP_nonneg a b (MWPair.dbl^[k] R)
  have h4 : (k : ℝ) < 4 ^ k := by
    have := Nat.lt_pow_self (n := k) (by norm_num : 1 < 4); exact_mod_cast this
  have hpos : 0 < -canonQ a b R := by linarith
  rw [div_lt_iff₀ hpos] at hk
  rw [abs_le] at happ
  have h4' : (0 : ℝ) < 4 ^ k := by positivity
  have e1 : hP a b (MWPair.dbl^[k] R) / 4 ^ k ≥ 0 := div_nonneg h0 h4'.le
  have e2 : C / 3 / 4 ^ k < -canonQ a b R := by
    rw [div_lt_iff₀ h4']; nlinarith
  linarith [happ.1]

/-- **Northcott for points over `ℚ`.** -/
lemma finite_hP_le (M : ℝ) : {R : (qW a b).toAffine.Point | hP a b R ≤ M}.Finite := by
  set B0 : ℕ := ⌈Real.exp M⌉₊
  let φ : (qW a b).toAffine.Point → Option (ℚ × ℚ) := fun R ↦ match R with
    | .zero => none
    | .some x y _ => some (x, y)
  have hφ : Function.Injective φ := by
    intro R S h
    cases R <;> cases S <;> simp_all [φ]
  have hX := finite_Hq_le B0
  set T : Set (ℚ × ℚ) := ⋃ x ∈ {q : ℚ | Hq q ≤ B0},
    ({x} : Set ℚ) ×ˢ ({Rat.sqrt (x ^ 3 + a * x + b), -Rat.sqrt (x ^ 3 + a * x + b)} : Set ℚ)
  have hT : T.Finite := hX.biUnion fun x _ ↦ (Set.finite_singleton x).prod (by simp)
  refine Set.Finite.of_finite_image ?_ hφ.injOn
  refine ((Set.finite_singleton none).union (hT.image some)).subset ?_
  rintro _ ⟨R, hR, rfl⟩
  cases R with
  | zero => left; rfl
  | some x y h =>
    right
    refine ⟨(x, y), ?_, rfl⟩
    simp only [Set.mem_setOf_eq, hP] at hR
    have hH : Hq x ≤ B0 := by
      have h1 : (Hq x : ℝ) ≤ Real.exp M := by
        have hpos : (0 : ℝ) < Hq x := by exact_mod_cast one_le_Hq x
        rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hR
      exact_mod_cast h1.trans (Nat.le_ceil _)
    have heq := h.1
    rw [equation_iff] at heq
    simp only [qW] at heq
    have hy : y * y = x ^ 3 + a * x + b := by linear_combination heq
    have hs := Rat.sqrt_eq y
    rw [hy] at hs
    simp only [T, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_insert_iff]
    refine ⟨x, hH, rfl, ?_⟩
    rw [hs]
    rcases abs_choice y with h' | h'
    · left; exact h'.symm
    · right; rw [h']; ring

/-- `ĥ(jR) = j² ĥ(R)`. -/
lemma canonQ_zsmul (R : (qW a b).toAffine.Point) (j : ℤ) :
    canonQ a b (j • R) = (j : ℝ) ^ 2 * canonQ a b R := by
  have par := canonQ_par a b hΔ
  rw [← MWPair.pairing_self _ par, ← MWPair.pairing_self _ par, MWPair.quad_smul]

/-- **Canonical height zero ⇒ torsion.** -/
lemma torsion_of_canonQ_zero (R : (qW a b).toAffine.Point) (h0 : canonQ a b R = 0) :
    ∃ n : ℕ, 0 < n ∧ n • R = 0 := by
  have hbd : ∀ j : ℕ, j • R ∈ {S : (qW a b).toAffine.Point |
      hP a b S ≤ Real.log (Cq a b) / 3} := fun j ↦ by
    have h1 := canonQ_approx0 a b hΔ (j • R)
    have h2 : canonQ a b (j • R) = 0 := by
      rw [← natCast_zsmul, canonQ_zsmul a b hΔ, h0, mul_zero]
    rw [h2, zero_sub, abs_neg] at h1
    exact (le_abs_self _).trans h1
  obtain ⟨i, -, j, -, hij, e⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo
    (fun j _ ↦ hbd j) (finite_hP_le a b hΔ _)
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨j - i, by omega, ?_⟩
    have : (j - i) • R + i • R = j • R := by rw [← add_nsmul, Nat.sub_add_cancel h.le]
    rw [← e] at this
    exact add_eq_right.mp this
  · refine ⟨i - j, by omega, ?_⟩
    have : (i - j) • R + j • R = i • R := by rw [← add_nsmul, Nat.sub_add_cancel h.le]
    rw [e] at this
    exact add_eq_right.mp this

/-- **The Gram determinant of independent points is positive.** -/
lemma gramQ_pos (P Q : (qW a b).toAffine.Point)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    0 < canonQ a b P * canonQ a b Q -
      ((canonQ a b (P + Q) - canonQ a b P - canonQ a b Q) / 2) ^ 2 := by
  have par := canonQ_par a b hΔ
  set Bp := MWPair.pairing (canonQ a b) par
  have hsym : ∀ P Q, Bp P Q = Bp Q P := fun P Q ↦ by
    simp only [Bp, MWPair.pairing_apply]; exact MWPair.polar_comm _ P Q
  have hself : ∀ R, Bp R R = canonQ a b R := fun R ↦ MWPair.pairing_self _ par R
  rw [← MWPair.gram_pairing _ par]
  refine MWPair.gram_pos_of_finite Bp hsym P Q (fun m n hmn ↦ ?_) (fun c ↦ ?_)
  · rw [hself]
    rcases (canonQ_nonneg a b hΔ (m • P + n • Q)).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨N, hN, hN0⟩ := torsion_of_canonQ_zero a b hΔ _ h.symm
      have e0 : ((N : ℤ) * m) • P + ((N : ℤ) * n) • Q = 0 := by
        rw [mul_zsmul, mul_zsmul, ← zsmul_add, natCast_zsmul]; exact hN0
      have e : ((N : ℤ) * m) • P = (-((N : ℤ) * n)) • Q := by
        rw [neg_zsmul]
        exact eq_neg_of_add_eq_zero_left e0
      obtain ⟨h1, h2⟩ := hind _ _ e
      have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
      have hm : m = 0 := (mul_eq_zero.mp h1).resolve_left hN'
      have hn : n = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h2)).resolve_left hN'
      exact hmn (by rw [hm, hn])
  · set f : ℤ × ℤ → (qW a b).toAffine.Point := fun v ↦ v.1 • P + v.2 • Q
    have hf : Function.Injective f := by
      intro v w hvw
      have e : (v.1 - w.1) • P = (w.2 - v.2) • Q := by
        have hvw' : v.1 • P + v.2 • Q = w.1 • P + w.2 • Q := hvw
        rw [sub_zsmul, sub_zsmul, ← sub_eq_add_neg, ← sub_eq_add_neg, sub_eq_sub_iff_add_eq_add,
          add_comm (w.2 • Q)]
        exact hvw'
      obtain ⟨h1, h2⟩ := hind _ _ e
      exact Prod.ext (by omega) (by omega)
    refine ((finite_hP_le a b hΔ (c + Real.log (Cq a b) / 3)).preimage hf.injOn).subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq, hself] at hv
    show hP a b (f v) ≤ c + Real.log (Cq a b) / 3
    have := canonQ_approx0 a b hΔ (f v)
    rw [abs_le] at this
    simp only [f] at this ⊢
    linarith [this.1]

/-- **Two-point certificates exist for independent points.** -/
theorem certG_exists (x1 y1 x2 y2 : ℚ) (h1 : (qW a b).toAffine.Nonsingular x1 y1)
    (h2 : (qW a b).toAffine.Nonsingular x2 y2)
    (hind : ∀ m n : ℤ, m • Point.some x1 y1 h1 = n • Point.some x2 y2 h2 → m = 0 ∧ n = 0) :
    ∃ k, certG a b k x1 y1 x2 y2 = true := by
  set P := Point.some x1 y1 h1
  set Q := Point.some x2 y2 h2
  have hx : x1 ≠ x2 := by
    intro hx
    rcases Y_eq_of_X_eq h1.1 h2.1 hx with hy | hy
    · have := hind 1 1 (by simp only [one_smul, P, Q]; congr 1 <;> simp [hx, hy])
      exact one_ne_zero this.1
    · have hs : P + Q = 0 := Point.add_of_Y_eq hx hy
      have := hind 1 (-1) (by rw [one_smul, neg_one_smul]; exact eq_neg_of_add_eq_zero_left hs)
      exact one_ne_zero this.1
  have hx3e : (qW a b).toAffine.addX x1 x2 ((qW a b).toAffine.slope x1 x2 y1 y2) =
      ((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2 := by rw [addX_qW, slope_of_X_ne hx]
  have h3 : (qW a b).toAffine.Nonsingular (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2)
      ((qW a b).toAffine.addY x1 x2 y1 ((qW a b).toAffine.slope x1 x2 y1 y2)) := by
    rw [← hx3e]; exact nonsingular_add h1 h2 (fun hxy ↦ hx hxy.1)
  have hsum : P + Q = Point.some (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) _ h3 := by
    simp only [P, Q]
    rw [Point.add_of_X_ne hx]
    simp only [Point.some.injEq, hx3e, and_self]
  -- infinite order
  have hntP : ∀ n : ℕ, 0 < n → n • P ≠ 0 := fun n hn h0 ↦ by
    have := hind n 0 (by rw [natCast_zsmul, h0, zero_zsmul]); omega
  have hntQ : ∀ n : ℕ, 0 < n → n • Q ≠ 0 := fun n hn h0 ↦ by
    have := hind 0 (-(n : ℤ)) (by rw [zero_zsmul, neg_zsmul, natCast_zsmul, h0, neg_zero]); omega
  have hntR : ∀ n : ℕ, 0 < n → n • Point.some (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2) _ h3 ≠ 0 :=
    fun n hn h0 ↦ by
      rw [← hsum, nsmul_add] at h0
      have := hind n (-(n : ℤ)) (by
        rw [neg_zsmul, natCast_zsmul, natCast_zsmul]; exact eq_neg_of_add_eq_zero_left h0)
      omega
  choose ps yp hp hps hpp using fun k ↦ xIter_total a b k x1 y1 h1 hntP
  choose qs yq hq hqs hqp using fun k ↦ xIter_total a b k x2 y2 h2 hntQ
  choose rs yr hr hrs hrp using fun k ↦ xIter_total a b k _ _ h3 hntR
  -- the canonical values, scaled by `log 2`
  set ℓ := Real.log 2
  have hℓ : 0 < ℓ := Real.log_pos (by norm_num)
  set A := canonQ a b P / ℓ
  set Bq := canonQ a b Q / ℓ
  set Cr := canonQ a b (P + Q) / ℓ
  set Dg := A * Bq - ((Cr - A - Bq) / 2) ^ 2
  have hDg : 0 < Dg := by
    have hg := gramQ_pos a b hΔ P Q hind
    have e : Dg = (canonQ a b P * canonQ a b Q -
        ((canonQ a b (P + Q) - canonQ a b P - canonQ a b Q) / 2) ^ 2) / (ℓ * ℓ) := by
      simp only [Dg, A, Bq, Cr]; field_simp
    rw [e]; exact div_pos hg (mul_pos hℓ hℓ)
  set L0 : ℝ := (bitLen (Cq a b).toNat : ℝ) / 3 + 1 / 2
  have hL0 : 0 ≤ L0 := by positivity
  set K : ℝ := (|A| + |Bq| + 3 * L0) + 3 / 2 * (|Cr| + |A| + |Bq| + 3 * L0 + 3 * L0 / 2) + 1
  have hK : 0 < K := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * (L0 / 4 ^ k) * K < Dg := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * L0 * K / Dg)
    refine ⟨k, ?_⟩
    have h4 : (k : ℝ) < 4 ^ k := by
      have := Nat.lt_pow_self (n := k) (by norm_num : 1 < 4); exact_mod_cast this
    rw [div_lt_iff₀ hDg] at hk
    rw [show 2 * (L0 / 4 ^ k) * K = 2 * L0 * K / 4 ^ k by ring, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨k, ?_⟩
  simp only [certG, Bool.and_eq_true, bne_iff_ne, ne_eq, hx, not_false_eq_true, true_and, hps k,
    hqs k, hrs k, gapQ, decide_eq_true_eq]
  -- the approximations
  set ε : ℝ := L0 / 4 ^ k
  have hε0 : 0 ≤ ε := by positivity
  have hεL : ε ≤ L0 := div_le_self hL0 (one_le_pow₀ (by norm_num))
  have aP := canon_approx_bits a b hΔ k x1 y1 h1 (ps k) (hps k)
  have aQ := canon_approx_bits a b hΔ k x2 y2 h2 (qs k) (hqs k)
  have aR := canon_approx_bits a b hΔ k _ _ h3 (rs k) (hrs k)
  rw [← hsum] at aR
  set α : ℝ := ((bitLen (Hq (ps k)) : ℝ) - 1 / 2) / 4 ^ k
  set β : ℝ := ((bitLen (Hq (qs k)) : ℝ) - 1 / 2) / 4 ^ k
  set γ : ℝ := ((bitLen (Hq (rs k)) : ℝ) - 1 / 2) / 4 ^ k
  have scale : ∀ u v : ℝ, |u - v * ℓ| ≤ ε * ℓ → |u / ℓ - v| ≤ ε := fun u v huv ↦ by
    rw [show u / ℓ - v = (u - v * ℓ) / ℓ by field_simp, abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]
    exact huv
  have hA := scale _ _ (by simpa [ε, L0] using aP)
  have hB := scale _ _ (by simpa [ε, L0] using aQ)
  have hC := scale _ _ (by simpa [ε, L0] using aR)
  have hA' : |α - A| ≤ ε := by rw [abs_sub_comm]; exact hA
  have hB' : |β - Bq| ≤ ε := by rw [abs_sub_comm]; exact hB
  have hC' : |γ - Cr| ≤ ε := by rw [abs_sub_comm]; exact hC
  have hpert := MWPair.gram_perturb α β γ A Bq Cr ε hA' hB' hC'
  -- both error terms are `≤ ε K`
  have bα : |α| ≤ |A| + ε := by
    have := abs_sub_abs_le_abs_sub α A; linarith
  have bβ : |β| ≤ |Bq| + ε := by
    have := abs_sub_abs_le_abs_sub β Bq; linarith
  have bγ : |γ - α - β| ≤ |Cr| + |A| + |Bq| + 3 * ε := by
    have := abs_sub_abs_le_abs_sub γ Cr
    have := abs_sub (γ - α) β; have := abs_sub γ α; linarith
  have E1 : ε * (|α| + |β| + ε) + 3 * ε / 2 * (|γ - α - β| + 3 * ε / 2) ≤ ε * K := by
    have : |α| + |β| + ε ≤ |A| + |Bq| + 3 * L0 := by linarith
    have h2 : |γ - α - β| + 3 * ε / 2 ≤ |Cr| + |A| + |Bq| + 3 * L0 + 3 * L0 / 2 := by linarith
    have := mul_le_mul_of_nonneg_left this hε0
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 3 * ε / 2)
    simp only [K]; nlinarith
  have E2 : ε * (|A| + |Bq| + ε) + 3 * ε / 2 * (|Cr - A - Bq| + 3 * ε / 2) ≤ ε * K := by
    have : |A| + |Bq| + ε ≤ |A| + |Bq| + 3 * L0 := by linarith
    have hcab : |Cr - A - Bq| ≤ |Cr| + |A| + |Bq| := by
      have := abs_sub (Cr - A) Bq; have := abs_sub Cr A; linarith
    have h2 : |Cr - A - Bq| + 3 * ε / 2 ≤ |Cr| + |A| + |Bq| + 3 * L0 + 3 * L0 / 2 := by linarith
    have := mul_le_mul_of_nonneg_left this hε0
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 3 * ε / 2)
    simp only [K]; nlinarith
  have hfin : ε * (|α| + |β| + ε) + 3 * ε / 2 * (|γ - α - β| + 3 * ε / 2) <
      |α * β - ((γ - α - β) / 2) ^ 2| := by
    have h1 : Dg - ε * K ≤ |α * β - ((γ - α - β) / 2) ^ 2| := by
      have := abs_sub_abs_le_abs_sub Dg (α * β - ((γ - α - β) / 2) ^ 2)
      rw [abs_sub_comm] at hpert
      have := abs_of_pos hDg
      linarith
    have : 2 * ε * K < Dg := by simpa [ε, mul_assoc] using hk
    linarith
  refine (Rat.cast_lt (K := ℝ)).mp ?_
  push_cast [Rat.cast_abs]
  exact hfin

end QHeight
