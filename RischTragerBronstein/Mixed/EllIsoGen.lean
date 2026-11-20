import RischTragerBronstein.Mixed.EllIsoGram

/-!
# Completeness of height certificates from integral, positive canonical heights

Abstract form of `EllIsoGram`: on `y² = x³ + A x + B` over `K(X)`, if `k · canonH` takes natural
values (`hint`, some `k ≥ 1`) and `canonH` vanishes only on torsion (`htor`), then for independent
`P, Q` the discriminant of the height form is positive (`disc_pos_gen`) and the level-`k'`
certificate of `ell_indep` holds for some `k'` (`hgap_exists_gen`). Instances: quadratic twists
(`k = 1`, `EllIso`), `j = 0` twists (`k = 3`, `EllIso0`), `j = 1728` twists (`k = 2`, `EllIso1728`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine Filter Topology

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

variable {A B : K[X]}

theorem canonH_ge_gen (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (k : ℕ) (hk : 0 < k)
    (hint : ∀ X : (shortW A B).toAffine.Point, ∃ z : ℕ, (k : ℝ) * canonH A B X = z)
    (htor : ∀ X : (shortW A B).toAffine.Point, canonH A B X = 0 → ∃ n : ℕ, 0 < n ∧ n • X = 0)
    (P Q : (shortW A B).toAffine.Point)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) (m n : ℤ) (hmn : ¬ (m = 0 ∧ n = 0)) :
    1 ≤ (k : ℝ) * canonH A B (m • P + n • Q) := by
  obtain ⟨z, hz⟩ := hint (m • P + n • Q)
  rw [hz]
  by_contra hlt
  have hz0 : z = 0 := by
    have : (z : ℝ) < 1 := not_le.mp hlt
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
  have h0 : canonH A B (m • P + n • Q) = 0 := by
    rw [hz0, Nat.cast_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hk.ne')
  obtain ⟨N, hN, hNX⟩ := htor _ h0
  have : ((N : ℤ) * m) • P = (-((N : ℤ) * n)) • Q := by
    rw [← sub_eq_zero, neg_smul, sub_neg_eq_add, mul_smul, mul_smul, ← zsmul_add, natCast_zsmul]
    exact hNX
  obtain ⟨h1, h2⟩ := hind _ _ this
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (by exact_mod_cast h : N = 0) hN.ne'
  rcases mul_eq_zero.mp (neg_eq_zero.mp h2) with h' | h'
  · exact absurd (by exact_mod_cast h' : N = 0) hN.ne'
  exact hmn ⟨h, h'⟩

theorem disc_pos_gen (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (k : ℕ) (hk : 0 < k)
    (hint : ∀ X : (shortW A B).toAffine.Point, ∃ z : ℕ, (k : ℝ) * canonH A B X = z)
    (htor : ∀ X : (shortW A B).toAffine.Point, canonH A B X = 0 → ∃ n : ℕ, 0 < n ∧ n • X = 0)
    (P Q : (shortW A B).toAffine.Point)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    0 < 4 * canonH A B P * canonH A B Q -
      (canonH A B (P + Q) - canonH A B P - canonH A B Q) ^ 2 := by
  obtain ⟨za, hza⟩ := hint P
  obtain ⟨zc, hzc⟩ := hint Q
  obtain ⟨zs, hzs⟩ := hint (P + Q)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set bb : ℤ := (zs : ℤ) - za - zc
  have hb : (k : ℝ) * (canonH A B (P + Q) - canonH A B P - canonH A B Q) = bb := by
    rw [mul_sub, mul_sub, hza, hzc, hzs]; push_cast [bb]; ring
  have ha := canonH_ge_gen hΔ' k hk hint htor P Q hind 1 0 (by simp)
  simp only [one_zsmul, zero_zsmul, add_zero] at ha
  have hza1 : (1 : ℝ) ≤ za := by rw [← hza]; exact ha
  have key := canonH_ge_gen hΔ' k hk hint htor P Q hind bb (-(2 * za)) (by
    rintro ⟨-, h⟩; have : (za : ℤ) = 0 := by omega
    have : (za : ℝ) = 0 := by exact_mod_cast this
    linarith)
  rw [canonH_quad hΔ'] at key
  have e : (k : ℝ) * ((bb : ℤ) ^ 2 * canonH A B P + (bb : ℤ) * (-(2 * (za : ℤ)) : ℤ) *
      (canonH A B (P + Q) - canonH A B P - canonH A B Q) + ((-(2 * (za : ℤ)) : ℤ) : ℝ) ^ 2 *
        canonH A B Q) = za * (4 * za * zc - bb ^ 2) := by
    have hP : canonH A B P = za / k := by rw [← hza]; field_simp
    have hQ : canonH A B Q = zc / k := by rw [← hzc]; field_simp
    have hS : canonH A B (P + Q) - canonH A B P - canonH A B Q = bb / k := by rw [← hb]; field_simp
    rw [hS, hP, hQ]; push_cast; field_simp; ring
  rw [e] at key
  have h1 : (1 : ℝ) ≤ za * (4 * za * zc - bb ^ 2) := key
  have h2 : (1 : ℝ) ≤ 4 * za * zc - bb ^ 2 := by
    have hint2 : ∃ t : ℤ, (4 * za * zc - bb ^ 2 : ℝ) = t := ⟨4 * za * zc - bb ^ 2, by push_cast; ring⟩
    obtain ⟨t, ht⟩ := hint2
    rw [ht] at h1 ⊢
    have : (0 : ℝ) < t := by
      by_contra hneg; push_neg at hneg
      have : (za : ℝ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
      linarith
    have : (1 : ℤ) ≤ t := by exact_mod_cast this
    exact_mod_cast this
  have hP : canonH A B P = za / k := by rw [← hza]; field_simp
  have hQ : canonH A B Q = zc / k := by rw [← hzc]; field_simp
  have hS : canonH A B (P + Q) - canonH A B P - canonH A B Q = bb / k := by rw [← hb]; field_simp
  rw [hS, hP, hQ]
  have : 4 * ((za : ℝ) / k) * (zc / k) - (bb / k) ^ 2 = (4 * za * zc - bb ^ 2) / k ^ 2 := by
    field_simp
  rw [this]
  positivity

theorem hgap_exists_gen (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (k : ℕ) (hk : 0 < k)
    (hint : ∀ X : (shortW A B).toAffine.Point, ∃ z : ℕ, (k : ℝ) * canonH A B X = z)
    (htor : ∀ X : (shortW A B).toAffine.Point, canonH A B X = 0 → ∃ n : ℕ, 0 < n ∧ n • X = 0)
    (P Q : (shortW A B).toAffine.Point)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k : ℕ, let C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
      let h := hR A B
      let d := MWPair.dbl (G := (shortW A B).toAffine.Point)
      C / 3 / 4 ^ k * (|h (d^[k] P) / 4 ^ k| + |h (d^[k] Q) / 4 ^ k| + C / 3 / 4 ^ k) +
        3 * (C / 3 / 4 ^ k) / 2 * (|h (d^[k] (P + Q)) / 4 ^ k - h (d^[k] P) / 4 ^ k -
          h (d^[k] Q) / 4 ^ k| + 3 * (C / 3 / 4 ^ k) / 2) <
      |h (d^[k] P) / 4 ^ k * (h (d^[k] Q) / 4 ^ k) - ((h (d^[k] (P + Q)) / 4 ^ k -
          h (d^[k] P) / 4 ^ k - h (d^[k] Q) / 4 ^ k) / 2) ^ 2| := by
  set C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
  have hC := hR_double A B hΔ'
  have tP := MWTate.tendsto_canon hC P
  have tQ := MWTate.tendsto_canon hC Q
  have tS := MWTate.tendsto_canon hC (P + Q)
  have te : Tendsto (fun k : ℕ ↦ C / 3 / 4 ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  set f := canonH A B
  have hlim1 := (te.mul ((tP.abs.add tQ.abs).add te)).add
    (((te.const_mul 3).div_const 2).mul (((tS.sub tP).sub tQ).abs.add ((te.const_mul 3).div_const 2)))
  have hlim2 := ((tP.mul tQ).sub ((((tS.sub tP).sub tQ).div_const 2).pow 2)).abs
  have hpos : (0 : ℝ) * (|f P| + |f Q| + 0) + 3 * 0 / 2 * (|f (P + Q) - f P - f Q| + 3 * 0 / 2) <
      |f P * f Q - ((f (P + Q) - f P - f Q) / 2) ^ 2| := by
    have := disc_pos_gen hΔ' k hk hint htor P Q hind
    have hk : 0 < f P * f Q - ((f (P + Q) - f P - f Q) / 2) ^ 2 := by nlinarith
    rw [abs_of_pos hk]
    linarith
  obtain ⟨k, hk⟩ := (hlim1.eventually_lt hlim2 hpos).exists
  exact ⟨k, hk⟩

end FFHeight
