import RischTragerBronstein.Computable.SysDegT

/-!
# Exponential levels with a triangular limit with logarithmic-derivative diagonal

At an exponential level (`t′ = b t`, no nonzero solution of `z′ + j b z = 0`, `j ∈ ℤ ∖ {0}`), also
`z′ + (r b + q c′/c) z = 0` has no nonzero solution for `r ∈ ℚ ∖ {0}`, `q ∈ ℚ` (`hom_ratlog`:
`zᴺ c^{qN}` solves the integer equation). For `A Y′ + B Y = G` with `A_δ = I` and
`B_δ = Λ − d b I`, `Λ` upper triangular with `Λᵢᵢ = pᵢ b + qᵢ cᵢ′/cᵢ`, a solution has degree at
most `max Bd (N − δ)` whenever `Bd` bounds the integers `D` with `D − d + pᵢ = 0`
(`sys_deg_triV`) — the limit of the derivation matrix of a non-constant curve over an exponential.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] (b : K)

/-- **Rational exponents with a logarithmic term**: `z′ + (r b + q c′/c) z = 0`, `r ≠ 0`, forces
`z = 0`. -/
lemma hom_ratlog (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0) (r q : ℚ)
    (hr : r ≠ 0) (c : K) (z : K) (hz : z′ + ((r : K) * b + (q : K) * (c′ / c)) * z = 0) :
    z = 0 := by
  by_cases hc : c = 0
  · rw [hc, div_zero, mul_zero, add_zero] at hz
    exact hom_rat b hom r hr z hz
  by_contra hz0
  set N : ℕ := r.den * q.den with hN
  have hN0 : (N : K) ≠ 0 := by
    rw [hN]; push_cast; exact mul_ne_zero (by exact_mod_cast r.den_nz) (by exact_mod_cast q.den_nz)
  -- integer exponents
  set k : ℤ := q.num * r.den with hk
  set j : ℤ := r.num * q.den with hj
  have hkq : (k : K) = (q : K) * N := by
    rw [hk, hN]; push_cast
    have : (q.num : K) = (q : K) * q.den := by exact_mod_cast (Rat.mul_den_eq_num q).symm
    rw [this]; ring
  have hjr : (j : K) = (r : K) * N := by
    rw [hj, hN]; push_cast
    have : (r.num : K) = (r : K) * r.den := by exact_mod_cast (Rat.mul_den_eq_num r).symm
    rw [this]; ring
  have hj0 : j ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hr) (by exact_mod_cast q.den_nz)
  set Z : K := z ^ N * c ^ k with hZ
  have hZ0 : Z ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) (zpow_ne_zero _ hc)
  apply hom Z hZ0 j hj0
  have hz' : z′ = -(((r : K) * b + (q : K) * (c′ / c)) * z) := by linear_combination hz
  rw [hZ, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_zpow, hz']
  simp only [smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul]
  rw [hjr, hkq]
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by
    have : 0 < N := Nat.pos_of_ne_zero (fun h ↦ hN0 (by rw [h]; simp)); omega⟩
  rw [hM, Nat.add_sub_cancel]
  have hczp : c ^ (k - 1) = c ^ k / c := by rw [zpow_sub_one₀ hc, div_eq_mul_inv]
  rw [hczp]
  push_cast
  field_simp
  ring

variable {n : ℕ} (A B : Fin n → Fin n → K[X])

/-- **The degree bound with a triangular limit whose diagonal is `p b + q c′/c`.** -/
theorem sys_deg_triV (δ : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (hAδ : ∀ i j, (A i j).coeff δ = if i = j then 1 else 0) (dD : ℕ) (Λ : Fin n → Fin n → K)
    (p q : Fin n → ℚ) (c : Fin n → K)
    (htri : ∀ i j, j < i → Λ i j = 0)
    (hdiag : ∀ i, Λ i i = (p i : K) * b + (q i : K) * ((c i)′ / c i))
    (hBδ : ∀ i j, (B i j).coeff δ = Λ i j - if i = j then (dD : K) * b else 0)
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0) (N : ℕ)
    (Y G : Fin n → K[X]) (hG : ∀ i d, N ≤ d → (G i).coeff d = 0) (hY : LopV 0 b A B Y = G)
    (Bd : ℕ) (hBd : ∀ (i : Fin n) (D : ℕ), (D : ℚ) - dD + p i = 0 → D ≤ Bd)
    (j : Fin n) : (Y j).natDegree ≤ max Bd (N - δ) := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Nonempty (Fin n) := ⟨j⟩
  set D := Finset.univ.sup fun j ↦ (Y j).natDegree with hD
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j ↦ (Y j).natDegree)
  have hjD : (Y j).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (Y j).natDegree) (Finset.mem_univ j)
  have hYD : ∀ j, (Y j).natDegree ≤ D := fun j ↦
    Finset.le_sup (f := fun j ↦ (Y j).natDegree) (Finset.mem_univ j)
  set w : Fin n → K := fun i ↦ (Y i).coeff D with hw
  have htop : ∀ i, (w i)′ + ((((D : ℚ) - dD + p i : ℚ) : K) * b + (q i : K) * ((c i)′ / c i)) * w i +
      ∑ k, (if i < k then Λ i k else 0) * w k = 0 := by
    intro i
    have h := congrArg (fun P : K[X] ↦ P.coeff (D + δ)) (congrFun hY i)
    rw [coeff_LopV_top 0 b A B δ hA hB Y D hYD i, hG i _ (by omega)] at h
    simp only [hAδ, hBδ, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h
    have e : ∑ x, (Λ i x - if i = x then (dD : K) * b else 0) * (Y x).coeff D =
        (Λ i i - dD * b) * w i + ∑ k, (if i < k then Λ i k else 0) * w k := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [add_comm]
      congr 1
      · simp [hw]
      · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        simp only [lt_irrefl, if_false, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        rcases lt_or_gt_of_ne hki with hlt | hgt
        · simp [htri i k hlt, Ne.symm hki, not_lt.mpr hlt.le]
        · simp [Ne.symm hki, hgt, hw]
    rw [e, hdiag] at h
    push_cast
    linear_combination h
  have hall : ∀ s : ℕ, ∀ i : Fin n, n - 1 - (i : ℕ) = s → w i = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro i hi
      have hr : ((D : ℚ) - dD + p i) ≠ 0 := fun h0 ↦ by
        have := hBd i D h0; omega
      have hsum : ∑ k, (if i < k then Λ i k else 0) * w k = 0 :=
        Finset.sum_eq_zero fun k _ ↦ by
          split_ifs with hik
          · rw [ih (n - 1 - k) (by omega) k rfl, mul_zero]
          · rw [zero_mul]
      have := htop i
      rw [hsum, add_zero] at this
      exact hom_ratlog b hom _ (q i) hr (c i) _ this
  have hwj0 : w j0 ≠ 0 := by
    have hne : Y j0 ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hj0; omega
    simp only [hw]
    rw [hD, hj0]
    exact mt leadingCoeff_eq_zero.mp hne
  exact hwj0 (hall _ j0 rfl)

end Tower.Sys
