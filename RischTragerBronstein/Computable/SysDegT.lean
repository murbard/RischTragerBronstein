import RischTragerBronstein.Computable.SysDegE

/-!
# Coupled Risch systems: exponential levels with a triangular limit at infinity

At an exponential level (`t′ = b t`, no nonzero solution of `z′ + j b z = 0` for an integer
`j ≠ 0`), also `z′ + r b z = 0` has no nonzero solution for a rational `r ≠ 0` (`hom_rat`: `zᵈ`
solves the equation with the integer `r d`). For `A Y′ + B Y = G` with `A_δ = I` and
`B_δ = b (Λ − d I)`, `Λ` rational upper triangular, the top coefficient `w` of a solution of degree
`D` beyond the right-hand side satisfies `w′ + b ((D − d) I + Λ) w = 0`, hence `w = 0` unless
`D − d + Λᵢᵢ = 0` for some `i` (`sys_deg_tri`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] (b : K)

/-- **Rational exponents**: `z′ + r b z = 0`, `r ∈ ℚ ∖ {0}` forces `z = 0`. -/
lemma hom_rat (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0) (r : ℚ) (hr : r ≠ 0)
    (z : K) (hz : z′ + (r : K) * b * z = 0) : z = 0 := by
  by_contra hz0
  have hd : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  apply hom (z ^ r.den) (pow_ne_zero _ hz0) r.num hnum
  have hz' : z′ = -((r : K) * b * z) := by linear_combination hz
  have hrd : ((r.num : ℤ) : K) = (r : K) * (r.den : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_mul]
    congr 1
    exact_mod_cast (Rat.mul_den_eq_num r).symm
  rw [Derivation.leibniz_pow, hz', hrd]
  obtain ⟨k, hk⟩ : ∃ k, r.den = k + 1 := ⟨r.den - 1, by have := r.den_pos; omega⟩
  rw [hk]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel, pow_succ]
  push_cast
  ring

variable {n : ℕ} (A B : Fin n → Fin n → K[X])

/-- **The degree bound with a triangular limit at infinity.** -/
theorem sys_deg_tri (δ : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (hAδ : ∀ i j, (A i j).coeff δ = if i = j then 1 else 0) (dD : ℕ) (Λ : Fin n → Fin n → ℚ)
    (htri : ∀ i j, j < i → Λ i j = 0)
    (hBδ : ∀ i j, (B i j).coeff δ = b * ((Λ i j : K) - if i = j then (dD : K) else 0))
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0) (N : ℕ)
    (Y G : Fin n → K[X]) (hG : ∀ i d, N ≤ d → (G i).coeff d = 0) (hY : LopV 0 b A B Y = G)
    (Bd : ℕ) (hBd : ∀ (i : Fin n) (D : ℕ), (D : ℚ) - dD + Λ i i = 0 → D ≤ Bd)
    (j : Fin n) : (Y j).natDegree ≤ max Bd (N - δ) := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Nonempty (Fin n) := ⟨j⟩
  set D := Finset.univ.sup fun j ↦ (Y j).natDegree with hD
  have hjD : (Y j).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (Y j).natDegree) (Finset.mem_univ j)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j ↦ (Y j).natDegree)
  have hYD : ∀ j, (Y j).natDegree ≤ D := fun j ↦
    Finset.le_sup (f := fun j ↦ (Y j).natDegree) (Finset.mem_univ j)
  set w : Fin n → K := fun i ↦ (Y i).coeff D with hw
  have htop : ∀ i, (w i)′ + (((D : ℚ) - dD + Λ i i : ℚ) : K) * b * w i +
      b * ∑ k, (if i < k then (Λ i k : K) else 0) * w k = 0 := by
    intro i
    have h := congrArg (fun P : K[X] ↦ P.coeff (D + δ)) (congrFun hY i)
    rw [coeff_LopV_top 0 b A B δ hA hB Y D hYD i, hG i _ (by omega)] at h
    simp only [hAδ, hBδ, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h
    have e : ∑ x, b * ((Λ i x : K) - if i = x then (dD : K) else 0) * (Y x).coeff D =
        b * ((Λ i i : K) - dD) * w i + b * ∑ k, (if i < k then (Λ i k : K) else 0) * w k := by
      rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [add_comm]
      congr 1
      · simp [hw]
      · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        simp only [lt_irrefl, if_false, zero_mul, mul_zero, add_zero]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        rcases lt_or_gt_of_ne hki with hlt | hgt
        · simp [htri i k hlt, Ne.symm hki, not_lt.mpr hlt.le]
        · simp [Ne.symm hki, hgt]; ring
    rw [e] at h
    push_cast
    linear_combination h
  -- all top coefficients vanish, from the last one up
  have hall : ∀ s : ℕ, ∀ i : Fin n, n - 1 - (i : ℕ) = s → w i = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro i hi
      have hr : ((D : ℚ) - dD + Λ i i) ≠ 0 := fun h0 ↦ by
        have := hBd i D h0; omega
      have hsum : ∑ k, (if i < k then (Λ i k : K) else 0) * w k = 0 :=
        Finset.sum_eq_zero fun k _ ↦ by
          split_ifs with hik
          · rw [ih (n - 1 - k) (by omega) k rfl, mul_zero]
          · rw [zero_mul]
      have := htop i
      rw [hsum, mul_zero, add_zero] at this
      exact hom_rat b hom _ hr _ this
  have hwj0 : w j0 ≠ 0 := by
    have hne : Y j0 ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hj0; omega
    simp only [hw]
    rw [hD, hj0]
    exact mt leadingCoeff_eq_zero.mp hne
  exact hwj0 (hall _ j0 rfl)

end Tower.Sys
