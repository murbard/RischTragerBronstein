import RischTragerBronstein.Computable.SysNorm

/-!
# A computable bound on the rational roots of a rational polynomial

`rootBound P = 1 + (∑_{i < d} |aᵢ|) / |a_d|`: every rational root `x` of `P ≠ 0` satisfies
`|x| ≤ rootBound P` (`abs_le_rootBound`).
-/

open Polynomial Finset

namespace Tower.Sys

/-- The bound `1 + ∑_{i < d} |aᵢ| / |a_d|`. -/
noncomputable def rootBound (P : ℚ[X]) : ℚ :=
  1 + (∑ i ∈ range P.natDegree, |P.coeff i|) / |P.leadingCoeff|

theorem abs_le_rootBound (P : ℚ[X]) (hP : P ≠ 0) (x : ℚ) (hx : P.IsRoot x) :
    |x| ≤ rootBound P := by
  set d := P.natDegree with hd
  set S := ∑ i ∈ range d, |P.coeff i| with hS
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hlc' : 0 < |P.leadingCoeff| := abs_pos.mpr hlc
  have hS0 : 0 ≤ S := sum_nonneg fun i _ ↦ abs_nonneg _
  rw [rootBound]
  rcases le_or_gt |x| 1 with h1 | h1
  · have : 0 ≤ S / |P.leadingCoeff| := div_nonneg hS0 hlc'.le
    linarith
  -- `|x| > 1`
  have hev : P.leadingCoeff * x ^ d = -∑ i ∈ range d, P.coeff i * x ^ i := by
    have h := hx
    rw [IsRoot.def, eval_eq_sum_range, sum_range_succ] at h
    rw [leadingCoeff]
    linarith
  have hd0 : 0 < d := by
    by_contra h0
    have hd0 : d = 0 := by omega
    rw [hd0, pow_zero, mul_one, range_zero, sum_empty, neg_zero] at hev
    exact hlc hev
  have hbound : |P.leadingCoeff| * |x| ^ d ≤ S * |x| ^ (d - 1) := by
    calc |P.leadingCoeff| * |x| ^ d = |∑ i ∈ range d, P.coeff i * x ^ i| := by
          rw [← abs_pow, ← abs_mul, hev, abs_neg]
      _ ≤ ∑ i ∈ range d, |P.coeff i * x ^ i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range d, |P.coeff i| * |x| ^ (d - 1) := by
          refine sum_le_sum fun i hi ↦ ?_
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1.le (by
            have := mem_range.mp hi; omega)) (abs_nonneg _)
      _ = S * |x| ^ (d - 1) := by rw [hS, sum_mul]
  have hxpos : 0 < |x| ^ (d - 1) := pow_pos (by linarith) _
  have hsplit : |x| ^ d = |x| * |x| ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hsplit, ← mul_assoc] at hbound
  have h2 : |P.leadingCoeff| * |x| ≤ S := le_of_mul_le_mul_right hbound hxpos
  have h3 : |x| ≤ S / |P.leadingCoeff| := by
    rw [le_div_iff₀ hlc']; linarith
  linarith

/-- Evaluation of a rational coefficient list. -/
def evalQ : CPoly ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

lemma evalQ_eq (p : CPoly ℚ) (x : ℚ) : evalQ p x = (CPoly.toPoly p).eval x := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih => simp [evalQ, ih, CPoly.toPoly_cons]

lemma le_foldr_max0 (l : List ℕ) : ∀ a ∈ l, a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · exact (ih a ha).trans (by simp)

/-- The largest natural root `≤ B` (or `0`). -/
def maxRootLE (w : CPoly ℚ) (B : ℕ) : ℕ :=
  (((List.range (B + 1) : List ℕ)).filter fun e : ℕ ↦ evalQ w (e : ℚ) == 0).foldr max 0

lemma le_maxRootLE (w : CPoly ℚ) (B e : ℕ) (he : e ≤ B) (hr : (CPoly.toPoly w).eval (e : ℚ) = 0) :
    e ≤ maxRootLE w B := by
  have hmem : e ∈ ((List.range (B + 1) : List ℕ)).filter fun e : ℕ ↦ evalQ w (e : ℚ) == 0 := by
    rw [List.mem_filter, List.mem_range]
    exact ⟨by omega, by rw [evalQ_eq, hr]; rfl⟩
  exact le_foldr_max0 _ _ hmem

end Tower.Sys
