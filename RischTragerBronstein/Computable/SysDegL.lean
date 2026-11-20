import RischTragerBronstein.Computable.SysDeg

/-!
# Coupled Risch systems: the degree bound at a primitive level with a limit matrix

As `SysDeg`, but `B` may reach the top degree: `deg A, deg B ≤ δ + 1`, `PA` a left inverse of the
leading matrix `A_{δ+1}`, `Λ = PA B_{δ+1}` (the limit at infinity). If `deg Y = D ≥ 1` and `G`
has no coefficients from `D + δ` on, the two top coefficients give (`sys_top_primL`)
* `Y_D′ + Λ Y_D = 0` — a nonzero solution `c` of the homogeneous limit system;
* `Y_{D−1}′ + Λ Y_{D−1} = −(D w0 c + β c)`, `β = PA (B_δ − A_δ Λ)`.
So `D` is a *special degree* (`SpecialDegL`), and if every special degree is `≤ Bs` then
`deg Y ≤ max Bs (N − δ)` (`sys_deg_primL`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K]
variable (w0 : K) {n : ℕ} (A B : Fin n → Fin n → K[X])

/-- The limit matrix `Λ = PA B_{δ+1}`. -/
noncomputable def lamML (PA : Fin n → Fin n → K) (δ : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of PA * Matrix.of fun l j ↦ (B l j).coeff (δ + 1)

/-- The matrix `β = PA (B_δ − A_δ Λ)`. -/
noncomputable def betaML (PA : Fin n → Fin n → K) (δ : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of PA * ((Matrix.of fun l j ↦ (B l j).coeff δ) -
    (Matrix.of fun l j ↦ (A l j).coeff δ) * lamML B PA δ)

/-- **A special degree** with a limit matrix `Λ`: a nonzero solution `c` of `c′ + Λ c = 0` with
`−(D w0 + β) c` in the image of `y ↦ y′ + Λ y`. -/
def SpecialDegL (Λ β : Matrix (Fin n) (Fin n) K) (D : ℕ) : Prop :=
  ∃ c : Fin n → K, c ≠ 0 ∧ (∀ i, (c i)′ + (Λ.mulVec c) i = 0) ∧
    ∃ y : Fin n → K, ∀ i, (y i)′ + (Λ.mulVec y) i = -((D : K) * w0 * c i + (β.mulVec c) i)

/-- **The two top coefficients at a primitive level, with a limit matrix.** -/
theorem sys_top_primL (δ k : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ + 1)
    (hB : ∀ i j, (B i j).natDegree ≤ δ + 1) (PA : Fin n → Fin n → K)
    (hPA : ∀ i l, ∑ j, PA i j * (A j l).coeff (δ + 1) = if i = l then 1 else 0)
    (Y : Fin n → K[X]) (hY : ∀ j, (Y j).natDegree ≤ k + 1)
    (h1 : ∀ i, (LopV w0 0 A B Y i).coeff (k + 1 + (δ + 1)) = 0)
    (h2 : ∀ i, (LopV w0 0 A B Y i).coeff (δ + k + 1) = 0) :
    (∀ i, ((Y i).coeff (k + 1))′ + ((lamML B PA δ).mulVec fun j ↦ (Y j).coeff (k + 1)) i = 0) ∧
      ∀ i, ((Y i).coeff k)′ + ((lamML B PA δ).mulVec fun j ↦ (Y j).coeff k) i =
        -((k + 1 : ℕ) * w0 * (Y i).coeff (k + 1) +
          ((betaML A B PA δ).mulVec fun j ↦ (Y j).coeff (k + 1)) i) := by
  -- apply the left inverse to a vector equation `A_top v = u`
  have inv : ∀ v u : Fin n → K, (∀ l, ∑ j, (A l j).coeff (δ + 1) * v j = u l) →
      v = (Matrix.of PA).mulVec u := by
    intro v u hvu
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ← hvu, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ l, PA i l * ((A l j).coeff (δ + 1) * v j) = (if i = j then 1 else 0) * v j :=
      fun j ↦ by rw [← hPA i j, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    simp [this]
  set c : Fin n → K := fun j ↦ (Y j).coeff (k + 1) with hc
  set y : Fin n → K := fun j ↦ (Y j).coeff k with hy
  set Ad : Matrix (Fin n) (Fin n) K := Matrix.of fun l j ↦ (A l j).coeff δ with hAd
  set Bd : Matrix (Fin n) (Fin n) K := Matrix.of fun l j ↦ (B l j).coeff δ with hBd
  set Bt : Matrix (Fin n) (Fin n) K := Matrix.of fun l j ↦ (B l j).coeff (δ + 1) with hBt
  have hmv : ∀ (Mx : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (l : Fin n),
      (Mx.mulVec v) l = ∑ j, Mx l j * v j := fun _ _ _ ↦ rfl
  -- the top equation: `c′ = −Λ c`
  have htop : (fun i ↦ (c i)′) = -(lamML B PA δ).mulVec c := by
    have := inv (fun j ↦ (c j)′) (-(Bt.mulVec c)) (fun l ↦ by
      have h := h1 l
      rw [coeff_LopV_top w0 0 A B (δ + 1) hA hB Y (k + 1) hY l] at h
      rw [Pi.neg_apply, hmv, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hc, hBt, Matrix.of_apply]; push_cast; ring)
    rw [this, lamML, ← Matrix.mulVec_mulVec, Matrix.mulVec_neg]
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · have := congrFun htop i
    simp only [Pi.neg_apply] at this
    change (c i)′ + _ = 0
    rw [this, neg_add_cancel]
  have hsec := inv (fun j ↦ (y j)′ + (k + 1 : ℕ) * w0 * c j)
    (-(Bd.mulVec c + Ad.mulVec (fun j ↦ (c j)′) + Bt.mulVec y)) (fun l ↦ by
      have h := h2 l
      rw [LopV, finsetSum_coeff] at h
      rw [Pi.neg_apply, Pi.add_apply, Pi.add_apply, hmv, hmv, hmv, eq_neg_iff_add_eq_zero,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hBc : (B l j * Y j).coeff (δ + k + 1) =
          (B l j).coeff (δ + 1) * (Y j).coeff k + (B l j).coeff δ * (Y j).coeff (k + 1) :=
        coeff_mul_below _ _ δ k (hB l j) (hY j)
      rw [coeff_add, coeff_mul_below _ _ δ k (hA l j) (natDegree_DzL_le w0 0 _ _ (hY j)), hBc,
        coeff_DzL, coeff_DzL, coeff_eq_zero_of_natDegree_lt (show (Y j).natDegree < k + 1 + 1 by
          linarith [hY j])]
      simp only [hc, hy, hAd, hBd, hBt, Matrix.of_apply]; push_cast; ring)
  rw [htop] at hsec
  have key : (Matrix.of PA).mulVec (-(Bd.mulVec c + Ad.mulVec (-(lamML B PA δ).mulVec c) +
      Bt.mulVec y)) = -((betaML A B PA δ).mulVec c + (lamML B PA δ).mulVec y) := by
    simp only [hBd, hAd, hBt, betaML, lamML, Matrix.mulVec_neg, Matrix.mulVec_add, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.mulVec_sub]
    abel
  rw [key] at hsec
  have := congrFun hsec i
  simp only [Pi.neg_apply, Pi.add_apply] at this
  change (y i)′ + _ = _
  linear_combination this

/-- **The degree bound at a primitive level with a limit matrix.** -/
theorem sys_deg_primL (δ : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ + 1)
    (hB : ∀ i j, (B i j).natDegree ≤ δ + 1) (PA : Fin n → Fin n → K)
    (hPA : ∀ i l, ∑ j, PA i j * (A j l).coeff (δ + 1) = if i = l then 1 else 0) (Bs N : ℕ)
    (hBs : ∀ D, 1 ≤ D → SpecialDegL w0 (lamML B PA δ) (betaML A B PA δ) D → D ≤ Bs)
    (Y G : Fin n → K[X]) (hG : ∀ i d, N ≤ d → (G i).coeff d = 0) (hY : LopV w0 0 A B Y = G)
    (j : Fin n) : (Y j).natDegree ≤ max Bs (N - δ) := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Nonempty (Fin n) := ⟨j⟩
  set D := Finset.univ.sup fun j ↦ (Y j).natDegree with hD
  have hjD : (Y j).natDegree ≤ D := Finset.le_sup (f := fun j ↦ (Y j).natDegree) (Finset.mem_univ j)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j ↦ (Y j).natDegree)
  obtain ⟨k, hk⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
  have hYk : ∀ j, (Y j).natDegree ≤ k + 1 := fun j ↦
    hk ▸ Finset.le_sup (f := fun j ↦ (Y j).natDegree) (Finset.mem_univ j)
  have hND : N ≤ δ + k + 1 := by omega
  have ⟨htop, hnext⟩ := sys_top_primL w0 A B δ k hA hB PA hPA Y hYk
    (fun i ↦ by rw [hY]; exact hG i _ (by omega)) (fun i ↦ by rw [hY]; exact hG i _ hND)
  have hsp : SpecialDegL w0 (lamML B PA δ) (betaML A B PA δ) (k + 1) := by
    refine ⟨fun j ↦ (Y j).coeff (k + 1), fun h0 ↦ ?_, htop, fun j ↦ (Y j).coeff k, fun i ↦ ?_⟩
    · have := congrFun h0 j0
      simp only [Pi.zero_apply] at this
      have hne : Y j0 ≠ 0 := fun h ↦ by
        rw [h, natDegree_zero] at hj0; omega
      rw [← hk, hD, hj0] at this
      exact hne (leadingCoeff_eq_zero.mp this)
    · exact hnext i
  have := hBs (k + 1) (by omega) hsp
  omega

end Tower.Sys
