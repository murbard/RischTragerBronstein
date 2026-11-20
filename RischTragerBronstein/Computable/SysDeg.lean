import RischTragerBronstein.Computable.SysLoop

/-!
# Coupled Risch systems: the degree bound at a primitive level

For `A Y′ + B Y = G` over `K[t]`, `t′ = w0` (`b = 0`), with `deg A ≤ δ + 1`, `deg B ≤ δ` and an
invertible leading matrix `A_{δ+1}` (left inverse `PA`): if `deg Y = D ≥ 1` and `G` has no
coefficients from `D + δ` on, the two top coefficients give (`sys_top_prim`)
* `Y_D′ = 0` — a nonzero constant vector `c`;
* `Y_{D−1}′ = −(D w0 c + β c)`, `β = PA B_δ`.
So `D` is a *special degree* (`SpecialDeg`); if every special degree is `≤ Bs`, then
`deg Y ≤ max Bs (N − δ)` where `G` vanishes from `N` on (`sys_deg_prim`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K]
variable (w0 : K) {n : ℕ} (A B : Fin n → Fin n → K[X])

/-- The coefficient one below the top of a product. -/
lemma coeff_mul_below (p q : K[X]) (δ k : ℕ) (hp : p.natDegree ≤ δ + 1) (hq : q.natDegree ≤ k + 1) :
    (p * q).coeff (δ + k + 1) = p.coeff (δ + 1) * q.coeff k + p.coeff δ * q.coeff (k + 1) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ p.coeff i * q.coeff j)]
  rw [Finset.sum_eq_add_of_mem (δ + 1) δ (Finset.mem_range.mpr (by omega))
    (Finset.mem_range.mpr (by omega)) (by omega) fun i hi hne ↦ ?_]
  · rw [show δ + k + 1 - (δ + 1) = k by omega, show δ + k + 1 - δ = k + 1 by omega]
  · rcases lt_or_gt_of_ne hne.1 with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (show q.natDegree < δ + k + 1 - i by omega), mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega), zero_mul]

/-- The matrix `β = PA B_δ`. -/
noncomputable def betaM (PA : Fin n → Fin n → K) (δ : ℕ) : Fin n → Fin n → K :=
  fun i j ↦ ∑ l, PA i l * (B l j).coeff δ

/-- **The two top coefficients at a primitive level.** -/
theorem sys_top_prim (δ k : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ + 1)
    (hB : ∀ i j, (B i j).natDegree ≤ δ) (PA : Fin n → Fin n → K)
    (hPA : ∀ i l, ∑ j, PA i j * (A j l).coeff (δ + 1) = if i = l then 1 else 0)
    (Y : Fin n → K[X]) (hY : ∀ j, (Y j).natDegree ≤ k + 1)
    (h1 : ∀ i, (LopV w0 0 A B Y i).coeff (k + 1 + (δ + 1)) = 0)
    (h2 : ∀ i, (LopV w0 0 A B Y i).coeff (δ + k + 1) = 0) :
    (∀ j, ((Y j).coeff (k + 1))′ = 0) ∧
      ∀ i, ((Y i).coeff k)′ = -((k + 1 : ℕ) * w0 * (Y i).coeff (k + 1) +
        ∑ j, betaM B PA δ i j * (Y j).coeff (k + 1)) := by
  have hB' : ∀ i j, (B i j).natDegree ≤ δ + 1 := fun i j ↦ (hB i j).trans (Nat.le_succ _)
  -- apply the left inverse to a vector equation `A_top v = u`
  have inv : ∀ v u : Fin n → K, (∀ l, ∑ j, (A l j).coeff (δ + 1) * v j = u l) →
      ∀ i, v i = ∑ l, PA i l * u l := by
    intro v u hvu i
    simp only [← hvu, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ l, PA i l * ((A l j).coeff (δ + 1) * v j) = (if i = j then 1 else 0) * v j :=
      fun j ↦ by rw [← hPA i j, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    simp [this]
  have htop : ∀ j, ((Y j).coeff (k + 1))′ = 0 := by
    intro j
    have := inv (fun j ↦ ((Y j).coeff (k + 1))′) 0 (fun l ↦ by
      have h := h1 l
      rw [coeff_LopV_top w0 0 A B (δ + 1) hA hB' Y (k + 1) hY l] at h
      rw [Pi.zero_apply, ← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [coeff_eq_zero_of_natDegree_lt (show (B l j).natDegree < δ + 1 by linarith [hB l j])]
      simp) j
    simpa using this
  refine ⟨htop, fun i ↦ ?_⟩
  have := inv (fun j ↦ ((Y j).coeff k)′ + (k + 1 : ℕ) * w0 * (Y j).coeff (k + 1))
    (fun l ↦ -∑ j, (B l j).coeff δ * (Y j).coeff (k + 1)) (fun l ↦ by
      have h := h2 l
      rw [LopV, finsetSum_coeff] at h
      rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hBc : (B l j * Y j).coeff (δ + k + 1) = (B l j).coeff δ * (Y j).coeff (k + 1) :=
        coeff_mul_add_eq_of_natDegree_le (hB l j) (hY j)
      rw [coeff_add, coeff_mul_below _ _ δ k (hA l j) (natDegree_DzL_le w0 0 _ _ (hY j)), hBc,
        coeff_DzL, coeff_DzL, coeff_eq_zero_of_natDegree_lt (show (Y j).natDegree < k + 1 + 1 by
          linarith [hY j]), htop j]
      push_cast; ring) i
  have e : ∑ j, betaM B PA δ i j * (Y j).coeff (k + 1) =
      ∑ l, PA i l * ∑ j, (B l j).coeff δ * (Y j).coeff (k + 1) := by
    simp only [betaM, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [e]
  simp only [mul_neg, Finset.sum_neg_distrib] at this
  linear_combination this

/-- **A special degree**: a nonzero constant vector `c` with `(D w0 + β) c` a derivative. -/
def SpecialDeg (β : Fin n → Fin n → K) (D : ℕ) : Prop :=
  ∃ c : Fin n → K, c ≠ 0 ∧ (∀ j, (c j)′ = 0) ∧
    ∃ y : Fin n → K, ∀ i, (y i)′ = -((D : K) * w0 * c i + ∑ j, β i j * c j)

/-- **The degree bound at a primitive level.** -/
theorem sys_deg_prim (δ : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ + 1)
    (hB : ∀ i j, (B i j).natDegree ≤ δ) (PA : Fin n → Fin n → K)
    (hPA : ∀ i l, ∑ j, PA i j * (A j l).coeff (δ + 1) = if i = l then 1 else 0) (Bs N : ℕ)
    (hBs : ∀ D, 1 ≤ D → SpecialDeg w0 (betaM B PA δ) D → D ≤ Bs)
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
  have ⟨htop, hnext⟩ := sys_top_prim w0 A B δ k hA hB PA hPA Y hYk
    (fun i ↦ by rw [hY]; exact hG i _ (by omega)) (fun i ↦ by rw [hY]; exact hG i _ hND)
  have hsp : SpecialDeg w0 (betaM B PA δ) (k + 1) := by
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
