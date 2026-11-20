import RischTragerBronstein.Computable.SysDeg

/-!
# Coupled Risch systems: the degree bound at an exponential level

For `A Y′ + B Y = G` over `K[t]`, `t′ = b t`, with `A_δ = I`, `B_δ = −d b I` (the shape of the
`W`-system when the matrix vanishes at infinity and the denominator has degree `d`), the top
coefficient `w` of a solution of degree `D` beyond the right-hand side satisfies
`w′ + (D − d) b w = 0`; at an exponential level (no nonzero solution of `z′ + j b z = 0`, `j ≠ 0`)
this forces `D = d`. Hence `deg Y ≤ max d (N − δ)` (`sys_deg_exp`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] (b : K) {n : ℕ}
  (A B : Fin n → Fin n → K[X])

/-- **The degree bound at an exponential level.** -/
theorem sys_deg_exp (δ : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (hAδ : ∀ i j, (A i j).coeff δ = if i = j then 1 else 0) (dD : ℕ)
    (hBδ : ∀ i j, (B i j).coeff δ = if i = j then -((dD : K) * b) else 0)
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0) (N : ℕ)
    (Y G : Fin n → K[X]) (hG : ∀ i d, N ≤ d → (G i).coeff d = 0) (hY : LopV 0 b A B Y = G)
    (j : Fin n) : (Y j).natDegree ≤ max dD (N - δ) := by
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
  have htop : ∀ i, ((Y i).coeff D)′ + ((D - dD : ℤ) : K) * b * (Y i).coeff D = 0 := by
    intro i
    have h := congrArg (fun P : K[X] ↦ P.coeff (D + δ)) (congrFun hY i)
    rw [coeff_LopV_top 0 b A B δ hA hB Y D hYD i, hG i _ (by omega)] at h
    simp only [hAδ, hBδ, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h
    push_cast
    linear_combination h
  have hwj0 : (Y j0).coeff D ≠ 0 := by
    have hne : Y j0 ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hj0; omega
    rw [hD, hj0]
    exact mt leadingCoeff_eq_zero.mp hne
  exact hom _ hwj0 (D - dD) (by omega) (htop j0)

end Tower.Sys
