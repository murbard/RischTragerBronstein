import RischTragerBronstein.Computable.SysNorm
import Mathlib.LinearAlgebra.Lagrange

/-!
# The interpolation check always passes

`lagrangeL N k` is the Lagrange basis polynomial of the node `k` among `0, …, N`
(`toPoly_lagrangeL`), so `∑ₖ ℓₖ kˡ = Xˡ` for `l ≤ N` (`eq_interpolate`) and **`vandCheck N` holds
for every `N`** (`vandCheck_true`).
-/

open Polynomial CPoly

namespace Tower.Sys

lemma toPoly_lagrange_foldr (k : ℕ) :
    ∀ l : List ℚ, toPoly (l.foldr (fun i acc ↦ CPoly.mul [-i / ((k : ℚ) - i), 1 / ((k : ℚ) - i)]
      acc) [1]) = (l.map fun i ↦ Lagrange.basisDivisor (k : ℚ) i).prod
  | [] => by simp [CPoly.toPoly]
  | i :: l => by
    rw [List.foldr_cons, CPoly.toPoly_mul, toPoly_lagrange_foldr k l, List.map_cons, List.prod_cons]
    congr 1
    simp only [Lagrange.basisDivisor, CPoly.toPoly_cons, CPoly.toPoly_nil]
    simp only [mul_zero, add_zero]
    rw [show (-i / ((k : ℚ) - i)) = -(((k : ℚ) - i)⁻¹ * i) by ring,
      show (1 / ((k : ℚ) - i)) = ((k : ℚ) - i)⁻¹ by ring]
    simp only [C_neg, C_mul]
    ring

lemma toPoly_lagrangeL (N k : ℕ) (_hk : k ≤ N) :
    toPoly (lagrangeL N k) =
      Lagrange.basis (Finset.range (N + 1)) (fun i : ℕ ↦ (i : ℚ)) k := by
  rw [lagrangeL]
  have e : ∀ L : List ℕ, (do let a ← L; pure (a : ℚ) : List ℚ) = L.map fun a : ℕ ↦ (a : ℚ) := by
    intro L; simp [List.map_eq_flatMap]
  rw [e, toPoly_lagrange_foldr, Lagrange.basis, List.map_map]
  have hnd : ((List.range (N + 1)).filter (· != k)).Nodup := (List.nodup_range).filter _
  have hset : ((List.range (N + 1)).filter (· != k)).toFinset = (Finset.range (N + 1)).erase k := by
    ext i; simp [and_comm]
  rw [← hset, List.prod_toFinset _ hnd]
  rfl

lemma sum_lagrange_pow (N l : ℕ) (hl : l ≤ N) :
    ∑ k ∈ Finset.range (N + 1), C ((k : ℚ) ^ l) * toPoly (lagrangeL N k) = (X ^ l : ℚ[X]) := by
  have hinj : Set.InjOn (fun i : ℕ ↦ (i : ℚ)) (Finset.range (N + 1) : Set ℕ) :=
    fun a _ b _ h ↦ by simpa using h
  have hdeg : (X ^ l : ℚ[X]).degree < (Finset.range (N + 1)).card := by
    rw [degree_X_pow, Finset.card_range]; exact_mod_cast Nat.lt_succ_of_le hl
  rw [Lagrange.eq_interpolate hinj hdeg, Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [toPoly_lagrangeL N k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), eval_pow, eval_X]

/-- **The interpolation check holds for every `N`.** -/
theorem vandCheck_true (N : ℕ) : vandCheck N = true := by
  simp only [vandCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro j hj l hl
  have h := congrArg (fun P : ℚ[X] ↦ P.coeff j) (sum_lagrange_pow N l (by omega))
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coeff_toPoly, mul_comm]

end Tower.Sys
