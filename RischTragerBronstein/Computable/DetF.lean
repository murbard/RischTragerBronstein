import RischTragerBronstein.Computable.SysNorm

/-!
# A computable determinant (Laplace expansion), generic in the ring operations

`detF zero one add mul neg n M` expands along the first row. For any map `h` into a commutative ring
preserving the operations, `h (detF … M) = det (h ∘ M)` (`detF_spec`).
-/

open Matrix

namespace Tower.Sys

variable {β : Type*} (zero one : β) (add mul : β → β → β) (neg : β → β)

/-- **The determinant by Laplace expansion** along the first row. -/
def detF : (n : ℕ) → (Fin n → Fin n → β) → β
  | 0, _ => one
  | n + 1, M => (List.finRange (n + 1)).foldr (fun j acc ↦
      add (let c := mul (M 0 j) (detF n fun i k ↦ M i.succ (j.succAbove k))
           if (j : ℕ) % 2 = 0 then c else neg c) acc) zero

variable {R : Type*} [CommRing R] (h : β → R) (h0 : h zero = 0) (h1 : h one = 1)
  (hadd : ∀ a b, h (add a b) = h a + h b) (hmul : ∀ a b, h (mul a b) = h a * h b)
  (hneg : ∀ a, h (neg a) = -h a)
include h0 h1 hadd hmul hneg

lemma foldr_detF_sum {n : ℕ} (f : Fin n → β) :
    ∀ l : List (Fin n), h (l.foldr (fun j acc ↦ add (f j) acc) zero) = (l.map fun j ↦ h (f j)).sum
  | [] => by simp [h0]
  | j :: l => by rw [List.foldr_cons, hadd, foldr_detF_sum f l]; simp

/-- **The determinant commutes with operation-preserving maps.** -/
theorem detF_spec : ∀ (n : ℕ) (M : Fin n → Fin n → β),
    h (detF zero one add mul neg n M) = (Matrix.of fun i j ↦ h (M i j)).det
  | 0, M => by simp [detF, h1]
  | n + 1, M => by
    rw [detF, foldr_detF_sum zero one add mul neg h h0 h1 hadd hmul hneg _ (List.finRange (n + 1)),
      det_succ_row_zero,
      Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun j _ ↦ ?_
    have hsub : (Matrix.of fun i k ↦ h (M i k)).submatrix Fin.succ j.succAbove =
        Matrix.of fun i k ↦ h (M i.succ (j.succAbove k)) := by
      ext i k; rfl
    simp only
    rw [hsub, ← detF_spec n (fun i k ↦ M i.succ (j.succAbove k))]
    split_ifs with hj
    · rw [hmul]
      obtain ⟨r, hr⟩ : ∃ r, (j : ℕ) = 2 * r := ⟨(j : ℕ) / 2, by omega⟩
      rw [hr, pow_mul]; simp [Matrix.of_apply]
    · rw [hneg, hmul]
      obtain ⟨r, hr⟩ : ∃ r, (j : ℕ) = 2 * r + 1 := ⟨(j : ℕ) / 2, by omega⟩
      rw [hr, pow_succ, pow_mul]; simp [Matrix.of_apply]

end Tower.Sys
