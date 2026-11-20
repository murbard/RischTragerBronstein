import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.BigOperators.Fin

/-!
# Arithmetic in `K(θ)`, `θⁿ = A`

Elements `∑_{i<n} cᵢ θⁱ`. Multiplication by `θʲ` (`col_lemma`) and by `∑ wⱼ θʲ` (`mul_lemma`) is
given by the matrix `mcolL` (`θⁿ = A` folds the high powers). **Inverses** (`inv_lemma`): when
`1, θ, …, θⁿ⁻¹` are linearly independent over a subfield `K` containing `A` and the `cᵢ`,
`(∑ cᵢ θⁱ)⁻¹ = ∑ (radj i / det M) θⁱ`, with `radj i` the determinant of `M` with first row
replaced by `eᵢ` (the first column of the adjugate); this also holds when the element is `0`
(`det M = 0`, both sides `0`).
-/

open Finset Matrix

namespace Curves.MT.Front

variable {L : Type*} [Field L]

/-- The multiplication matrix: entry `(k, j)` is the coefficient of `θᵏ` in `u θʲ`. -/
def mcolL (n : ℕ) (A : L) (c : ℕ → L) (k j : ℕ) : L :=
  if j ≤ k then c (k - j) else A * c (k + n - j)

lemma col_lemma (n : ℕ) (A θ : L) (hθ : θ ^ n = A) (c : ℕ → L) (j : ℕ) (hj : j ≤ n) :
    (∑ i ∈ range n, c i * θ ^ i) * θ ^ j = ∑ k ∈ range n, mcolL n A c k j * θ ^ k := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + j := ⟨n - j, by omega⟩
  have e : ∀ f : ℕ → L, ∑ k ∈ range (d + j), f k =
      ∑ x ∈ range j, f x + ∑ x ∈ range d, f (j + x) := fun f ↦ by
    rw [add_comm d j, Finset.sum_range_add]
  rw [Finset.sum_mul, Finset.sum_range_add, e, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hx' := Finset.mem_range.mp hx
    rw [mcolL, if_neg (by omega), show x + (d + j) - j = d + x by omega, ← hθ]
    ring
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mcolL, if_pos (by omega), show j + x - j = x by omega]
    ring

lemma mul_lemma (n : ℕ) (A θ : L) (hθ : θ ^ n = A) (c w : ℕ → L) :
    (∑ i ∈ range n, c i * θ ^ i) * (∑ j ∈ range n, w j * θ ^ j) =
      ∑ k ∈ range n, (∑ j ∈ range n, mcolL n A c k j * w j) * θ ^ k := by
  calc _ = ∑ j ∈ range n, w j * ((∑ i ∈ range n, c i * θ ^ i) * θ ^ j) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∑ j ∈ range n, w j * ∑ k ∈ range n, mcolL n A c k j * θ ^ k :=
        Finset.sum_congr rfl fun j hj ↦ by
          rw [col_lemma n A θ hθ c j (le_of_lt (Finset.mem_range.mp hj))]
    _ = _ := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The multiplication matrix over `Fin n`. -/
def mMat (n : ℕ) (A : L) (c : ℕ → L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun r s ↦ mcolL n A c r s

/-- The first column of the adjugate, as a determinant. -/
def radj (n : ℕ) (A : L) (c : ℕ → L) (i : ℕ) : L :=
  (Matrix.of fun r s : Fin n ↦ if (r : ℕ) = 0 then (if (s : ℕ) = i then 1 else 0)
    else mcolL n A c r s).det

lemma radj_eq (n : ℕ) (A : L) (c : ℕ → L) (i : ℕ) (hi : i < n + 1) :
    radj (n + 1) A c i = adjugate (mMat (n + 1) A c) ⟨i, hi⟩ 0 := by
  rw [adjugate_apply, radj]
  congr 1
  ext r s
  rw [Matrix.of_apply, Matrix.updateRow_apply]
  by_cases hr : r = 0
  · subst hr
    rw [if_pos rfl, if_pos (show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl), Pi.single_apply]
    by_cases hs : s = ⟨i, hi⟩
    · rw [if_pos hs, if_pos (by rw [hs])]
    · rw [if_neg hs, if_neg (fun h ↦ hs (Fin.ext h))]
  · rw [if_neg hr, if_neg (show ¬((r : ℕ) = 0) from fun h ↦ hr (Fin.ext h))]; rfl

/-- **The inverse in `K(θ)`.** -/
theorem inv_lemma (K : Subfield L) (n : ℕ) (A θ : L) (hθ : θ ^ (n + 1) = A) (hA : A ∈ K)
    (c : ℕ → L) (hc : ∀ i, c i ∈ K)
    (hind : ∀ w : ℕ → L, (∀ i, w i ∈ K) → ∑ i ∈ range (n + 1), w i * θ ^ i = 0 →
      ∀ i < n + 1, w i = 0) :
    (∑ i ∈ range (n + 1), c i * θ ^ i)⁻¹ =
      ∑ i ∈ range (n + 1), (radj (n + 1) A c i * (mMat (n + 1) A c).det⁻¹) * θ ^ i := by
  classical
  set M := mMat (n + 1) A c with hM
  have hmem : ∀ k j, mcolL (n + 1) A c k j ∈ K := fun k j ↦ by
    unfold mcolL; split
    · exact hc _
    · exact mul_mem hA (hc _)
  by_cases hD : M.det = 0
  · rw [hD, _root_.inv_zero]
    simp only [mul_zero, zero_mul, Finset.sum_const_zero]
    set Mk : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun r s ↦ ⟨mcolL (n + 1) A c r s, hmem _ _⟩
    have hMk : Mk.det = 0 := by
      apply K.subtype.injective
      rw [RingHom.map_det, map_zero]
      have : K.subtype.mapMatrix Mk = M := by ext r s; rfl
      rw [this, hD]
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMk
    set W : ℕ → L := fun j ↦ if h : j < n + 1 then (w ⟨j, h⟩ : L) else 0 with hW
    have hWK : ∀ j, W j ∈ K := fun j ↦ by
      simp only [hW]; split
      · exact SetLike.coe_mem _
      · exact zero_mem _
    have hprod := mul_lemma (n + 1) A θ hθ c W
    have hinner : ∀ k ∈ range (n + 1), ∑ j ∈ range (n + 1), mcolL (n + 1) A c k j * W j = 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ mcolL (n + 1) A c k j * W j)]
      have h1 := congrFun hw ⟨k, hk'⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      have h2 : K.subtype (∑ x, Mk ⟨k, hk'⟩ x * w x) = 0 := by rw [h1, map_zero]
      rw [map_sum] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hW, dif_pos j.isLt, Mk, Matrix.of_apply, map_mul]
      rfl
    have hz : ∑ k ∈ range (n + 1), (∑ j ∈ range (n + 1), mcolL (n + 1) A c k j * W j) * θ ^ k =
        0 := Finset.sum_eq_zero fun k hk ↦ by rw [hinner k hk, zero_mul]
    rw [hz] at hprod
    have hWne : ∑ j ∈ range (n + 1), W j * θ ^ j ≠ 0 := by
      intro h0
      apply hw0
      funext j
      have := hind W hWK h0 j j.isLt
      simp only [hW, dif_pos j.isLt] at this
      exact Subtype.ext this
    rw [(mul_eq_zero.mp hprod).resolve_right hWne, _root_.inv_zero]
  · apply inv_eq_of_mul_eq_one_right
    rw [mul_lemma (n + 1) A θ hθ c]
    have hinner : ∀ k ∈ range (n + 1), ∑ j ∈ range (n + 1),
        mcolL (n + 1) A c k j * (radj (n + 1) A c j * M.det⁻¹) = if k = 0 then 1 else 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ mcolL (n + 1) A c k j *
        (radj (n + 1) A c j * M.det⁻¹))]
      have hma := congrFun (congrFun (mul_adjugate M) ⟨k, hk'⟩) 0
      rw [Matrix.mul_apply] at hma
      have : ∑ j : Fin (n + 1), mcolL (n + 1) A c k j * (radj (n + 1) A c j * M.det⁻¹) =
          (∑ j : Fin (n + 1), M ⟨k, hk'⟩ j * adjugate M j 0) * M.det⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [radj_eq n A c j j.isLt]
        simp only [hM, mMat, Matrix.of_apply]
        ring
      rw [this, hma, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases hk0 : k = 0
      · subst hk0; simp [mul_inv_cancel₀ hD]
      · rw [if_neg (fun h ↦ hk0 (by simpa using congrArg Fin.val h)), if_neg hk0, mul_zero,
          zero_mul]
    rw [Finset.sum_congr rfl (fun k hk ↦ by rw [hinner k hk] :
      ∀ k ∈ range (n + 1), (∑ j ∈ range (n + 1), mcolL (n + 1) A c k j *
        (radj (n + 1) A c j * M.det⁻¹)) * θ ^ k = (if k = 0 then 1 else 0) * θ ^ k)]
    simp

end Curves.MT.Front
