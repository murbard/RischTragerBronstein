import RischTragerBronstein.Mixed.NKLogDecide

/-!
# Coordinate matrices of a basis of a curve

For a curve `S` over `C` and `C(x)`-independent `w₀, …, wₙ₋₁ ∈ C(x, y)` (`n = deg F`): the matrix
`T` of the `wᵢ` in the powers `yᵏ` and its inverse have entries `A/B` with `A, B ∈ C[x]`
(`exists_coordMats`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]

variable (S : CurveData C L)

/-- Elements of `C(x)` are quotients of polynomials. -/
lemma ratfun_reprC (c : C⟮S.x⟯) :
    ∃ A B : C[X], B ≠ 0 ∧ (c : L) = aeval S.x A / aeval S.x B := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  obtain ⟨A, B, hB, hc⟩ := IsFractionRing.div_surjective (A := C[X]) c
  refine ⟨A, B, nonZeroDivisors.ne_zero hB, ?_⟩
  rw [← hc, IntermediateField.coe_div, algebraMap_adjoinSimple, algebraMap_adjoinSimple]

/-- **Coordinate matrices of an independent family.** -/
theorem exists_coordMats (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯)
    (hindw : ∀ c : Fin S.F.natDegree → C⟮S.x⟯,
      ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) :
    ∃ (A B Ai Bi : Fin S.F.natDegree → Fin S.F.natDegree → C[X]),
      (∀ i k, B i k ≠ 0) ∧ (∀ i k, Bi i k ≠ 0) ∧
      (∀ i, (w i : L) = ∑ k, aeval S.x (A i k) / aeval S.x (B i k) * S.y ^ (k : ℕ)) ∧
      (∀ i j, ∑ k, aeval S.x (A i k) / aeval S.x (B i k) *
        (aeval S.x (Ai k j) / aeval S.x (Bi k j)) = if i = j then 1 else 0) ∧
      (∀ i j, ∑ k, aeval S.x (Ai i k) / aeval S.x (Bi i k) *
        (aeval S.x (A k j) / aeval S.x (B k j)) = if i = j then 1 else 0) := by
  classical
  haveI := IntermediateField.adjoin.finiteDimensional S.isIntegral
  have hfin : Module.finrank C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) = S.F.natDegree := by
    rw [IntermediateField.adjoin.finrank S.isIntegral, S.natDegree_minpoly]
  have hliw : LinearIndependent C⟮S.x⟯ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    exact hindw c (by simpa [Algebra.smul_def] using hc)
  let bw := basisOfLinearIndependentOfCardEqFinrank' _ hliw (by rw [Fintype.card_fin, hfin])
  have hbw : ∀ j, bw j = w j := fun j ↦ by simp [bw]
  set th : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯ := fun k ↦ (AdjoinSimple.gen C⟮S.x⟯ S.y) ^ (k : ℕ)
    with hth
  have hthL : ∀ k, ((th k : C⟮S.x⟯⟮S.y⟯) : L) = S.y ^ (k : ℕ) := fun k ↦ by
    simp [hth]
  have hlith : LinearIndependent C⟮S.x⟯ th := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h0 := S.coords_uniqueG (fun j ↦ if hj : j < S.F.natDegree then (c ⟨j, hj⟩ : L) else 0)
      (fun j hj ↦ by simp only [dif_pos hj]; exact (c ⟨j, hj⟩).2) (by
        rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (if hj : j < S.F.natDegree then
          (c ⟨j, hj⟩ : L) else 0) * S.y ^ j)]
        have := congrArg (fun z : C⟮S.x⟯⟮S.y⟯ ↦ (z : L)) hc
        simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Fin.is_lt, dif_pos, Fin.eta]
        rw [Algebra.smul_def, IntermediateField.coe_mul, hthL j]
        rfl) k k.2
    simp only [Fin.is_lt, dif_pos, Fin.eta] at h0
    exact Subtype.ext h0
  let bt := basisOfLinearIndependentOfCardEqFinrank' _ hlith (by rw [Fintype.card_fin, hfin])
  have hbt : ∀ k, bt k = th k := fun k ↦ by simp [bt]
  set cT : Fin S.F.natDegree → Fin S.F.natDegree → C⟮S.x⟯ := fun i k ↦ bt.repr (w i) k with hcT
  set cI : Fin S.F.natDegree → Fin S.F.natDegree → C⟮S.x⟯ := fun k j ↦ bw.repr (th k) j with hcI
  have hwT : ∀ i, (w i : L) = ∑ k, (cT i k : L) * S.y ^ (k : ℕ) := fun i ↦ by
    have h2 := congrArg (fun z : C⟮S.x⟯⟮S.y⟯ ↦ (z : L)) (bt.sum_repr (w i))
    simp only [AddSubmonoidClass.coe_finsetSum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hbt, Algebra.smul_def, IntermediateField.coe_mul, hthL]
    rfl
  have hTiT : ∀ l k, ∑ j, cI l j * cT j k = if l = k then 1 else 0 := by
    intro l k
    have h := congrArg (fun z ↦ bt.repr z k) (bw.sum_repr (th l))
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, hbw] at h
    have hr : bt.repr (th l) k = if l = k then 1 else 0 := by
      rw [← hbt l, bt.repr_self, Finsupp.single_apply]
    rw [← hr]
    exact h
  have hTTi : ∀ i j, ∑ k, cT i k * cI k j = if i = j then 1 else 0 := by
    have hM : (Matrix.of cI) * (Matrix.of cT) = 1 := by
      refine Matrix.ext fun l k ↦ ?_
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact hTiT l k
    have hM' := mul_eq_one_comm.mp hM
    intro i j
    have := congrArg (fun M ↦ M i j) hM'
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  choose A B hB hAB using fun i k ↦ S.ratfun_reprC (cT i k)
  choose Ai Bi hBi hABi using fun k j ↦ S.ratfun_reprC (cI k j)
  refine ⟨A, B, Ai, Bi, hB, hBi, fun i ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
  · rw [hwT i]; exact Finset.sum_congr rfl fun k _ ↦ by rw [← hAB]
  · have := congrArg (fun z : C⟮S.x⟯ ↦ (z : L)) (hTTi i j)
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul] at this
    rw [Finset.sum_congr rfl fun k _ ↦ by rw [← hAB, ← hABi], this]
    split_ifs <;> simp
  · have := congrArg (fun z : C⟮S.x⟯ ↦ (z : L)) (hTiT i j)
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul] at this
    rw [Finset.sum_congr rfl fun k _ ↦ by rw [← hAB, ← hABi], this]
    split_ifs <;> simp

end CurveData

end Curves
