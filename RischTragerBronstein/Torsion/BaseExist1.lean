import RischTragerBronstein.Torsion.GlobalExist

/-!
# Base-point data exist (1): left inverses, the unit at infinity, Newton values

* **`detCheck_complete`**: invertible matrices at the base points have left inverses passing
  `detCheck`;
* **`infU0_ne_zero`**: the coefficient `U₀` of the basis check at infinity is `1`-led, non-zero;
* **`newtonVals_eq`**: the Newton lifts from a simple root `y₀` of `F(a, Y)` keep the constant
  term `y₀`, and every divisor value is `F_Y(a, y₀)` (so non-zero).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Det

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Invertible matrices have certified left inverses.** -/
lemma leftInvCheck_of_det {n : ℕ} (M : ℕ → ℕ → F)
    (hdet : (Matrix.of fun k j : Fin n ↦ M k j).det ≠ 0) : ∃ Lm, leftInvCheck Lm M n n = true := by
  classical
  set A : Matrix (Fin n) (Fin n) F := Matrix.of fun k j : Fin n ↦ M k j with hA
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
  set Lm : List (List F) := (List.range n).map fun i ↦ (List.range n).map fun r ↦
    if h : i < n ∧ r < n then A⁻¹ ⟨i, h.1⟩ ⟨r, h.2⟩ else 0 with hLm
  refine ⟨Lm, ?_⟩
  simp only [leftInvCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi j hj
  have e1 : ∀ r (hr : r < n), (Lm.getD i []).getD r 0 = A⁻¹ ⟨i, hi⟩ ⟨r, hr⟩ := fun r hr ↦ by
    simp [hLm, List.getD_eq_getElem?_getD, hi, hr]
  have e2 := congrFun (congrFun hinv ⟨i, hi⟩) ⟨j, hj⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at e2
  rw [← Fin.sum_univ_eq_sum_range (fun r ↦ (Lm.getD i []).getD r 0 * M r j)]
  simp only [Fin.ext_iff] at e2
  rw [← e2]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [e1 r r.2]
  rfl

/-- **Certified left inverses at all base points.** -/
theorem detCheck_complete (n g : ℕ) (Bc : List (BPoly F)) (xs : List F) (ys : List (List F))
    (h : ∀ i < g, (Matrix.of fun k j : Fin n ↦ detMat Bc xs ys i k j).det ≠ 0) :
    ∃ Ls, detCheck n g Bc xs ys Ls = true := by
  classical
  have hL : ∀ i, ∃ Lm : List (List F), i < g → leftInvCheck Lm (detMat Bc xs ys i) n n = true :=
    fun i ↦ if hi : i < g then (leftInvCheck_of_det _ (h i hi)).elim fun Lm hLm ↦ ⟨Lm, fun _ ↦ hLm⟩
      else ⟨[], fun h' ↦ absurd h' hi⟩
  choose Lf hLf using hL
  refine ⟨(List.range g).map Lf, ?_⟩
  simp only [detCheck, List.all_eq_true, List.mem_range]
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  exact hLf i hi

end Det

section Inf

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The unit at infinity**: `U₀ = D̃(0)` is the leading coefficient `1` of `D`. -/
lemma infU0_ne_zero (I : IntBasisCert F) (hDl : I.Dc.getLast? = some 1) (hN : 0 < I.infc.N) :
    infU0 I ≠ 0 := by
  have hlast : I.Dc.getD (I.Dc.length - 1) 0 = 1 := by
    rw [List.getLast?_eq_getElem?] at hDl
    rw [List.getD_eq_getElem?_getD, hDl]; rfl
  rw [infU0, compC_shift_getD_zero' _ _ _ hN, Kron.evalC_eq, ← coeff_zero_eq_eval_zero,
    coeff_toPoly, reflectC, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp only [Nat.sub_zero]
  rw [hlast]; exact one_ne_zero

end Inf

section Newton

variable {F : Type*} [Field F] [DecidableEq F]

lemma eval_eval_poly (P : F[X][X]) (q : F[X]) (x : F) :
    (P.eval q).eval x = (P.map (evalRingHom x)).eval (q.eval x) := by
  rw [← coe_evalRingHom, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id, eval_map]

lemma coeff_zero_eval_toB (W : BPoly F) (Z : CPoly F) (a : F) :
    ((toB (W.map fun q ↦ compC q (shiftC a 1))).eval (toPoly Z)).coeff 0 =
      evalB W a (Z.getD 0 0) := by
  rw [toB_shiftF, evalB_eq, evalW, coeff_zero_eq_eval_zero, eval_eval_poly, Polynomial.map_map,
    ← coeff_zero_eq_eval_zero, coeff_toPoly]
  congr 2
  refine RingHom.ext fun p ↦ ?_
  simp [eval_comp]

lemma derivYB_shift (W : BPoly F) (a : F) :
    toB (derivYB (W.map fun q ↦ compC q (shiftC a 1))) =
      toB ((derivYB W).map fun q ↦ compC q (shiftC a 1)) := by
  rw [toB_derivYB, toB_shiftF, toB_shiftF, toB_derivYB, derivative_map]

/-- **The Newton values at a simple root.** -/
theorem newtonVals_eq (W : BPoly F) (a y0 : F) (hroot : evalB W a y0 = 0) {L : ℕ} (hL : 0 < L) :
    ∀ (k : ℕ) (Z : CPoly F), Z.getD 0 0 = y0 →
      ∀ v ∈ newtonVals (W.map fun q ↦ compC q (shiftC a 1)) L k Z, v = evalB (derivYB W) a y0
  | 0, Z, _, v, hv => by simp [newtonVals] at hv
  | k + 1, Z, hZ, v, hv => by
    set H := W.map fun q ↦ compC q (shiftC a 1) with hH
    have hval : (evalBT (derivYB H) Z L).getD 0 0 = evalB (derivYB W) a y0 := by
      rw [evalBT_getD Z L _ 0 hL, ← hZ]
      have e : toB (derivYB H) = toB ((derivYB W).map fun q ↦ compC q (shiftC a 1)) :=
        derivYB_shift W a
      rw [e, coeff_zero_eval_toB]
    have hV0 : (evalBT H Z L).getD 0 0 = 0 := by
      rw [evalBT_getD Z L _ 0 hL, coeff_zero_eval_toB, hZ, hroot]
    simp only [newtonVals, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hval
    · refine newtonVals_eq W a y0 hroot hL k _ ?_ v hv
      rw [List.getD_eq_getElem _ _ (by simpa using hL), List.getElem_map, List.getElem_range, hZ]
      have : (sDivT (evalBT H Z L) (evalBT (derivYB H) Z L) L).getD 0 0 = 0 := by
        have hd : sDivT (evalBT H Z L) (evalBT (derivYB H) Z L) L =
            divTrunc (evalBT H Z L) (evalBT (derivYB H) Z L) L := rfl
        rw [hd, divTrunc_getD_le _ _ 1 L 0 one_pos hL]
        simp only [divTrunc, List.nil_append, List.getD_cons_zero, Finset.range_zero,
          Finset.sum_empty, sub_zero, hV0, zero_div]
      rw [this, sub_zero]

end Newton

end Curves
