import RischTragerBronstein.Torsion.KernelComplete

/-!
# Completeness of the failed-test certificate

* `nullBasis_pivot`: every vector of `nullBasis vs` has a coefficient `1` (at its pivot), so it is a
  non-trivial relation;
* `princWit_of_rel`: a non-trivial relation among the columns `kerCols` of the test gives a
  principal-witness certificate (`princWitCheckN`);
* **`nonPrincOK_complete`**: if the principality test fails (over an extension, with exact
  expansions within the certified precision), the null basis is empty and `nonPrincOK` passes.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Pivot

variable {R : Type*} [Field R] [DecidableEq R]

lemma coeff_lcomb_eq_zero (N : ℕ) : ∀ (a : List R) (ps : List (CPoly R)),
    (∀ p ∈ ps, p.length ≤ N) → (lcomb a ps).coeff N = 0
  | [], _, _ => by simp [lcomb]
  | _ :: _, [], _ => by simp [lcomb]
  | c :: a, p :: ps, h => by
    have ih := coeff_lcomb_eq_zero N a ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq)
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [coeff_add, ih, add_zero, coeff_C_mul, coeff_toPoly,
      List.getD_eq_default _ _ (h p List.mem_cons_self), mul_zero]

/-- The invariant of the elimination. -/
def PivInv (N : ℕ) (st : List (CPoly R × CPoly R) × List (CPoly R)) : Prop :=
  (∀ p ∈ st.1, p.2.length ≤ N) ∧ ∀ w ∈ st.2, ∃ t < N, w.getD t 0 = 1

lemma pivInv_step (N : ℕ) (st : List (CPoly R × CPoly R) × List (CPoly R)) (v : CPoly R)
    (h : PivInv N st) : PivInv (N + 1) (nsStep st (v, unitL N)) := by
  obtain ⟨h1, h2⟩ := h
  unfold nsStep
  cases hls : linSolve (st.1.map Prod.fst) v with
  | none =>
    refine ⟨fun p hp ↦ ?_, fun w hw ↦ ?_⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact (h1 p hp).trans (Nat.le_succ _)
      · simp at hp; subst hp; simp [unitL]
    · obtain ⟨t, ht, hw⟩ := h2 w hw
      exact ⟨t, by omega, hw⟩
  | some a =>
    refine ⟨fun p hp ↦ (h1 p hp).trans (Nat.le_succ _), fun w hw ↦ ?_⟩
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨t, ht, hw⟩ := h2 w hw
      exact ⟨t, by omega, hw⟩
    · simp only [List.mem_singleton] at hw
      subst hw
      refine ⟨N, by omega, ?_⟩
      rw [← coeff_toPoly (sub (unitL N) (lcombL a (st.1.map Prod.snd))) N, toPoly_sub, toPoly_lcombL, coeff_sub, toPoly_unitLF, coeff_X_pow_self,
        coeff_lcomb_eq_zero N _ _ fun p hp ↦ ?_, sub_zero]
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact h1 q hq

lemma pivInv_foldl (vs : List (CPoly R)) (N : ℕ) :
    PivInv N (((List.range N).map fun j ↦ (vs.getD j [], unitL j)).foldl nsStep ([], [])) := by
  induction N with
  | zero => exact ⟨by simp, by simp⟩
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_singleton,
      List.foldl_cons, List.foldl_nil]
    exact pivInv_step N _ _ ih

/-- **Null-basis vectors are non-trivial.** -/
theorem nullBasis_pivot (vs : List (CPoly R)) :
    ∀ w ∈ nullBasis vs, ∃ t < vs.length, w.getD t 0 = 1 :=
  (pivInv_foldl vs vs.length).2

lemma lcomb_eq_range : ∀ (w : List R) (vs : List (CPoly R)),
    lcomb w vs = ∑ idx ∈ Finset.range vs.length, C (w.getD idx 0) * toPoly (vs.getD idx [])
  | [], vs => by simp [lcomb]
  | c :: w, [] => by simp [lcomb]
  | c :: w, v :: vs => by
    have ih := lcomb_eq_range w vs
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

end Pivot

section Complete

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]
variable (n M : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F)
  (cL : List (BranchCert F)) (bL : List (List ℕ))

lemma map_getD_range {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i ↦ l.getD i d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ h2]

lemma sum_map_eq_range {α : Type*} {A : Type*} [AddCommMonoid A] (l : List α) (d : α) (h : α → A) :
    (l.map h).sum = ∑ i ∈ Finset.range l.length, h (l.getD i d) := by
  conv_lhs => rw [← map_getD_range l d, List.map_map]
  exact sum_range_list _ _

/-- The admissible columns. -/
def colsL : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
    decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d)

lemma colsL_nodup : (colsL n M δL).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun i _ ↦ ?_, ?_⟩
  · exact ((List.nodup_range).filter _).map fun a b h ↦ by simpa using h
  · refine (List.nodup_range).pairwise_of_forall_ne fun i _ i' _ hii' ↦ ?_
    simp only [Function.onFun, List.disjoint_iff_ne, List.mem_map, List.mem_filter]
    rintro _ ⟨d, -, rfl⟩ _ ⟨d', -, rfl⟩ h
    exact hii' (congrArg Prod.fst h)

lemma mem_colsL {i d : ℕ} : (i, d) ∈ colsL n M δL ↔ i < n ∧ d + δL.getD i 0 ≤ M := by
  simp only [colsL, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', d', ⟨-, hv⟩, rfl, rfl⟩; exact ⟨hi', hv⟩
  · rintro ⟨hi, hv⟩; exact ⟨i, hi, d, ⟨by omega, hv⟩, rfl, rfl⟩

lemma kerCols_eq (m : ℕ) : kerCols n M δL Bc Dc αL cL bL m =
    (colsL n M δL).map fun id ↦ ((List.range m).flatMap fun j ↦ (List.range n).flatMap fun k ↦
      (List.range (rowsN Dc αL cL bL j k)).map fun t ↦ (j, k, t)).map fun jkt ↦
        testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2 := rfl

/-- **A non-trivial relation gives a principal witness.** -/
theorem princWit_of_rel (w : List F)
    (hw : lcomb w (kerCols n M δL Bc Dc αL cL bL αL.length) = 0) (t0 : ℕ)
    (ht0 : t0 < (kerCols n M δL Bc Dc αL cL bL αL.length).length) (hw0 : w.getD t0 0 ≠ 0)
    (hside : testSideN n Dc αL cL bL = true) :
    ∃ G, princWitCheckN n M δL Bc Dc αL cL bL G = true := by
  classical
  set cols := colsL n M δL with hcols
  set rows := (List.range αL.length).flatMap fun j ↦ (List.range n).flatMap fun k ↦
    (List.range (rowsN Dc αL cL bL j k)).map fun t ↦ (j, k, t) with hrows
  set cN : ℕ → ℕ → F := fun i d ↦ w.getD (cols.idxOf (i, d)) 0 with hcN
  set G : List (List F) := (List.range n).map fun i ↦ (List.range (M + 1)).map fun d ↦ cN i d
  have hG : ∀ i < n, ∀ d < M + 1, (G.getD i []).getD d 0 = cN i d := fun i hi d hd ↦ by
    simp [G, List.getD_eq_getElem?_getD, hi, hd]
  have hlen : (kerCols n M δL Bc Dc αL cL bL αL.length).length = cols.length := by
    rw [kerCols_eq]; simp [hcols]
  have hnd := colsL_nodup n M δL
  refine ⟨G, ?_⟩
  simp only [princWitCheckN, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, List.any_eq_true]
  refine ⟨⟨hside, ?_⟩, ?_⟩
  · -- the non-zero coefficient
    rw [hlen] at ht0
    rcases hid : cols[t0] with ⟨i0, d0⟩
    have hmem : (i0, d0) ∈ cols := hid ▸ List.getElem_mem ht0
    obtain ⟨hi0, hv0⟩ := (mem_colsL n M δL).mp hmem
    have hidx : cols.idxOf (i0, d0) = t0 := by
      rw [← hid]; exact hnd.idxOf_getElem t0 ht0
    refine ⟨i0, hi0, d0, by omega, ?_⟩
    rw [hG i0 hi0 d0 (by omega)]
    exact ⟨hv0, by simp only [hcN, hidx]; exact hw0⟩
  · -- the rows
    intro j hj k hk t ht
    have hmem : (j, k, t) ∈ rows := by
      simp only [hrows, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨j, hj, k, hk, t, ht, rfl⟩
    obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hmem
    have hc := congrArg (·.coeff r) hw
    simp only [lcomb_eq_range, finsetSum_coeff, coeff_C_mul, coeff_toPoly,
      Polynomial.coeff_zero] at hc
    rw [hlen] at hc
    have hterm : ∀ idx ∈ Finset.range cols.length,
        w.getD idx 0 * ((kerCols n M δL Bc Dc αL cL bL αL.length).getD idx []).getD r 0 =
          (fun id : ℕ × ℕ ↦ cN id.1 id.2 * testEntryN Bc Dc αL cL j k t id.1 id.2)
            (cols.getD idx (0, 0)) := by
      intro idx hidx
      have hidx' : idx < cols.length := Finset.mem_range.mp hidx
      have e1 : (kerCols n M δL Bc Dc αL cL bL αL.length).getD idx [] =
          rows.map fun jkt ↦ testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 cols[idx].1 cols[idx].2 := by
        rw [kerCols_eq, List.getD_eq_getElem _ _ (by simpa [hcols] using hidx'), List.getElem_map]
      have e2 : (rows.map fun jkt ↦ testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 cols[idx].1
          cols[idx].2).getD r 0 = testEntryN Bc Dc αL cL j k t cols[idx].1 cols[idx].2 := by
        rw [List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_map, hget]
      rw [e1, e2, List.getD_eq_getElem _ _ hidx']
      simp only [hcN, Prod.mk.eta]
      congr 2
      exact (hnd.idxOf_getElem idx hidx').symm
    rw [Finset.sum_congr rfl hterm, ← sum_map_eq_range cols (0, 0)
      (fun id : ℕ × ℕ ↦ cN id.1 id.2 * testEntryN Bc Dc αL cL j k t id.1 id.2), hcols, colsL] at hc
    have hsc := sum_cols n M δL (fun i d ↦ cN i d * testEntryN Bc Dc αL cL j k t i d)
    rw [hsc] at hc
    refine Eq.trans (Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun d hd ↦ ?_) hc
    split_ifs with hv
    · rw [hG i (Finset.mem_range.mp hi) d (Finset.mem_range.mp hd)]
    · rw [zero_mul]

variable (ψ : F →+* K)

/-- **Completeness of `nonPrincOK`**: a failing test (over any extension, with expansions within the
certified precision) is certified. -/
theorem nonPrincOK_complete (P : ℕ) (Lm : List (List F)) (hside : testSideN n Dc αL cL bL = true)
    (Y : Fin αL.length → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin αL.length) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k [])))
    (hnot : ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M
      (fun q : Fin αL.length × Fin n ↦ (cL.getD q.1 ⟨1, [], 0⟩).N) (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) (cL.getD q.1 ⟨1, [], 0⟩).N (ψ (αL.getD q.1 0))
          (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0)) :
    nonPrincOK n M P δL Bc Dc αL cL bL Lm = true := by
  have hnil : nullBasis (kerCols n M δL Bc Dc αL cL bL αL.length) = [] := by
    by_contra hne
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨t, ht, h1⟩ := nullBasis_pivot _ w hw
    obtain ⟨G, hG⟩ := princWit_of_rel n M δL Bc Dc αL cL bL w (nullBasis_sound _ w hw) t ht
      (by rw [h1]; exact one_ne_zero) hside
    exact hnot (princTest_of_certN ψ n M δL Bc Dc αL cL bL G hG rfl Y hY)
  simp only [nonPrincOK, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff]
  exact Or.inr ⟨hside, hnil⟩

end Complete

end Curves
