import RischTragerBronstein.Mixed.SysRoot

/-!
# A complete bound on the natural roots of a polynomial over `Fₘ`

`intRootBound2`: the `ℚ`-coordinates (`MCols`) turn `∑ eʲ cⱼ = 0` into rational equations
`∑ eʲ colⱼ[k] = 0`, one per coordinate `k`; the first non-zero one bounds the natural roots
(`intRootBound2_spec`). It answers as soon as some `cⱼ ≠ 0` (`intRootBound2_isSome`): a code
whose coordinates all vanish has value `0` (`MCols_spec`).
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys

/-- The rational polynomial of the coordinate `k`. -/
def coordPoly (cols : List (CPoly ℚ)) (L k : ℕ) : CPoly ℚ :=
  (List.range L).map fun j ↦ (cols.getD j []).getD k 0

/-- **The natural-root bound** (`none` iff all coordinates vanish). -/
def intRootBound2 (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (vs : List (LC m)) :
    Option ℕ :=
  let cols := MCols Fc ks m vs
  let K := (cols.map List.length).foldr max 0
  match (List.range K).find? (fun k ↦ (coordPoly cols vs.length k).any (· != 0)) with
  | some k => let w := coordPoly cols vs.length k; some (maxRootLE w ⌈rootBoundL w⌉₊)
  | none => none

lemma le_root_bound (w : CPoly ℚ) (hw : toPoly w ≠ 0) (e : ℕ) (hr : (toPoly w).eval (e : ℚ) = 0) :
    e ≤ maxRootLE w ⌈rootBoundL w⌉₊ := by
  have hb := abs_le_rootBound (toPoly w) hw _ hr
  rw [← rootBoundL_eq _ hw, abs_of_nonneg (by positivity)] at hb
  exact le_maxRootLE _ _ e (by exact_mod_cast hb.trans (Nat.le_ceil _)) hr

lemma le_foldr_max_nat {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

lemma toPoly_ne_zero_of_any {w : CPoly ℚ} (h : w.any (· != 0) = true) : toPoly w ≠ 0 := by
  simp only [List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨x, hx, hx0⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  intro h0
  apply hx0
  have := congrArg (fun Q : ℚ[X] ↦ Q.coeff j) h0
  simp only [coeff_toPoly, coeff_zero] at this
  rwa [List.getD_eq_getElem _ _ hj] at this

lemma eval_coordPoly (cols : List (CPoly ℚ)) (L k : ℕ) (x : ℚ) :
    (toPoly (coordPoly cols L k)).eval x =
      ∑ j ∈ Finset.range L, (cols.getD j []).getD k 0 * x ^ j := by
  have hlen : (coordPoly cols L k).length = L := by simp [coordPoly]
  rw [eval_eq_sum_range' (n := L + 1), Finset.sum_range_succ, coeff_toPoly,
    List.getD_eq_default _ _ (by omega), zero_mul, add_zero]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [coeff_toPoly, coordPoly, Tower.NestP.NestTower.getD_range_map _ _ (Finset.mem_range.mp hj)]
  · rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_toPoly, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hi.le)]

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Every natural root is bounded.** -/
theorem intRootBound2_spec (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (B : ℕ)
    (hB : intRootBound2 Fc ks m vs = some B) (e : ℕ)
    (he : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fun j ↦ algebraMap ℚ Cc ((e : ℚ) ^ j)) vs).sum = 0) :
    e ≤ B := by
  unfold intRootBound2 at hB
  dsimp only at hB
  split at hB
  swap
  · exact absurd hB (by simp)
  rename_i k hk
  obtain rfl := Option.some.inj hB
  have hany := List.find?_some hk
  set cols := MCols Fc ks m vs with hcols
  have hz := (T.MCols_spec m h vs _ (by simp)).mp he
  have hc := congrArg (fun Q : Cc[X] ↦ Q.coeff k) hz
  simp only [coeff_zero] at hc
  rw [Tower.NestP.NestTower.coeff_lcombS] at hc
  refine le_root_bound _ (toPoly_ne_zero_of_any hany) e ?_
  rw [eval_coordPoly]
  apply (algebraMap ℚ Cc).injective
  rw [map_zero, ← hc, map_sum,
    Tower.NestP.zipWith_sum_getD (fun (b : Cc) (w : CPoly ℚ) ↦ b * algebraMap ℚ Cc (w.getD k 0)) 0 []
      (fun w ↦ by simp)]
  have hl : cols.length = vs.length := length_MCols Fc ks m vs
  rw [length_MCols]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Tower.NestP.NestTower.getD_range_map _ _ (Finset.mem_range.mp hj), map_mul, mul_comm]

/-- **The bound answers** as soon as some `cⱼ` is non-zero. -/
theorem intRootBound2_isSome (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (j : ℕ) (hj : j < vs.length)
    (hne : (T.MP m h).sem (vs.getD j (MO Fc ks m).zero) ≠ 0) :
    (intRootBound2 Fc ks m vs).isSome := by
  classical
  set cols := MCols Fc ks m vs with hcols
  have hl : cols.length = vs.length := length_MCols Fc ks m vs
  set K := (cols.map List.length).foldr max 0 with hK
  unfold intRootBound2
  dsimp only
  rw [← hcols, ← hK]
  rcases hf : (List.range K).find? (fun k ↦ (coordPoly cols vs.length k).any (· != 0)) with _ | k
  · exfalso
    have hall := List.find?_eq_none.mp hf
    -- every coordinate of `colⱼ` vanishes
    have hcol : ∀ k, (cols.getD j []).getD k 0 = 0 := by
      intro k
      by_cases hk : k < K
      · have := hall k (List.mem_range.mpr hk)
        simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and, not_not] at this
        have h2 := this ((coordPoly cols vs.length k).getD j 0) (by
          rw [List.getD_eq_getElem _ _ (by simp [coordPoly]; exact hj)]
          exact List.getElem_mem _)
        rwa [coordPoly, Tower.NestP.NestTower.getD_range_map _ _ hj] at h2
      · apply List.getD_eq_default
        have : (cols.getD j []).length ≤ K := by
          rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
          exact le_foldr_max_nat (List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩)
        omega
    have hP : toPoly (cols.getD j []) = 0 := Polynomial.ext fun k ↦ by
      rw [coeff_toPoly, hcol k, coeff_zero]
    set c : List Cc := (List.range vs.length).map fun i ↦ if i = j then (1 : Cc) else 0 with hc
    have hcl : c.length = vs.length := by simp [hc]
    have hgc : ∀ i < vs.length, c.getD i 0 = if i = j then 1 else 0 := fun i hi ↦ by
      rw [hc, Tower.NestP.NestTower.getD_range_map _ _ hi]
    have hlz : lcombS (algebraMap ℚ Cc) c cols = 0 := by
      unfold lcombS
      rw [sum_zipWith_range _ 0 [] c cols (by rw [hcl, hl]), hl]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [hgc i (Finset.mem_range.mp hi)]
      split_ifs with hij
      · subst hij; rw [hP, Polynomial.map_zero, mul_zero]
      · rw [map_zero, zero_mul]
    have hsem := (T.MCols_spec m h vs c hcl).mpr hlz
    rw [sum_zipWith_range _ 0 (MO Fc ks m).zero c vs hcl,
      Finset.sum_eq_single j (fun i hi hij ↦ by rw [hgc i (Finset.mem_range.mp hi), if_neg hij,
        map_zero, zero_mul]) (fun h' ↦ absurd (Finset.mem_range.mpr hj) h'),
      hgc j hj, if_pos rfl, map_one, one_mul] at hsem
    exact hne hsem
  · simp

end MTower

end Curves.MT
