import RischTragerBronstein.Torsion.TestCertN
import RischTragerBronstein.Computable.NullSpace

/-!
# Failed principality tests from an empty null space

`kerCols`: the columns of the principality test (over the coefficient field). If `nullBasis` finds
no relation among them, the test fails over every extension (**`not_princTest_of_nullN`**, via
`nullBasis_complete`). `nonPrincOK` accepts either this or a left-inverse certificate
(`nonPrincCheckN`); **`not_princTest_of_nonPrincOK`**.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Lin

variable {R S : Type*} [Field R] [DecidableEq R] [Field S] (ι : R →+* S)

lemma toPoly_unitLF (j : ℕ) : toPoly (unitL j : CPoly R) = X ^ j := by
  rw [unitL, toPoly_append]
  have : toPoly (List.replicate j (0 : R)) = 0 := by
    induction j with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  simp [this]

lemma lcombS_range_unitLF : ∀ (c : List S), lcombS ι c ((List.range c.length).map unitL) = toPoly c := by
  classical
  intro c
  induction c using List.reverseRecOn with
  | nil => simp [lcombS]
  | append_singleton c x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
      List.map_singleton, lcombS_append ι _ _ _ _ (by simp), ih, toPoly_append, toPoly_unitLF]
    simp

/-- **No relation found**: every relation (over any extension) is trivial. -/
theorem eq_zero_of_nullBasis_nil {vs : List (CPoly R)} (hnil : nullBasis vs = []) (cs : List S)
    (hl : cs.length = vs.length) (h0 : lcombS ι cs vs = 0) (j : ℕ) : cs.getD j 0 = 0 := by
  obtain ⟨β, hβ, h⟩ := nullBasis_complete ι vs cs hl h0
  rw [hnil, List.length_nil, List.length_eq_zero_iff] at hβ
  subst hβ
  have hs : (nsItems vs).map Prod.snd = (List.range cs.length).map unitL := by
    simp [nsItems, hl]
  rw [hs, lcombS_range_unitLF] at h
  have := congrArg (·.coeff j) h
  simpa [lcombS, coeff_toPoly] using this

lemma coeff_lcombS_zero (j : ℕ) : ∀ (β : List S) (ws : List (CPoly R)),
    (∀ w ∈ ws, w.getD j 0 = 0) → (lcombS ι β ws).coeff j = 0
  | [], _, _ => by simp [lcombS]
  | _ :: _, [], _ => by simp [lcombS]
  | b :: β, w :: ws, h => by
    have ih := coeff_lcombS_zero j β ws (fun w' hw' ↦ h w' (List.mem_cons_of_mem _ hw'))
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [coeff_add, ih, coeff_C_mul, coeff_map, coeff_toPoly, h w List.mem_cons_self, map_zero,
      mul_zero, add_zero]

/-- **Only zero relations found**: if every basis vector vanishes on the column indices, every
relation (over any extension) is trivial. -/
theorem eq_zero_of_nullBasis_zero {vs : List (CPoly R)}
    (hZ : ∀ w ∈ nullBasis vs, ∀ t < vs.length, w.getD t 0 = 0) (cs : List S)
    (hl : cs.length = vs.length) (h0 : lcombS ι cs vs = 0) (j : ℕ) : cs.getD j 0 = 0 := by
  by_cases hj : j < vs.length
  · obtain ⟨β, -, h⟩ := nullBasis_complete ι vs cs hl h0
    have hs : (nsItems vs).map Prod.snd = (List.range cs.length).map unitL := by
      simp [nsItems, hl]
    rw [hs, lcombS_range_unitLF] at h
    have := congrArg (·.coeff j) h
    simp only [coeff_toPoly] at this
    rw [this]
    exact coeff_lcombS_zero ι j β _ fun w hw ↦ hZ w hw j hj
  · exact List.getD_eq_default _ _ (by omega)

lemma lcombS_map_map {α : Type*} (f : α → S) (g : α → CPoly R) :
    ∀ l : List α, lcombS ι (l.map f) (l.map g) = (l.map fun a ↦ C (f a) * (toPoly (g a)).map ι).sum
  | [] => by simp [lcombS]
  | a :: l => by
    have ih := lcombS_map_map f g l
    simp only [lcombS] at ih
    simp [lcombS, ih]

end Lin

section Sums

variable {K : Type*} [AddCommMonoid K]

lemma sum_map_filter_ite {α : Type*} (p : α → Bool) (f : α → K) :
    ∀ l : List α, ((l.filter p).map f).sum = (l.map fun a ↦ if p a then f a else 0).sum
  | [] => rfl
  | a :: l => by
    have ih := sum_map_filter_ite p f l
    by_cases h : p a <;> simp [h, ih]

lemma sum_flatMapL {α β : Type*} (f : α → List β) (g : β → K) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a ↦ ((f a).map g).sum).sum
  | [] => by simp
  | a :: l => by simp [List.flatMap_cons, sum_flatMapL f g l]

lemma sum_range_list (f : ℕ → K) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The sum over the admissible columns `(i, d)`, `d + δᵢ ≤ M`. -/
lemma sum_cols (n M : ℕ) (δL : List ℕ) (h : ℕ → ℕ → K) :
    (((List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
      decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d)).map fun id ↦ h id.1 id.2).sum =
      ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (M + 1),
        if d + δL.getD i 0 ≤ M then h i d else 0 := by
  rw [sum_flatMapL, ← sum_range_list]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  rw [List.map_map, ← sum_range_list, sum_map_filter_ite]
  simp [Function.comp_def]

end Sums

section Spec

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]
variable (ψ : F →+* K) (n M : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F)
  (cL : List (BranchCert F)) (bL : List (List ℕ))

/-- The columns of the test, as `testKernel` builds them. -/
def kerCols (m : ℕ) : List (List F) :=
  let cols := (List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
    decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d)
  let rows := (List.range m).flatMap fun j ↦ (List.range n).flatMap fun k ↦
    (List.range (rowsN Dc αL cL bL j k)).map fun t ↦ (j, k, t)
  cols.map fun id ↦ rows.map fun jkt ↦ testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2

/-- **A test without non-zero kernel vector fails** (over every extension `K`). -/
theorem not_princTest_of_nullZ
    (hZ : ∀ w ∈ nullBasis (kerCols n M δL Bc Dc αL cL bL αL.length),
      ∀ t < (kerCols n M δL Bc Dc αL cL bL αL.length).length, w.getD t 0 = 0)
    (hside : testSideN n Dc αL cL bL = true) (Y : Fin αL.length → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin αL.length) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M (fun q : Fin αL.length × Fin n ↦ (cL.getD q.1 ⟨1, [], 0⟩).N)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) (cL.getD q.1 ⟨1, [], 0⟩).N (ψ (αL.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) := by
  classical
  rintro ⟨cc, hc0, hdeg, hlb⟩
  apply hc0
  have hdeg' : ∀ i, (cc i).natDegree ≤ M := fun i ↦ by
    by_cases h : cc i = 0
    · rw [h, natDegree_zero]; exact Nat.zero_le _
    · have := hdeg i h; simp only at this; omega
  have hvan : ∀ (i : Fin n) (d : ℕ), M < d + δL.getD i 0 → (cc i).coeff d = 0 := fun i d hd ↦ by
    by_cases h : cc i = 0
    · rw [h, Polynomial.coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by have := hdeg i h; simp only at this; omega)
  set cN : ℕ → ℕ → K := fun i d ↦ if h : i < n then (cc ⟨i, h⟩).coeff d else 0 with hcN
  have hcNv : ∀ i d, M < d + δL.getD i 0 → cN i d = 0 := fun i d hd ↦ by
    simp only [hcN]; split_ifs with h
    · exact hvan _ d hd
    · rfl
  -- the rows
  have hrow : ∀ j < αL.length, ∀ k < n, ∀ t < rowsN Dc αL cL bL j k,
      ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (M + 1),
        ψ (testEntryN Bc Dc αL cL j k t i d) * cN i d = 0 := by
    intro j hj k hk t ht
    have h1 := hlb (⟨j, hj⟩, ⟨k, hk⟩) ((t : ℤ) - muAtN Dc αL cL j)
      (by simp only [rowsN] at ht ⊢; omega)
    rw [test_rowsN ψ n M Bc Dc αL cL bL Y hside hY cc hdeg' ⟨j, hj⟩ ⟨k, hk⟩ t ht] at h1
    rw [← h1, ← Fin.sum_univ_eq_sum_range (fun i ↦ ∑ d ∈ Finset.range (M + 1),
      ψ (testEntryN Bc Dc αL cL j k t i d) * cN i d)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [hcN, dif_pos i.2, Fin.eta]
    ring
  -- the relation among the columns
  set cols := (List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
    decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d) with hcols
  set rows := (List.range αL.length).flatMap fun j ↦ (List.range n).flatMap fun k ↦
    (List.range (rowsN Dc αL cL bL j k)).map fun t ↦ (j, k, t) with hrows
  have hkc : kerCols n M δL Bc Dc αL cL bL αL.length =
      cols.map fun id ↦ rows.map fun jkt ↦ testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2 :=
    rfl
  set cs : List K := cols.map fun id ↦ cN id.1 id.2 with hcs
  have h0 : lcombS ψ cs (kerCols n M δL Bc Dc αL cL bL αL.length) = 0 := by
    rw [hkc, hcs, lcombS_map_map]
    ext r
    rw [← Polynomial.lcoeff_apply, map_list_sum, List.map_map, Polynomial.coeff_zero]
    have hterm : ∀ id : ℕ × ℕ, (lcoeff K r) (C (cN id.1 id.2) * (toPoly (rows.map fun jkt ↦
        testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2)).map ψ) =
        cN id.1 id.2 * ψ ((rows.map fun jkt ↦
          testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2).getD r 0) := by
      intro id
      rw [lcoeff_apply, coeff_C_mul, coeff_map, coeff_toPoly]
    simp only [Function.comp_def, hterm]
    by_cases hr : r < rows.length
    · have hmem : rows[r] ∈ rows := List.getElem_mem hr
      rcases hE : rows[r] with ⟨j, k, t⟩
      rw [hE] at hmem
      simp only [hrows, List.mem_flatMap, List.mem_range, List.mem_map] at hmem
      obtain ⟨j', hj, k', hk, t', ht, he⟩ := hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hg : ∀ id : ℕ × ℕ, (rows.map fun jkt ↦
          testEntryN Bc Dc αL cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2).getD r 0 =
          testEntryN Bc Dc αL cL j' k' t' id.1 id.2 := by
        intro id
        rw [List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_map, hE]
      simp only [hg]
      rw [sum_cols n M δL (fun i d ↦ cN i d * ψ (testEntryN Bc Dc αL cL j' k' t' i d))]
      refine Eq.trans ?_ (hrow j' hj k' hk t' ht)
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
      split_ifs with hv
      · ring
      · rw [hcNv i d (by omega), mul_zero]
    · refine List.sum_eq_zero fun x hx ↦ ?_
      obtain ⟨id, -, rfl⟩ := List.mem_map.mp hx
      rw [List.getD_eq_default _ _ (by simpa using hr), map_zero, mul_zero]
  have hz := eq_zero_of_nullBasis_zero ψ hZ cs (by simp [hcs, hkc]) h0
  -- every admissible coefficient vanishes
  have hall : ∀ i < n, ∀ d ≤ M, d + δL.getD i 0 ≤ M → cN i d = 0 := by
    intro i hi d hd hv
    have hmem : (i, d) ∈ cols := by
      simp only [hcols, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
        decide_eq_true_eq]
      exact ⟨i, hi, d, ⟨by omega, hv⟩, rfl⟩
    obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem
    have := hz idx
    rwa [hcs, List.getD_eq_getElem _ _ (by simpa using hidx), List.getElem_map, hget] at this
  funext i
  ext d
  rw [Pi.zero_apply, Polynomial.coeff_zero]
  by_cases hv : d + δL.getD i 0 ≤ M
  · have := hall i i.2 d (by omega) hv
    simpa [hcN] using this
  · exact hvan i d (by omega)

/-- **A test without kernel vector fails** (over every extension `K`). -/
theorem not_princTest_of_nullN (hnull : nullBasis (kerCols n M δL Bc Dc αL cL bL αL.length) = [])
    (hside : testSideN n Dc αL cL bL = true) (Y : Fin αL.length → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin αL.length) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M (fun q : Fin αL.length × Fin n ↦ (cL.getD q.1 ⟨1, [], 0⟩).N)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) (cL.getD q.1 ⟨1, [], 0⟩).N (ψ (αL.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) :=
  not_princTest_of_nullZ ψ n M δL Bc Dc αL cL bL (by rw [hnull]; simp) hside Y hY

/-- The same, with the points indexed by `Fin m`. -/
theorem not_princTest_of_nullZ' {m : ℕ} (hm : αL.length = m)
    (hZ : ∀ w ∈ nullBasis (kerCols n M δL Bc Dc αL cL bL m),
      ∀ t < (kerCols n M δL Bc Dc αL cL bL m).length, w.getD t 0 = 0)
    (hside : testSideN n Dc αL cL bL = true) (Y : Fin m → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin m) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M (fun q : Fin m × Fin n ↦ (cL.getD q.1 ⟨1, [], 0⟩).N)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) (cL.getD q.1 ⟨1, [], 0⟩).N (ψ (αL.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) := by
  subst hm
  exact not_princTest_of_nullZ ψ n M δL Bc Dc αL cL bL hZ hside Y hY

theorem not_princTest_of_nullN' {m : ℕ} (hm : αL.length = m)
    (hnull : nullBasis (kerCols n M δL Bc Dc αL cL bL m) = [])
    (hside : testSideN n Dc αL cL bL = true) (Y : Fin m → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin m) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M (fun q : Fin m × Fin n ↦ (cL.getD q.1 ⟨1, [], 0⟩).N)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) (cL.getD q.1 ⟨1, [], 0⟩).N (ψ (αL.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) := by
  subst hm
  exact not_princTest_of_nullN ψ n M δL Bc Dc αL cL bL hnull hside Y hY

end Spec

section OK

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The failed-test certificate**: a left inverse (`nonPrincCheckN`) or an empty null space of
the test columns (recomputed). -/
def nonPrincOK (n M P : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F)
    (cL : List (BranchCert F)) (bL : List (List ℕ)) (Lm : List (List F)) : Bool :=
  nonPrincCheckN n M P δL Bc Dc αL cL bL Lm ||
    (testSideN n Dc αL cL bL && (nullBasis (kerCols n M δL Bc Dc αL cL bL αL.length)).isEmpty)

variable {K : Type*} [Field K]

/-- **A failed test** from `nonPrincOK`. -/
theorem not_princTest_of_nonPrincOK (ψ : F →+* K) (n M P : ℕ) (δL : List ℕ)
    (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F) (cL : List (BranchCert F))
    (bL : List (List ℕ)) (Lm : List (List F))
    (hchk : nonPrincOK n M P δL Bc Dc αL cL bL Lm = true) {m : ℕ} (hm : αL.length = m)
    (Y : Fin m → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin m) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M (fun q : Fin m × Fin n ↦ (cL.getD q.1 ⟨1, [], 0⟩).N)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) (cL.getD q.1 ⟨1, [], 0⟩).N (ψ (αL.getD q.1 0))
          (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) := by
  simp only [nonPrincOK, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hchk
  subst hm
  rcases hchk with h | ⟨hside, hnull⟩
  · exact not_princTest_of_certN ψ n M δL Bc Dc αL cL bL Y P Lm h hY
  · exact not_princTest_of_nullN ψ n M δL Bc Dc αL cL bL hnull hside Y hY

end OK

end Curves
