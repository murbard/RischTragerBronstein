import RischTragerBronstein.Torsion.AutoPrime
import RischTragerBronstein.Torsion.NullTest

/-!
# The kernel search for the multiplier `m_p`: soundness and completeness

`placeWit` returns a non-zero relation among the columns of the principality test at `m Γ`
modulo `p` (from `nullBasis`).

* **`placeWit_spec`**: its output always passes `princWitCheckN` (so `autoPlaceData` only returns
  data accepted by `primeCheck`, as far as the witness is concerned);
* **`placeWit_isSome`**: if the side conditions hold at `m` (enough precision) and the test passes
  over some extension (`princTest`), the search finds a witness (via `nullBasis_complete`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Lists

variable {R : Type*} [Field R]

lemma getD_grid {α : Type*} [Zero α] (f : ℕ → ℕ → α) {n M i d : ℕ} (hi : i < n) (hd : d < M + 1) :
    (((List.range n).map fun i ↦ (List.range (M + 1)).map fun d ↦ f i d).getD i []).getD d 0 =
      f i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range, hi, hd]

/-- A coefficient of `∑ wᵢ vᵢ`. -/
lemma coeff_lcomb (r : ℕ) : ∀ (vs : List (CPoly R)) (w : List R),
    (lcomb w vs).coeff r = ∑ c ∈ Finset.range vs.length, w.getD c 0 * (vs.getD c []).getD r 0
  | [], w => by cases w <;> simp [lcomb]
  | v :: vs, [] => by simp [lcomb]
  | v :: vs, a :: w => by
    have ih := coeff_lcomb r vs w
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [coeff_add, ih, coeff_C_mul, coeff_toPoly, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma sum_map_getD {α M : Type*} [AddCommMonoid M] (h : α → M) (d0 : α) :
    ∀ l : List α, (l.map h).sum = ∑ c ∈ Finset.range l.length, h (l.getD c d0)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_getD h d0 l, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

lemma cols_nodup (n M : ℕ) (δL : List ℕ) :
    ((List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
      decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun i _ ↦ (List.nodup_range.filter _).map fun a b h ↦ (Prod.mk.inj h).2, ?_⟩
  refine List.Pairwise.imp (fun {a b} hab ↦ ?_) List.nodup_range
  intro x hx1 hx2
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hx1
  obtain ⟨d', -, h⟩ := List.mem_map.mp hx2
  exact hab (Prod.mk.inj h).1.symm

lemma findIdx?_nodup {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) {c : ℕ}
    (hc : c < l.length) : l.findIdx? (· = l[c]) = some c := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hc, by simp, fun j hj h ↦ ?_⟩
  have := (hl.getElem_inj_iff).mp (of_decide_eq_true h)
  omega

end Lists

section Spec

variable {p : ℕ} [Fact p.Prime]

/-- **The witness found by the kernel search passes the check.** -/
theorem placeWit_spec {n : ℕ} {δL : List ℕ} {Bp : List (BPoly (ZMod p))} {Dp : CPoly (ZMod p)}
    {Pc : PlaceCert (ZMod p)} {m : ℕ} {G : List (List (ZMod p))}
    (h : placeWit n δL Bp Dp Pc m = some G) :
    princWitCheckN n (m * Pc.cΓ) δL Bp Dp Pc.αs (Pc.fcerts n) (Pc.bL n m) G = true := by
  classical
  unfold placeWit at h
  simp only at h
  split_ifs at h with hs
  set M := m * Pc.cΓ with hM
  set cL := Pc.fcerts n
  set bL := Pc.bL n m
  set cols := (List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
    decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d) with hcols
  set rows := (List.range Pc.fib.length).flatMap fun j ↦ (List.range n).flatMap fun k ↦
    (List.range (rowsN Dp Pc.αs cL bL j k)).map fun t ↦ (j, k, t) with hrows
  set kc := cols.map fun id ↦ rows.map fun jkt ↦
    testEntryN Bp Dp Pc.αs cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2 with hkc
  have hside : testSideN n Dp Pc.αs cL bL = true := by simpa using hs
  obtain ⟨w, hw, hGw⟩ := Option.map_eq_some_iff.mp h
  have hwmem : w ∈ nullBasis kc := List.mem_of_find?_eq_some hw
  have hwnz := List.find?_some hw
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq] at hwnz
  obtain ⟨t0, ht0, hwt0⟩ := hwnz
  have hrel : lcomb w kc = 0 := nullBasis_sound kc w hwmem
  have hnd := cols_nodup n M δL
  have hkcl : kc.length = cols.length := by simp [hkc]
  -- membership in the columns
  have hmemc : ∀ i d, (i, d) ∈ cols → i < n ∧ d < M + 1 ∧ d + δL.getD i 0 ≤ M := by
    intro i d hid
    simp only [hcols, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hid
    obtain ⟨i', hi', d', ⟨hd', hv⟩, he⟩ := hid
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨hi', hd', hv⟩
  -- the entries of the witness
  have hG : ∀ c (hc : c < cols.length),
      (G.getD cols[c].1 []).getD cols[c].2 0 = w.getD c 0 := by
    intro c hc
    obtain ⟨hi, hd, -⟩ := hmemc cols[c].1 cols[c].2 (by simpa using List.getElem_mem hc)
    rw [← hGw]
    beta_reduce
    rw [getD_grid _ hi hd]
    have := findIdx?_nodup hnd hc
    simp only [Prod.mk.eta] at this ⊢
    rw [this]
  simp only [princWitCheckN, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨hside, ?_⟩, ?_⟩
  · -- a non-zero coefficient
    have hc : t0 < cols.length := by rw [← hkcl]; exact ht0
    obtain ⟨hi, hd, hv⟩ := hmemc cols[t0].1 cols[t0].2 (by simpa using List.getElem_mem hc)
    exact ⟨cols[t0].1, hi, cols[t0].2, hd, hv, by rw [hG t0 hc]; exact hwt0⟩
  · -- every row vanishes
    intro j hj k hk t ht
    have hmem : (j, k, t) ∈ rows := by
      simp only [hrows, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨j, ?_, k, hk, t, ht, rfl⟩
      simpa [PlaceCert.αs] using hj
    obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hmem
    have hco := congrArg (·.coeff r) hrel
    simp only [coeff_lcomb, Polynomial.coeff_zero] at hco
    rw [hkcl] at hco
    have e1 := sum_cols n M δL (fun i d ↦ (G.getD i []).getD d 0 * testEntryN Bp Dp Pc.αs cL j k t i d)
    rw [sum_map_getD _ (0, 0)] at e1
    have e2 : ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (M + 1),
        (if d + δL.getD i 0 ≤ M then (G.getD i []).getD d 0 else 0) *
          testEntryN Bp Dp Pc.αs cL j k t i d =
        ∑ i ∈ Finset.range n, ∑ d ∈ Finset.range (M + 1),
          if d + δL.getD i 0 ≤ M then (G.getD i []).getD d 0 *
            testEntryN Bp Dp Pc.αs cL j k t i d else 0 :=
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun d _ ↦ by split_ifs <;> simp
    rw [e2, ← e1]
    refine Eq.trans (Finset.sum_congr rfl fun c hc ↦ ?_) hco
    have hc' : c < cols.length := Finset.mem_range.mp hc
    rw [List.getD_eq_getElem (l := cols) _ hc', hG c hc',
      List.getD_eq_getElem (l := kc) _ (by rw [hkcl]; exact hc'), List.getElem_map,
      List.getD_eq_getElem (l := List.map _ rows) _ (by simpa using hr), List.getElem_map, hget]

/-- **The kernel search finds a witness when the test passes** (with enough precision). -/
theorem placeWit_isSome {K : Type*} [Field K] (ψ : ZMod p →+* K) {n : ℕ} {δL : List ℕ}
    {Bp : List (BPoly (ZMod p))} {Dp : CPoly (ZMod p)} {Pc : PlaceCert (ZMod p)} {m : ℕ}
    (hside : testSideN n Dp Pc.αs (Pc.fcerts n) (Pc.bL n m) = true) {mf : ℕ}
    (hmf : Pc.fib.length = mf) (Y : Fin mf → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin mf) (k : Fin n),
      (PowerSeries.X : PowerSeries K) ^ ((Pc.fcerts n).getD j ⟨1, [], 0⟩).prec ∣
        Y j k - thetaT ψ (toPoly ((((Pc.fcerts n).getD j ⟨1, [], 0⟩).ys).getD k [])))
    (htest : princTest (fun i : Fin n ↦ δL.getD i 0) (m * Pc.cΓ)
      (fun q : Fin mf × Fin n ↦ ((Pc.fcerts n).getD q.1 ⟨1, [], 0⟩).N)
      (fun q ↦ ψ (Pc.αs.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bp.getD i [])).map (mapRingHom ψ))
        ((toPoly Dp).map ψ) ((Pc.fcerts n).getD q.1 ⟨1, [], 0⟩).N (ψ (Pc.αs.getD q.1 0))
        (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ ((Pc.bL n m).getD q.1 []).getD q.2 0)) :
    (placeWit n δL Bp Dp Pc m).isSome := by
  classical
  subst hmf
  unfold placeWit
  simp only [hside, Bool.not_true, Bool.false_eq_true, ite_false, Option.isSome_map]
  rw [Option.isSome_iff_ne_none]
  intro hnone
  refine not_princTest_of_nullZ' ψ n (m * Pc.cΓ) δL Bp Dp Pc.αs (Pc.fcerts n) (Pc.bL n m)
    (by simp [PlaceCert.αs]) ?_ hside Y hY htest
  intro w hw t ht
  have := List.find?_eq_none.mp hnone w hw
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq, not_exists, not_and,
    not_not] at this
  exact this t (by simpa [kerCols] using ht)

end Spec

end Curves
