import RischTragerBronstein.Curves.ProcRFSem1

/-!
# The linear system: rows versus `lcomb`

`lcombS_cols`: if every row is satisfied by `cs` (over an extension), then `lcombS ι cs cols` is
the right-hand side (so `linSolve` answers, `linSolve_complete_map`). `rows_of_lcomb`: conversely
a solution satisfies every row.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Rows

variable {F : Type*} [Field F] [DecidableEq F] {S : Type*} [Field S]

/-- The columns of a list of rows. -/
def colsOf (nb : ℕ) (rows : List (List F × F)) : List (CPoly F) :=
  (List.range nb).map fun b ↦ rows.map fun r ↦ r.1.getD b 0

lemma coeff_lcombS (ι : F →+* S) (m : ℕ) : ∀ (cs : List S) (vs : List (CPoly F)),
    (lcombS ι cs vs).coeff m = (List.zipWith (fun c v ↦ c * ι (v.getD m 0)) cs vs).sum
  | [], _ => by simp [lcombS]
  | _ :: _, [] => by simp [lcombS]
  | c :: cs, v :: vs => by
    have := coeff_lcombS ι m cs vs
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul, coeff_map,
      coeff_toPoly] at this ⊢
    rw [this]

lemma sum_zipWith_cols (ι : F →+* S) (nb : ℕ) (cs : List S) (hcs : cs.length = nb)
    (rows : List (List F × F)) (m : ℕ) :
    (List.zipWith (fun c v ↦ c * ι (v.getD m 0)) cs (colsOf nb rows)).sum =
      ∑ b ∈ Finset.range nb, cs.getD b 0 * ι ((rows.getD m ([], 0)).1.getD b 0) := by
  subst hcs
  induction cs using List.reverseRecOn with
  | nil => simp [colsOf]
  | append_singleton cs c ih =>
    rw [colsOf, List.length_append, List.length_singleton, List.range_succ, List.map_append,
      List.zipWith_append (by simp), List.sum_append, Finset.sum_range_succ]
    rw [colsOf] at ih
    rw [ih]
    congr 1
    · refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hb)]
    · simp only [List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.sum_cons, List.sum_nil, add_zero]
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      congr 2
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases h : rows[m]? with
      | none => simp [List.getD_eq_getElem?_getD, h]
      | some r => simp [List.getD_eq_getElem?_getD, h]

/-- **Rows ⇒ `lcombS`.** -/
theorem lcombS_cols (ι : F →+* S) (nb : ℕ) (cs : List S) (hcs : cs.length = nb)
    (rows : List (List F × F))
    (h : ∀ r ∈ rows, ∑ b ∈ Finset.range nb, cs.getD b 0 * ι (r.1.getD b 0) = ι r.2) :
    lcombS ι cs (colsOf nb rows) = (toPoly (rows.map Prod.snd)).map ι := by
  ext m
  rw [coeff_lcombS, sum_zipWith_cols ι nb cs hcs, coeff_map, coeff_toPoly]
  by_cases hm : m < rows.length
  · have hr := h (rows[m]) (List.getElem_mem hm)
    rw [List.getD_eq_getElem _ _ hm, hr, List.getD_eq_getElem _ _ (by simpa using hm),
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (not_lt.mp hm), List.getD_eq_default _ _ (by simpa using hm),
      map_zero]
    exact Finset.sum_eq_zero fun b _ ↦ by simp

/-- **`lcomb` ⇒ rows.** -/
theorem rows_of_lcomb (nb : ℕ) (cs : List F) (hcs : cs.length = nb) (rows : List (List F × F))
    (h : lcomb cs (colsOf nb rows) = toPoly (rows.map Prod.snd)) :
    ∀ r ∈ rows, ∑ b ∈ Finset.range nb, cs.getD b 0 * r.1.getD b 0 = r.2 := by
  intro r hr
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr
  have h1 := congrArg (fun p ↦ p.coeff m) h
  have e : lcomb cs (colsOf nb rows) = lcombS (RingHom.id F) cs (colsOf nb rows) := by
    simp [lcomb, lcombS]
  rw [e, coeff_lcombS, sum_zipWith_cols (RingHom.id F) nb cs hcs, coeff_toPoly,
    List.getD_eq_getElem _ _ hm, List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map]
    at h1
  simpa using h1

end Rows

end Curves
