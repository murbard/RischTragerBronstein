import RischTragerBronstein.Torsion.NullTest

/-!
# Linear descent

**`exists_kernel_of_ext`**: a homogeneous linear system with coefficients in `F` that has a
non-zero solution over an extension `ψ : F → K` has a non-zero solution over `F` (from
`nullBasis_complete`). This is how functions with prescribed orders, found over a large constant
field, are brought down to the number field of the certificates.
-/

open Polynomial

namespace Curves

open CPoly

section Descent

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K] (ψ : F →+* K)

/-- The columns of a system given by rows. -/
def colsOfRows (rows : List (List F)) (nb : ℕ) : List (CPoly F) :=
  (List.range nb).map fun b ↦ rows.map fun row ↦ row.getD b 0

/-- A coefficient of `∑ cᵢ vᵢ`. -/
lemma coeff_lcombS_gen (r : ℕ) : ∀ (vs : List (CPoly F)) (c : List K),
    (lcombS ψ c vs).coeff r = ∑ b ∈ Finset.range vs.length, c.getD b 0 * ψ ((vs.getD b []).getD r 0)
  | [], c => by cases c <;> simp [lcombS]
  | v :: vs, [] => by simp [lcombS]
  | v :: vs, x :: c => by
    have ih := coeff_lcombS_gen r vs c
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [coeff_add, ih, coeff_C_mul, coeff_map, coeff_toPoly, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

lemma lcomb_eq_lcombS (c : List F) (vs : List (CPoly F)) : lcomb c vs = lcombS (RingHom.id F) c vs := by
  simp [lcomb, lcombS]

lemma cols_getD (rows : List (List F)) (nb b r : ℕ) (hb : b < nb) (hr : r < rows.length) :
    ((colsOfRows rows nb).getD b []).getD r 0 = (rows.getD r []).getD b 0 := by
  simp [colsOfRows, List.getD_eq_getElem?_getD, List.getElem?_range hb, hr]

/-- **Linear descent.** -/
theorem exists_kernel_of_ext (rows : List (List F)) (nb : ℕ) (c : ℕ → K)
    (hc : ∃ b < nb, c b ≠ 0)
    (h : ∀ row ∈ rows, ∑ b ∈ Finset.range nb, c b * ψ (row.getD b 0) = 0) :
    ∃ d : ℕ → F, (∃ b < nb, d b ≠ 0) ∧
      ∀ row ∈ rows, ∑ b ∈ Finset.range nb, d b * row.getD b 0 = 0 := by
  classical
  set vs := colsOfRows rows nb with hvs
  have hvl : vs.length = nb := by simp [hvs, colsOfRows]
  -- the relation over `K`
  set cs : List K := (List.range nb).map c with hcs
  have hcsl : cs.length = vs.length := by simp [hcs, hvl]
  have hrel : lcombS ψ cs vs = 0 := by
    ext r
    rw [Polynomial.coeff_zero, coeff_lcombS_gen, hvl]
    by_cases hr : r < rows.length
    · have := h (rows.getD r []) (by rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem _)
      rw [← this]
      refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [hvs, cols_getD rows nb b r (Finset.mem_range.mp hb) hr, hcs]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (Finset.mem_range.mp hb)]
    · refine Finset.sum_eq_zero fun b hb ↦ ?_
      have : ((vs.getD b []).getD r 0) = 0 := by
        simp [hvs, colsOfRows, List.getD_eq_getElem?_getD,
          List.getElem?_range (Finset.mem_range.mp hb), List.getElem?_eq_none (by omega : rows.length ≤ r)]
      rw [this, map_zero, mul_zero]
  -- a basis vector with a non-zero coordinate
  by_contra hno
  push Not at hno
  have hZ : ∀ w ∈ nullBasis vs, ∀ t < vs.length, w.getD t 0 = 0 := by
    intro w hw t ht
    by_contra hwt
    have hw0 : lcomb w vs = 0 := nullBasis_sound vs w hw
    obtain ⟨b, hb, hbne⟩ : ∃ b < nb, (fun b ↦ w.getD b 0) b ≠ 0 := ⟨t, by omega, hwt⟩
    obtain ⟨row, hrow, hne⟩ := hno (fun b ↦ w.getD b 0) ⟨b, hb, hbne⟩
    apply hne
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hrow
    have := congrArg (·.coeff r) hw0
    simp only [Polynomial.coeff_zero] at this
    rw [lcomb_eq_lcombS, coeff_lcombS_gen, hvl] at this
    refine Eq.trans (Finset.sum_congr rfl fun b' hb' ↦ ?_) this
    rw [hvs, cols_getD rows nb b' r (Finset.mem_range.mp hb') hr, RingHom.id_apply]
    simp [List.getD_eq_getElem?_getD, hr]
  obtain ⟨b, hb, hcb⟩ := hc
  have := eq_zero_of_nullBasis_zero ψ hZ cs hcsl hrel b
  simp [hcs, List.getD_eq_getElem?_getD, List.getElem?_range hb] at this
  exact hcb this

end Descent

end Curves
