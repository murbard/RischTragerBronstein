import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# `p`-adic divisibility of rationals

`PDvd p k q`: `q ∈ p^k ℤ_(p)`, i.e. `q = 0` or `k ≤ v_p(q)`. Closed under sums, negation;
multiplicative in `k`; integers are in `PDvd p 0`; `1 + u` with `PDvd p 1 u` is a `p`-adic unit.
-/

namespace PVal

variable {p : ℕ} [hp : Fact p.Prime]

/-- `q ∈ p^k ℤ_(p)`. -/
def PDvd (p : ℕ) (k : ℤ) (q : ℚ) : Prop := q = 0 ∨ k ≤ padicValRat p q

lemma pdvd_zero (k : ℤ) : PDvd p k 0 := Or.inl rfl

lemma pdvd_of_ne {k : ℤ} {q : ℚ} (h : PDvd p k q) (hq : q ≠ 0) : k ≤ padicValRat p q :=
  h.resolve_left hq

lemma PDvd.mono {k k' : ℤ} {q : ℚ} (h : PDvd p k q) (hk : k' ≤ k) : PDvd p k' q :=
  h.imp id fun h ↦ hk.trans h

lemma PDvd.neg {k : ℤ} {q : ℚ} (h : PDvd p k q) : PDvd p k (-q) := by
  rcases h with rfl | h
  · simp [pdvd_zero]
  · right; rwa [padicValRat.neg]

lemma PDvd.add {k : ℤ} {q r : ℚ} (hq : PDvd p k q) (hr : PDvd p k r) : PDvd p k (q + r) := by
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · rw [add_zero]; exact Or.inr hq
  right
  exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add hqr)

lemma PDvd.sub {k : ℤ} {q r : ℚ} (hq : PDvd p k q) (hr : PDvd p k r) : PDvd p k (q - r) := by
  rw [sub_eq_add_neg]; exact hq.add hr.neg

lemma PDvd.mul {k l : ℤ} {q r : ℚ} (hq : PDvd p k q) (hr : PDvd p l r) :
    PDvd p (k + l) (q * r) := by
  rcases hq with rfl | hq
  · simp [pdvd_zero]
  rcases hr with rfl | hr
  · simp [pdvd_zero]
  by_cases h0 : q = 0
  · simp [h0, pdvd_zero]
  by_cases h1 : r = 0
  · simp [h1, pdvd_zero]
  right
  rw [padicValRat.mul h0 h1]
  omega

lemma pdvd_intCast (z : ℤ) : PDvd p 0 (z : ℚ) := by
  by_cases hz : (z : ℚ) = 0
  · exact Or.inl hz
  right
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le _

lemma pdvd_natCast (n : ℕ) : PDvd p 0 (n : ℚ) := by
  exact_mod_cast pdvd_intCast (p := p) (n : ℤ)

lemma pdvd_one : PDvd p 0 (1 : ℚ) := by exact_mod_cast pdvd_natCast (p := p) 1

lemma PDvd.pow {k : ℤ} {q : ℚ} (h : PDvd p k q) (n : ℕ) : PDvd p (n * k) (q ^ n) := by
  induction n with
  | zero => simpa using pdvd_one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul h
    convert this using 1
    push_cast; ring

/-- `1 + u` is a unit when `u ∈ p ℤ_(p)`. -/
lemma val_one_add {u : ℚ} (hu : PDvd p 1 u) : padicValRat p (1 + u) = 0 ∧ 1 + u ≠ 0 := by
  rcases hu with rfl | hu
  · simp
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : u = -1 := by linear_combination h
    rw [this, padicValRat.neg, padicValRat.one] at hu
    omega
  refine ⟨?_, h1u⟩
  rw [padicValRat.add_eq_of_lt h1u one_ne_zero hu0 (by rw [padicValRat.one]; omega)]
  exact padicValRat.one

/-- Division by a unit. -/
lemma PDvd.div_unit {k : ℤ} {q w : ℚ} (h : PDvd p k q) (hw : padicValRat p w = 0)
    (hw0 : w ≠ 0) : PDvd p k (q / w) := by
  rcases h with rfl | h
  · simp [pdvd_zero]
  by_cases hq : q = 0
  · simp [hq, pdvd_zero]
  right
  rw [padicValRat.div hq hw0, hw]
  omega

/-- A value `v` with `PDvd p k v`, `k > v_p(q)` cannot equal `q ≠ 0`. -/
lemma not_pdvd_of_lt {k : ℤ} {q : ℚ} (hq : q ≠ 0) (hk : padicValRat p q < k) : ¬PDvd p k q := by
  rintro (h | h)
  · exact hq h
  · omega

end PVal
