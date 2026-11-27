import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# A pigeonhole bound for the exponent of a quotient

`exists_nsmul_mem`: let `H` be a subgroup of an abelian group `G`, and suppose the complement of
`H` is split into `t` classes such that among any `r + 1` elements of one class two are *related*
(their difference or their sum lies in `H`). Then every `P` has a multiple `m • P ∈ H` with
`0 < m ≤ 2 (r t + 1)`.
-/

namespace ExH

theorem exists_nsmul_mem {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (t r : ℕ)
    (c : G → ℕ) (hc : ∀ g, c g < t)
    (hrel : ∀ Q : Fin (r + 1) → G, (∀ i, Q i ∉ H) → (∀ i j, c (Q i) = c (Q j)) →
      ∃ i j, i < j ∧ (Q j - Q i ∈ H ∨ Q j + Q i ∈ H)) (P : G) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2 * (r * t + 1) ∧ m • P ∈ H := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ m : ℕ, 0 < m → m ≤ 2 * (r * t + 1) → m • P ∉ H := hcon
  -- the multiples `1 … r t + 1` fall into `t` classes
  have hmaps : ∀ i ∈ Finset.Icc 1 (r * t + 1), c (i • P) ∈ Finset.range t :=
    fun i _ ↦ Finset.mem_range.mpr (hc _)
  have hcard : (Finset.range t).card * r < (Finset.Icc 1 (r * t + 1)).card := by
    rw [Finset.card_range, Nat.card_Icc]
    have : t * r = r * t := mul_comm _ _
    omega
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hy)
  have hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r * t + 1 ∧ c (i • P) = y := fun i hi ↦ by
    have := hSsub hi
    rw [Finset.mem_filter, Finset.mem_Icc] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  set f := S.orderEmbOfFin hScard with hf
  have hfS : ∀ i, f i ∈ S := fun i ↦ S.orderEmbOfFin_mem hScard i
  obtain ⟨i, j, hij, h⟩ := hrel (fun i ↦ f i • P)
    (fun i ↦ hall _ (hS _ (hfS i)).1 (by have := (hS _ (hfS i)).2.1; omega))
    (fun i j ↦ by rw [(hS _ (hfS i)).2.2, (hS _ (hfS j)).2.2])
  have hlt : f i < f j := f.strictMono hij
  have hi := hS _ (hfS i)
  have hj := hS _ (hfS j)
  rcases h with h | h
  · have e : (f j - f i) • P + f i • P = f j • P := by
      rw [← add_nsmul]; congr 1; omega
    rw [← e, add_sub_cancel_right] at h
    exact hall _ (by omega) (by omega) h
  · rw [← add_nsmul] at h
    exact hall _ (by omega) (by omega) h

end ExH
