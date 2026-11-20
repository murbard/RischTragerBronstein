import RischTragerBronstein.Curves.Abel

/-!
# Constants of an extension are linearly disjoint from the base

`const_independent`: if `eⱼ ∈ E` are linearly independent over the constants of `E`, they remain
linearly independent over the constants of any differential extension `L ⊇ E`. (Induction: divide
a relation by `e₀` and differentiate.)
-/

open Polynomial

namespace Curves

open Differential

variable {E L : Type*} [Field E] [Field L] [Differential E] [Differential L]

theorem const_independent (jE : E →+* L) (hj : ∀ z, (jE z)′ = jE z′) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) :
    ∀ e : ι → E, (∀ k : ι → E, (∀ j ∈ s, (k j)′ = 0) → ∑ j ∈ s, k j * e j = 0 → ∀ j ∈ s, k j = 0) →
      ∀ c : ι → L, (∀ j ∈ s, (c j)′ = 0) → ∑ j ∈ s, c j * jE (e j) = 0 → ∀ j ∈ s, c j = 0 := by
  induction s using Finset.induction_on with
  | empty => intro e _ c _ _ j hj; exact absurd hj (Finset.notMem_empty j)
  | insert a s ha ih =>
    intro e hind c hc hrel
    -- `e a ≠ 0`
    have hea : e a ≠ 0 := by
      intro h0
      have := hind (fun j ↦ if j = a then 1 else 0) (fun j _ ↦ by split_ifs <;> simp)
        (by
          rw [Finset.sum_insert ha, if_pos rfl, h0, mul_zero, zero_add]
          exact Finset.sum_eq_zero fun j hj ↦ by
            rw [if_neg (fun (h : j = a) ↦ ha (h ▸ hj)), zero_mul])
        a (Finset.mem_insert_self _ _)
      simp at this
    -- the derived family `(eⱼ / eₐ)′`
    set f : ι → E := fun j ↦ (e j / e a)′ with hf
    have hfind : ∀ k : ι → E, (∀ j ∈ s, (k j)′ = 0) → ∑ j ∈ s, k j * f j = 0 →
        ∀ j ∈ s, k j = 0 := by
      intro k hk hsum
      set κ := ∑ j ∈ s, k j * (e j / e a) with hκ
      have hκ' : κ′ = 0 := by
        rw [hκ, map_sum]
        rw [← hsum]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [Derivation.leibniz, hk j hj, smul_zero, add_zero, smul_eq_mul]
      have := hind (fun j ↦ if j = a then -κ else k j) (fun j hj ↦ by
          split_ifs with h
          · rw [map_neg, hκ', neg_zero]
          · exact hk j ((Finset.mem_insert.mp hj).resolve_left h))
        (by
          rw [Finset.sum_insert ha, if_pos rfl]
          rw [Finset.sum_congr rfl (g := fun j ↦ k j * e j) (fun j hj ↦ by
            rw [if_neg (fun (h : j = a) ↦ ha (h ▸ hj))])]
          rw [hκ, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_eq_zero fun j _ ↦ ?_
          field_simp
          ring)
      intro j hj
      have h2 := this j (Finset.mem_insert_of_mem hj)
      rwa [if_neg (fun (h : j = a) ↦ ha (h ▸ hj))] at h2
    -- the relation divided by `eₐ` and differentiated
    have hjea : jE (e a) ≠ 0 := (map_ne_zero_iff jE jE.injective).mpr hea
    have hrel' : c a + ∑ j ∈ s, c j * jE (e j / e a) = 0 := by
      have h1 : (c a * jE (e a) + ∑ j ∈ s, c j * jE (e j)) / jE (e a) = 0 := by
        rw [← Finset.sum_insert ha (f := fun j ↦ c j * jE (e j)), hrel, zero_div]
      rw [add_div, Finset.sum_div] at h1
      rw [← h1]
      congr 1
      · field_simp
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_div₀]; ring
    have hd := congrArg (fun z : L ↦ z′) hrel'
    simp only [map_add, map_sum, Derivation.leibniz, hc a (Finset.mem_insert_self _ _),
      map_zero, smul_eq_mul] at hd
    have hs : ∑ j ∈ s, c j * jE (f j) = 0 := by
      rw [← hd, zero_add]
      refine Finset.sum_congr rfl fun j hjs ↦ ?_
      rw [hc j (Finset.mem_insert_of_mem hjs), mul_zero, add_zero, hj, hf]
    have hcs := ih f hfind c (fun j hj ↦ hc j (Finset.mem_insert_of_mem hj)) hs
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · have : c j * jE (e j) = 0 := by
        rw [← hrel, Finset.sum_insert ha, Finset.sum_eq_zero (fun i hi ↦ by rw [hcs i hi, zero_mul]),
          add_zero]
      exact (mul_eq_zero.mp this).resolve_right hjea
    · exact hcs j hj'

end Curves
