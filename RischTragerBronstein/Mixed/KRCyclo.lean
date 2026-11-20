import RischTragerBronstein.Mixed.KRCodes
import RischTragerBronstein.Computable.EuclidDegree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The computed cyclotomic polynomial

`cycloQ_spec`: `cycloQ n` is Mathlib's `cyclotomic n ℚ` (for `n > 0`): `Xⁿ − 1` is the product of
`Φ_d` over `d ∣ n`, and the division by the product over the proper divisors is exact.
-/

open Polynomial CPoly

namespace Curves.MT

lemma toPoly_xnSub1 (n : ℕ) (hn : 0 < n) : toPoly (xnSub1 n) = X ^ n - 1 := by
  rw [xnSub1, toPoly_cons, toPoly_append]
  have : toPoly (List.replicate (n - 1) (0 : ℚ)) = 0 := by
    induction (n - 1) with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, ih]
  rw [this, List.length_replicate]
  simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_one, zero_add, mul_one]
  rw [← pow_succ', Nat.sub_add_cancel hn]
  simp [sub_eq_neg_add]

lemma toPoly_foldr_mul (l : List (CPoly ℚ)) :
    toPoly (l.foldr (fun p acc ↦ CPoly.mul p acc) [1]) = (l.map toPoly).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **The computed `Φₙ` is the cyclotomic polynomial.** -/
theorem cycloQ_spec : ∀ n : ℕ, 0 < n → toPoly (cycloQ n) = cyclotomic n ℚ
  | n, hn => by
    rw [cycloQ, if_neg hn.ne']
    set ds := (List.range n).filter (fun d ↦ decide (0 < d ∧ d ∣ n)) with hds
    have hmem : ∀ d ∈ ds, 0 < d ∧ d ∣ n ∧ d < n := fun d hd ↦ by
      have h := List.mem_filter.mp hd
      simp only [decide_eq_true_eq] at h
      exact ⟨h.2.1, h.2.2, List.mem_range.mp h.1⟩
    have hrec : ∀ d ∈ ds, toPoly (cycloQ d) = cyclotomic d ℚ := fun d hd ↦
      cycloQ_spec d (hmem d hd).1
    set D := ds.attach.foldr (fun d acc ↦ CPoly.mul (cycloQ d.1) acc) [1] with hD
    have hDval : toPoly D = ∏ d ∈ n.properDivisors, cyclotomic d ℚ := by
      have e1 : D = (ds.attach.map fun d ↦ cycloQ d.1).foldr (fun p acc ↦ CPoly.mul p acc) [1] := by
        rw [hD, List.foldr_map]
      rw [e1, toPoly_foldr_mul, List.map_map]
      have e2 : (ds.attach.map (toPoly ∘ fun d ↦ cycloQ d.1)) = ds.attach.map fun d ↦ cyclotomic d.1 ℚ :=
        List.map_congr_left fun d hd ↦ by simp [hrec d.1 d.2]
      rw [e2, List.attach_map_val (l := ds) (f := fun d ↦ cyclotomic d ℚ)]
      have hnd : ds.Nodup := (List.nodup_range).filter _
      have hset : ds.toFinset = n.properDivisors := by
        ext d
        simp only [List.mem_toFinset, hds, List.mem_filter, List.mem_range, decide_eq_true_eq,
          Nat.mem_properDivisors]
        constructor
        · rintro ⟨h1, -, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, Nat.pos_of_dvd_of_pos h1 hn, h1⟩
      rw [← hset, List.prod_toFinset _ hnd]
    have hprod : X ^ n - 1 = cyclotomic n ℚ * toPoly D := by
      rw [hDval, ← prod_cyclotomic_eq_X_pow_sub_one hn, ← Nat.cons_self_properDivisors hn.ne',
        Finset.prod_cons]
    have hD0 : toPoly D ≠ 0 := by
      rw [hDval]
      exact Finset.prod_ne_zero_iff.mpr fun d _ ↦ cyclotomic_ne_zero d ℚ
    have hspec := divMod_spec (xnSub1 n) D
    have hdeg := divMod_degree_lt (xnSub1 n) D hD0
    rw [toPoly_xnSub1 n hn, hprod] at hspec
    set q := toPoly (divMod (xnSub1 n) D).1
    set r := toPoly (divMod (xnSub1 n) D).2
    have hr : r = (cyclotomic n ℚ - q) * toPoly D := by linear_combination (-1 : ℚ[X]) * hspec
    by_contra hne
    have hsub : cyclotomic n ℚ - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have : (toPoly D).degree ≤ r.degree := by
      rw [hr, degree_mul]
      exact le_add_of_nonneg_left (Polynomial.zero_le_degree_iff.mpr hsub)
    exact absurd hdeg (not_lt.mpr this)
termination_by n _ => n
decreasing_by exact (hmem d hd).2.2

end Curves.MT
