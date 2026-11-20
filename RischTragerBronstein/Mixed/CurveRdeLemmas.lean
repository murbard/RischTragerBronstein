import RischTragerBronstein.Mixed.CurveRde

/-!
# The parametric Risch equation on a curve: algebraic lemmas

* `toPoly_flatV`: the Kronecker flattening `∑ᵢ X^{b i} Vᵢ`;
* `kronecker_eq_zero`: it is injective on blocks of degree `< b`;
* `scaledWs_spec`: the scaled numerators over the common denominator.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Kron

lemma le_foldr_max_self {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

lemma toPoly_padTo (p : CPoly ℚ) (b : ℕ) : toPoly (padTo p b) = toPoly p := by
  rw [padTo, toPoly_append]
  have : toPoly (List.replicate (b - p.length) (0 : ℚ)) = 0 := by
    rw [← isZero_iff]; simp [isZero]
  rw [this, mul_zero, add_zero]

lemma length_padTo (p : CPoly ℚ) (b : ℕ) (hp : p.length ≤ b) : (padTo p b).length = b := by
  simp [padTo]; omega

lemma toPoly_flatV (b : ℕ) : ∀ V : BPoly ℚ, (∀ p ∈ V, p.length ≤ b) →
    toPoly (flatV V b) = ∑ i ∈ Finset.range V.length, X ^ (b * i) * toPoly (V.getD i [])
  | [], _ => by simp [flatV]
  | p :: V, hV => by
    have ih := toPoly_flatV b V fun q hq ↦ hV q (List.mem_cons_of_mem _ hq)
    have hp := hV p List.mem_cons_self
    rw [flatV, List.map_cons, List.flatten_cons, toPoly_append, length_padTo p b hp,
      toPoly_padTo]
    rw [flatV] at ih
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, mul_zero, pow_zero, one_mul,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, ← pow_add]; ring_nf

/-- **Kronecker substitution is injective** on blocks of degree `< b`. -/
lemma kronecker_eq_zero {S : Type*} [Field S] (b m : ℕ) (G : ℕ → S[X])
    (hG : ∀ i < m, (G i).degree < b)
    (h0 : ∑ i ∈ Finset.range m, X ^ (b * i) * G i = 0) : ∀ i < m, G i = 0 := by
  intro i hi
  ext e
  rw [Polynomial.coeff_zero]
  by_cases he : e < b
  · have := congrArg (fun P : S[X] ↦ P.coeff (b * i + e)) h0
    simp only [finset_sum_coeff, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · rwa [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left] at this
    · intro l hl hli
      rw [coeff_X_pow_mul']
      split_ifs with hle
      · have hlt := Finset.mem_range.mp hl
        rcases Nat.lt_or_gt_of_ne hli with hl' | hl'
        · -- `l < i`: the index is beyond the degree
          refine coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hG l hlt) ?_)
          have : b * l + b ≤ b * i := by nlinarith
          exact_mod_cast (by omega : b ≤ b * i + e - b * l)
        · exfalso
          have : b * i + b ≤ b * l := by nlinarith
          omega
      · rfl
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hG i hi) (by exact_mod_cast not_lt.mp he))

end Kron

section Scaled

lemma toB_map_mul (q : CPoly ℚ) : ∀ W : BPoly ℚ,
    toB (W.map (mul q)) = Polynomial.C (toPoly q) * toB W
  | [] => by simp
  | c :: W => by
    rw [List.map_cons, toB_cons, toB_cons, toB_map_mul q W, toPoly_mul]; simp; ring

lemma length_scaledWs : ∀ L : List (BPoly ℚ × CPoly ℚ), (scaledWs L).length = L.length
  | [] => rfl
  | p :: L => by simp [scaledWs, length_scaledWs L]

/-- **The scaled numerators**: `Vₖ · Qₖ = (∏ Q) · Wₖ`. -/
lemma scaledWs_spec : ∀ (L : List (BPoly ℚ × CPoly ℚ)) (k : ℕ), k < L.length →
    toB ((scaledWs L).getD k []) * Polynomial.C (toPoly (L.getD k ([], [])).2) =
      Polynomial.C (toPoly (prodQs L)) * toB (L.getD k ([], [])).1
  | [], k, hk => by simp at hk
  | p :: L, 0, _ => by
    simp only [scaledWs, prodQs, List.getD_cons_zero, toB_map_mul, toPoly_mul, map_mul]; ring
  | p :: L, k + 1, hk => by
    have ih := scaledWs_spec L k (by simpa using hk)
    have hk' : k < (scaledWs L).length := by rw [length_scaledWs]; simpa using hk
    simp only [scaledWs, prodQs, List.getD_cons_succ, toPoly_mul, map_mul]
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map, toB_map_mul,
      ← List.getD_eq_getElem _ [] hk', mul_assoc, ih]
    ring

lemma prodQs_ne_zero : ∀ L : List (BPoly ℚ × CPoly ℚ), (∀ p ∈ L, toPoly p.2 ≠ 0) →
    toPoly (prodQs L) ≠ 0
  | [], _ => by simp [prodQs, CPoly.toPoly]
  | p :: L, h => by
    rw [prodQs, toPoly_mul]
    exact mul_ne_zero (h p List.mem_cons_self)
      (prodQs_ne_zero L fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

lemma length_le_maxLenB (Vs : List (BPoly ℚ)) : ∀ V ∈ Vs, ∀ p ∈ V, p.length ≤ maxLenB Vs := by
  intro V hV p hp
  have h1 : p.length ≤ (V.map List.length).foldr max 0 :=
    le_foldr_max_self (List.mem_map_of_mem hp)
  have h2 : (V.map List.length).foldr max 0 ≤ maxLenB Vs :=
    le_foldr_max_self (List.mem_map_of_mem (f := fun V ↦ (V.map List.length).foldr max 0) hV)
  omega

end Scaled

section Sums

variable {S : Type*} [Field S] (ι : ℚ →+* S)

lemma lcombS_eq_range : ∀ (w : List S) (vs : List (CPoly ℚ)), w.length = vs.length →
    lcombS ι w vs = ∑ k ∈ Finset.range vs.length, C (w.getD k 0) * (toPoly (vs.getD k [])).map ι
  | [], [], _ => by simp [lcombS]
  | c :: w, v :: vs, h => by
    have ih := lcombS_eq_range w vs (by simpa using h)
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma lcomb_eq_range' : ∀ (w : List ℚ) (vs : List (CPoly ℚ)),
    lcomb w vs = ∑ k ∈ Finset.range vs.length, C (w.getD k 0) * toPoly (vs.getD k [])
  | [], vs => by simp [lcomb]
  | c :: w, [] => by simp [lcomb]
  | c :: w, v :: vs => by
    have ih := lcomb_eq_range' w vs
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- Reindexing a sum over `n (E + 1)` indices. -/
lemma sum_range_mul_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (E : ℕ) : ∀ n : ℕ,
    ∑ k ∈ Finset.range (n * (E + 1)), f k =
      ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (E + 1), f (i * (E + 1) + e)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul_succ f E n,
      Finset.sum_range_succ (fun i ↦ ∑ e ∈ Finset.range (E + 1), f (i * (E + 1) + e)) n]

end Sums

section Bcodes

lemma length_bcodes (den : CPoly ℚ) (E n : ℕ) : (bcodes den n E).length = n * (E + 1) := by
  simp [bcodes, List.length_flatMap, List.map_const', List.sum_replicate]

lemma getD_bcodes (den : CPoly ℚ) (E : ℕ) : ∀ (n i e : ℕ), i < n → e ≤ E →
    (bcodes den n E).getD (i * (E + 1) + e) [] = bcode den i e
  | 0, i, e, hi, _ => by omega
  | n + 1, i, e, hi, he => by
    have hl := length_bcodes den E n
    rw [bcodes] at hl ⊢
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith)]
      have := getD_bcodes den E n i e hin he
      rw [bcodes] at this
      exact this
    · have hi' : i = n := by omega
      subst hi'
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

end Bcodes

section FlatMap

lemma length_flatMap_range {α : Type*} (f : ℕ → ℕ → α) (E n : ℕ) :
    ((List.range n).flatMap fun i ↦ (List.range (E + 1)).map fun e ↦ f i e).length =
      n * (E + 1) := by
  simp [List.length_flatMap, List.map_const', List.sum_replicate]

lemma getD_flatMap_range {α : Type*} (f : ℕ → ℕ → α) (d : α) (E : ℕ) : ∀ (n i e : ℕ), i < n →
    e ≤ E → ((List.range n).flatMap fun i ↦ (List.range (E + 1)).map fun e ↦ f i e).getD
      (i * (E + 1) + e) d = f i e
  | 0, i, e, hi, _ => by omega
  | n + 1, i, e, hi, he => by
    have hl := length_flatMap_range f E n
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith)]
      exact getD_flatMap_range f d E n i e hin he
    · have hi' : i = n := by omega
      subst hi'
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

end FlatMap

end Curves
