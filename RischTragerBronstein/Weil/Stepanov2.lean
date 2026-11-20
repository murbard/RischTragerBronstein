import RischTragerBronstein.Weil.Stepanov1

/-!
# Stepanov's method, step 2: Hasse derivatives of `f^c s`

`f^i D^{(i)}(f^c) = f^c U` with `deg U ≤ i (d − 1)` (`exists_hasseDeriv_pow`), hence
`f^k D^{(k)}(f^c s) = f^c T` with `deg T ≤ deg s + k (d − 1)` (`exists_hasseDeriv_pow_mul`).
-/

open Polynomial

namespace Stepanov

variable {R : Type*} [CommRing R]

lemma natDegree_sum_le_of_forall {ι : Type*} (s : Finset ι) (g : ι → R[X]) (B : ℕ)
    (h : ∀ i ∈ s, (g i).natDegree ≤ B) : (∑ i ∈ s, g i).natDegree ≤ B :=
  (natDegree_sum_le_of_forall_le s g h)

/-- `f^i D^{(i)}(f^c) = f^c U`, `deg U ≤ i (deg f − 1)`. -/
theorem exists_hasseDeriv_pow (f : R[X]) (hd : 1 ≤ f.natDegree) :
    ∀ (c i : ℕ), ∃ U : R[X], f ^ i * hasseDeriv i (f ^ c) = f ^ c * U ∧
      U.natDegree ≤ i * (f.natDegree - 1)
  | 0, i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨0, by rw [pow_zero, hasseDeriv_apply_one _ hi, mul_zero, mul_zero], by simp⟩
  | c + 1, i => by
    classical
    choose U hU hUd using fun b ↦ exists_hasseDeriv_pow f hd c b
    -- `f^{c+1} = f · f^c`, Leibniz
    refine ⟨∑ ab ∈ Finset.antidiagonal i,
      (if ab.1 = 0 then U ab.2 else f ^ (ab.1 - 1) * hasseDeriv ab.1 f * U ab.2), ?_, ?_⟩
    · rw [pow_succ', hasseDeriv_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ab hab ↦ ?_
      have hs := Finset.mem_antidiagonal.mp hab
      have e : f ^ i = f ^ ab.1 * f ^ ab.2 := by rw [← pow_add, hs]
      rw [e]
      split_ifs with ha
      · rw [ha, hasseDeriv_zero', pow_zero, one_mul]
        calc f ^ ab.2 * (f * hasseDeriv ab.2 (f ^ c))
            = f * (f ^ ab.2 * hasseDeriv ab.2 (f ^ c)) := by ring
          _ = f * (f ^ c * U ab.2) := by rw [hU]
          _ = f * f ^ c * U ab.2 := by ring
      · obtain ⟨a', ha'⟩ : ∃ a', ab.1 = a' + 1 := ⟨ab.1 - 1, by omega⟩
        rw [ha', Nat.add_sub_cancel]
        calc f ^ (a' + 1) * f ^ ab.2 * (hasseDeriv (a' + 1) f * hasseDeriv ab.2 (f ^ c))
            = f * f ^ a' * hasseDeriv (a' + 1) f * (f ^ ab.2 * hasseDeriv ab.2 (f ^ c)) := by ring
          _ = f * f ^ c * (f ^ a' * hasseDeriv (a' + 1) f * U ab.2) := by rw [hU]; ring
    · refine natDegree_sum_le_of_forall _ _ _ fun ab hab ↦ ?_
      have hs := Finset.mem_antidiagonal.mp hab
      split_ifs with ha
      · have := hUd ab.2
        have : ab.2 = i := by omega
        subst this; exact hUd _
      · rcases le_or_gt ab.1 f.natDegree with hle | hlt
        · have h1 := natDegree_mul_le (p := f ^ (ab.1 - 1) * hasseDeriv ab.1 f) (q := U ab.2)
          have h2 := natDegree_mul_le (p := f ^ (ab.1 - 1)) (q := hasseDeriv ab.1 f)
          have h3 := natDegree_pow_le (p := f) (n := ab.1 - 1)
          have h4 := natDegree_hasseDeriv_le f ab.1
          have h5 := hUd ab.2
          set d := f.natDegree
          have h6 : (ab.1 - 1) * d + (d - ab.1) + ab.2 * (d - 1) ≤ i * (d - 1) := by
            rw [← hs]
            obtain ⟨e, he⟩ : ∃ e, d = ab.1 + e := ⟨d - ab.1, by omega⟩
            rw [he]
            obtain ⟨a', ha'⟩ : ∃ a', ab.1 = a' + 1 := ⟨ab.1 - 1, by omega⟩
            rw [ha']; simp only [Nat.add_sub_cancel]
            rw [show a' + 1 + e - (a' + 1) = e by omega, show a' + 1 + e - 1 = a' + e by omega]
            nlinarith
          omega
        · rw [hasseDeriv_eq_zero_of_lt_natDegree f _ hlt, mul_zero, zero_mul, natDegree_zero]
          exact Nat.zero_le _

/-- **`f^k D^{(k)}(f^c s) = f^c T`, `deg T ≤ deg s + k (deg f − 1)`.** -/
theorem exists_hasseDeriv_pow_mul (f : R[X]) (hd : 1 ≤ f.natDegree) (c k : ℕ) (s : R[X]) :
    ∃ T : R[X], f ^ k * hasseDeriv k (f ^ c * s) = f ^ c * T ∧
      T.natDegree ≤ s.natDegree + k * (f.natDegree - 1) := by
  classical
  choose U hU hUd using exists_hasseDeriv_pow f hd c
  refine ⟨∑ ab ∈ Finset.antidiagonal k, f ^ ab.2 * U ab.1 * hasseDeriv ab.2 s, ?_, ?_⟩
  · rw [hasseDeriv_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab hab ↦ ?_
    have hs := Finset.mem_antidiagonal.mp hab
    have e : f ^ k = f ^ ab.1 * f ^ ab.2 := by rw [← pow_add, hs]
    rw [e]
    calc f ^ ab.1 * f ^ ab.2 * (hasseDeriv ab.1 (f ^ c) * hasseDeriv ab.2 s)
        = (f ^ ab.1 * hasseDeriv ab.1 (f ^ c)) * (f ^ ab.2 * hasseDeriv ab.2 s) := by ring
      _ = f ^ c * (f ^ ab.2 * U ab.1 * hasseDeriv ab.2 s) := by rw [hU]; ring
  · refine natDegree_sum_le_of_forall _ _ _ fun ab hab ↦ ?_
    have hs := Finset.mem_antidiagonal.mp hab
    rcases le_or_gt ab.2 s.natDegree with hle | hlt
    · have h1 := natDegree_mul_le (p := f ^ ab.2 * U ab.1) (q := hasseDeriv ab.2 s)
      have h2 := natDegree_mul_le (p := f ^ ab.2) (q := U ab.1)
      have h3 := natDegree_pow_le (p := f) (n := ab.2)
      have h4 := natDegree_hasseDeriv_le s ab.2
      have h5 := hUd ab.1
      set d := f.natDegree
      have h6 : ab.2 * d + ab.1 * (d - 1) + (s.natDegree - ab.2) ≤ s.natDegree + k * (d - 1) := by
        rw [← hs]
        obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        rw [he]; simp only [Nat.add_sub_cancel]
        obtain ⟨t, ht⟩ : ∃ t, s.natDegree = ab.2 + t := ⟨s.natDegree - ab.2, by omega⟩
        rw [ht, show ab.2 + t - ab.2 = t by omega]
        nlinarith
      omega
    · rw [hasseDeriv_eq_zero_of_lt_natDegree s _ hlt, mul_zero, natDegree_zero]
      exact Nat.zero_le _

end Stepanov
