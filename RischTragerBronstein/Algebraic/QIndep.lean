import RischTragerBronstein.Liouville.Strong

/-!
# Logarithmic parts with `ℚ`-linearly independent coefficients

`logSum_qindep`: every `∑ cᵢ uᵢ′ / uᵢ` with constant `cᵢ` equals `∑ dⱼ wⱼ′ / wⱼ` where the
constants `dⱼ` are `ℚ`-linearly independent and each `wⱼ` is a product of integer powers of the
`uᵢ` (so it lies in any subfield containing them).
-/

namespace Differential

variable {K : Type*} [Field K] [CharZero K] [Differential K]

lemma logDeriv_zpow' (u : K) (hu : u ≠ 0) (n : ℤ) : logDeriv (u ^ n) = n * logDeriv u := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, logDeriv_pow]; simp
  · rw [zpow_neg, zpow_natCast, ← one_div, logDeriv_div _ _ one_ne_zero (pow_ne_zero _ hu),
      logDeriv_one, logDeriv_pow]
    simp

/-- A family `(dⱼ, wⱼ)_{j < k}`: `ℚ`-independent constants and non-zero elements of `S`. -/
def QIndepFam (S : Subfield K) (k : ℕ) (d w : ℕ → K) : Prop :=
  (∀ j < k, (d j)′ = 0) ∧ (∀ j < k, w j ≠ 0 ∧ w j ∈ S) ∧
    ∀ g : ℕ → ℚ, ∑ j ∈ Finset.range k, (g j : K) * d j = 0 → ∀ j < k, g j = 0

lemma deriv_ratCast_K (q : ℚ) : ((q : K))′ = 0 := by
  have hd : ((q.den : ℤ) : K) ≠ 0 := by exact_mod_cast q.den_nz
  have e : (q : K) * ((q.den : ℤ) : K) = ((q.num : ℤ) : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_intCast, ← Rat.cast_mul]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num q
  have := congrArg (fun z : K ↦ z′) e
  simp only [Derivation.leibniz, Derivation.map_intCast, smul_eq_mul, mul_zero, zero_add] at this
  exact (mul_eq_zero.mp this).resolve_left hd

/-- **Reduction to `ℚ`-independent coefficients.** -/
theorem logSum_qindep (S : Subfield K) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c u : ι → K) (hc : ∀ i ∈ s, (c i)′ = 0) (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ S) :
    ∃ (k : ℕ) (d w : ℕ → K), QIndepFam S k d w ∧
      ∑ i ∈ s, c i * logDeriv (u i) = ∑ j ∈ Finset.range k, d j * logDeriv (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, fun _ ↦ 0, fun _ ↦ 1, ⟨fun j hj ↦ absurd hj (by omega),
      fun j hj ↦ absurd hj (by omega), fun g _ j hj ↦ absurd hj (by omega)⟩, by simp⟩
  | insert i0 s hi0 ih =>
    obtain ⟨k, d, w, ⟨hd, hw, hind⟩, heq⟩ := ih (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))
    have hc0 := hc i0 (Finset.mem_insert_self _ _)
    obtain ⟨hu0, hu0S⟩ := hu i0 (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi0, heq]
    by_cases hspan : ∃ q : ℕ → ℚ, c i0 = ∑ j ∈ Finset.range k, (q j : K) * d j
    · -- `c₀` is a rational combination: absorb `u₀` into the `wⱼ`
      obtain ⟨q, hq⟩ := hspan
      set D : ℕ := ∏ j ∈ Finset.range k, (q j).den with hD
      have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ (q j).den_nz
      have hDK : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD0
      have hint : ∀ j ∈ Finset.range k, ∃ n : ℤ, (n : ℚ) = q j * D := by
        intro j hj
        obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun j ↦ (q j).den) hj
        refine ⟨(q j).num * m, ?_⟩
        rw [hD, hm]
        push_cast
        rw [← mul_assoc, Rat.mul_den_eq_num]
      choose! n hn using hint
      refine ⟨k, fun j ↦ d j / D, fun j ↦ w j ^ D * u i0 ^ n j,
        ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, fun g hg j hj ↦ ?_⟩, ?_⟩
      · show (d j / D)′ = 0
        rw [div_eq_mul_inv, Derivation.leibniz, hd j hj,
          show ((D : K)⁻¹)′ = 0 by rw [← Rat.cast_natCast, ← Rat.cast_inv]; exact deriv_ratCast_K _]
        simp
      · obtain ⟨hwj, hwS⟩ := hw j hj
        exact ⟨mul_ne_zero (pow_ne_zero _ hwj) (zpow_ne_zero _ hu0),
          mul_mem (pow_mem hwS _) (zpow_mem hu0S _)⟩
      · have := hind (fun j ↦ g j / D) (by
          rw [← hg]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          push_cast
          ring) j hj
        have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD0
        simpa [hD'] using this
      · have e : ∀ j ∈ Finset.range k, d j / D * logDeriv (w j ^ D * u i0 ^ n j) =
            d j * logDeriv (w j) + ((q j : K) * d j) * logDeriv (u i0) := by
          intro j hj
          have hwj := (hw j (Finset.mem_range.mp hj)).1
          rw [logDeriv_mul _ _ (pow_ne_zero _ hwj) (zpow_ne_zero _ hu0), logDeriv_pow,
            logDeriv_zpow' _ hu0]
          have hnq : ((n j : ℤ) : K) = (q j : K) * D := by
            rw [← Rat.cast_intCast, hn j hj]; push_cast; ring
          rw [hnq]
          field_simp
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, ← hq]
        ring
    · -- `c₀` is independent: append `(c₀, u₀)`
      have hspan' : ∀ q : ℕ → ℚ, c i0 ≠ ∑ j ∈ Finset.range k, (q j : K) * d j :=
        fun q h ↦ hspan ⟨q, h⟩
      refine ⟨k + 1, fun j ↦ if j < k then d j else c i0, fun j ↦ if j < k then w j else u i0,
        ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, fun g hg j hj ↦ ?_⟩, ?_⟩
      · beta_reduce; split_ifs with h
        · exact hd j h
        · exact hc0
      · beta_reduce; split_ifs with h
        · exact hw j h
        · exact ⟨hu0, hu0S⟩
      · beta_reduce at hg
        rw [Finset.sum_range_succ, if_neg (lt_irrefl k)] at hg
        have hs : ∑ j ∈ Finset.range k, (g j : K) * (if j < k then d j else c i0) =
            ∑ j ∈ Finset.range k, (g j : K) * d j :=
          Finset.sum_congr rfl fun j hj ↦ by rw [if_pos (Finset.mem_range.mp hj)]
        rw [hs] at hg
        have hgk : g k = 0 := by
          by_contra hgk
          have hgk' : (g k : K) ≠ 0 := by exact_mod_cast hgk
          apply hspan' (fun j ↦ -g j / g k)
          have hc' : c i0 = -(∑ j ∈ Finset.range k, (g j : K) * d j) / g k := by
            field_simp
            linear_combination hg
          rw [hc', neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          push_cast
          ring
        rw [hgk, Rat.cast_zero, zero_mul, add_zero] at hg
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hind g hg j hj
        · exact hgk
      · beta_reduce
        rw [Finset.sum_range_succ, if_neg (lt_irrefl k), if_neg (lt_irrefl k)]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [if_pos (Finset.mem_range.mp hj), if_pos (Finset.mem_range.mp hj)]

end Differential
