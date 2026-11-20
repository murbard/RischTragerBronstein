import RischTragerBronstein.Mixed.NKExp0
import RischTragerBronstein.Mixed.NKInfLead

/-!
# Leading coefficients above `x = 0` for a single place above `0`

The analogue at `x = 0` of `NKInfLead`: for `F` with `ord₀ a₀ = d`, `gcd(n, d) = 1` and a root `r` of
`F(Tᴺ, Y)`: the leading coefficient `γ₀` of `r` satisfies `γ₀ⁿ = −tc(a₀)` (`root_lead_zero`), and for
`W = ∑ bⱼ Yʲ` the index `j₀` of least weight `n ord₀ bⱼ + j d` gives the leading coefficient
`tc(b_{j₀}) γ₀^{j₀}` of `W(Tᴺ, r)` (`eval_lead_zero`).
-/

open Polynomial HahnSeries LaurentSeries Differential

set_option linter.unusedSectionVars false

namespace Curves

section LeadZero

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The coefficients of `P(Tᴺ)`. -/
lemma coeff_branchSub_zero (N : ℕ) (hN : 0 < N) (P : C[X]) (k : ℕ) :
    (branchSub (K := K) N 0 P).coeff ((N * k : ℕ) : ℤ) = algebraMap C K (P.coeff k) := by
  rw [branchSub_apply, map_zero, zero_add, LaurentSeries.coeff_ofPS,
    if_pos (by positivity)]
  simp only [Int.toNat_natCast, Polynomial.coeff_coe]
  rw [← expand_eq_comp_X_pow, mul_comm, coeff_expand_mul hN, coeff_map]

/-- The leading coefficient of `P(Tᴺ)` is the trailing coefficient of `P`. -/
lemma leadingCoeff_branchSub_zero (N : ℕ) (hN : 0 < N) (P : C[X]) (hP : P ≠ 0) :
    (branchSub (K := K) N 0 P).leadingCoeff = algebraMap C K P.trailingCoeff := by
  rw [HahnSeries.leadingCoeff_eq, order_branchSub_zero N hN P hP, coeff_branchSub_zero N hN,
    trailingCoeff]

/-- **The leading coefficient of a root above `0`**: `γ₀ⁿ = −tc(a₀)`. -/
theorem root_lead_zero (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natTrailingDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ d * (n - i) < n * (F.coeff i).natTrailingDegree)
    (r : LaurentSeries K) (hr : (F.map (branchSub (K := K) N 0)).eval r = 0) :
    r.leadingCoeff ^ n = -algebraMap C K (F.coeff 0).trailingCoeff := by
  classical
  obtain ⟨hr0, hro⟩ := root_order_zero F hF n d N hn hn0 hN ha0 hd hw r hr
  have hdeg : (F.map (branchSub (K := K) N 0)).natDegree = n := by rw [hF.natDegree_map, hn]
  rw [eval_eq_sum_range' (by omega : (F.map (branchSub (K := K) N 0)).natDegree < n + 1)] at hr
  simp only [coeff_map] at hr
  set k : ℤ := (N : ℤ) * d with hk
  have hc := congrArg (fun z : LaurentSeries K ↦ z.coeff k) hr
  simp only [HahnSeries.coeff_sum, HahnSeries.coeff_zero] at hc
  have hlead : F.coeff n = 1 := by rw [← hn]; exact hF.leadingCoeff
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hc
  have hmid : ∑ i ∈ Finset.range m,
      (branchSub (K := K) N 0 (F.coeff (i + 1)) * r ^ (i + 1)).coeff k = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi' : i + 1 < m + 1 := by have := Finset.mem_range.mp hi; omega
    by_cases hci : F.coeff (i + 1) = 0
    · rw [hci, map_zero, zero_mul, HahnSeries.coeff_zero]
    · refine HahnSeries.coeff_eq_zero_of_lt_order ?_
      have h1 := branchSub_zero_ne_zero (K := K) N hN _ hci
      have h2 : r ^ (i + 1) ≠ 0 := pow_ne_zero _ hr0
      rw [HahnSeries.order_mul h1 h2, order_branchSub_zero N hN _ hci, HahnSeries.order_pow,
        nsmul_eq_mul]
      rcases hw (i + 1) (by omega) hi' with h0 | hlt'
      · exact absurd h0 hci
      · have hsub : m + 1 - (i + 1) = m - i := by omega
        rw [hsub] at hlt'
        have h1 : (d : ℤ) * (m - i) < ((m + 1 : ℕ) : ℤ) * (F.coeff (i + 1)).natTrailingDegree := by
          have := hlt'; rw [← Nat.cast_lt (α := ℤ)] at this
          push_cast [Nat.cast_sub (by omega : i ≤ m)] at this; push_cast; linarith
        have h3 : (N : ℤ) * (d * (m - i)) <
            N * (((m + 1 : ℕ) : ℤ) * (F.coeff (i + 1)).natTrailingDegree) :=
          mul_lt_mul_of_pos_left h1 hNpos
        have key : ((m + 1 : ℕ) : ℤ) * k < ((m + 1 : ℕ) : ℤ) *
            (((N * (F.coeff (i + 1)).natTrailingDegree : ℕ) : ℤ) + (i + 1 : ℕ) * r.order) := by
          rw [hk]; push_cast at h3 hro ⊢; nlinarith
        exact lt_of_mul_lt_mul_left key hnpos.le
  rw [hmid, zero_add] at hc
  have htop : (branchSub (K := K) N 0 (F.coeff (m + 1)) * r ^ (m + 1)).coeff k =
      r.leadingCoeff ^ (m + 1) := by
    rw [hlead, map_one, one_mul, ← leadingCoeff_pow_hahn, HahnSeries.leadingCoeff_eq,
      HahnSeries.order_pow, nsmul_eq_mul, hk, hro]
  have hbot : (branchSub (K := K) N 0 (F.coeff 0) * r ^ 0).coeff k =
      algebraMap C K (F.coeff 0).trailingCoeff := by
    rw [pow_zero, mul_one, ← leadingCoeff_branchSub_zero N hN _ ha0, HahnSeries.leadingCoeff_eq,
      order_branchSub_zero N hN _ ha0, hd, hk]
    push_cast; rfl
  rw [htop, hbot] at hc
  linear_combination hc

/-- **The leading term above `0`**: the index `j₀` of least weight gives the order and the
leading coefficient `tc(b_{j₀}) γ₀^{j₀}` of `W(Tᴺ, r)`. -/
theorem eval_lead_zero (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natTrailingDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ d * (n - i) < n * (F.coeff i).natTrailingDegree)
    (hcop : Nat.Coprime n d)
    (r : LaurentSeries K) (hr : (F.map (branchSub (K := K) N 0)).eval r = 0)
    (W : C[X][X]) (hW0 : W ≠ 0) (hWn : W.natDegree < n) :
    ∃ j0 < n, W.coeff j0 ≠ 0 ∧ wt0W n d W = n * (W.coeff j0).natTrailingDegree + j0 * d ∧
      (W.map (branchSub (K := K) N 0)).eval r ≠ 0 ∧
      (n : ℤ) * ((W.map (branchSub (K := K) N 0)).eval r).order = (N : ℤ) * wt0W n d W ∧
      ((W.map (branchSub (K := K) N 0)).eval r).leadingCoeff =
        algebraMap C K (W.coeff j0).trailingCoeff * r.leadingCoeff ^ j0 := by
  classical
  obtain ⟨hr0, hro⟩ := root_order_zero F hF n d N hn hn0 hN ha0 hd hw r hr
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  set t : ℕ → LaurentSeries K := fun j ↦ branchSub (K := K) N 0 (W.coeff j) * r ^ j with ht
  have hev : (W.map (branchSub (K := K) N 0)).eval r = ∑ j ∈ Finset.range n, t j := by
    rw [eval_eq_sum_range' (by
      rw [natDegree_map_eq_of_injective (branchSub_injective N hN 0)]; exact hWn)]
    simp only [coeff_map, ht]
  set wt : ℕ → ℕ := fun j ↦ n * (W.coeff j).natTrailingDegree + j * d with hwt
  have hto : ∀ j, W.coeff j ≠ 0 → t j ≠ 0 ∧
      (n : ℤ) * (t j).order = (N : ℤ) * (wt j : ℕ) := fun j hj ↦ by
    have h1 := branchSub_zero_ne_zero (K := K) N hN _ hj
    have h2 : r ^ j ≠ 0 := pow_ne_zero _ hr0
    refine ⟨mul_ne_zero h1 h2, ?_⟩
    rw [ht]; dsimp only
    rw [HahnSeries.order_mul h1 h2, order_branchSub_zero N hN _ hj, HahnSeries.order_pow,
      nsmul_eq_mul]
    simp only [hwt]
    push_cast
    linear_combination (j : ℤ) * hro
  have hnemp : ((Finset.range n).filter fun j ↦ W.coeff j ≠ 0).Nonempty :=
    ⟨W.natDegree, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hWn,
      mt leadingCoeff_eq_zero.mp hW0⟩⟩
  obtain ⟨j0, hj0m, hj0min⟩ := Finset.exists_min_image _ wt hnemp
  obtain ⟨hj0r, hj0⟩ := Finset.mem_filter.mp hj0m
  have hdist : ∀ j ∈ Finset.range n, j ≠ j0 → W.coeff j ≠ 0 → wt j0 < wt j := by
    intro j hj hne hc
    have hle := hj0min j (Finset.mem_filter.mpr ⟨hj, hc⟩)
    refine lt_of_le_of_ne hle fun heq ↦ hne ?_
    have hj' := Finset.mem_range.mp hj
    have hj0' := Finset.mem_range.mp hj0r
    have hmod : j * d ≡ j0 * d [MOD n] := by
      have e1 : wt j % n = j * d % n := by simp only [hwt]; rw [Nat.mul_add_mod]
      have e2 : wt j0 % n = j0 * d % n := by simp only [hwt]; rw [Nat.mul_add_mod]
      unfold Nat.ModEq; rw [← e1, ← e2, heq]
    have := Nat.ModEq.cancel_right_of_coprime (c := d) (by rw [Nat.gcd_comm]; exact hcop.symm) hmod
    exact Nat.ModEq.eq_of_lt_of_lt this hj' hj0'
  have hwt0 : wt0W n d W = wt j0 := by
    unfold wt0W
    rw [dif_pos hnemp]
    exact le_antisymm (Finset.inf'_le _ hj0m) (Finset.le_inf' _ _ fun j hj ↦ hj0min j hj)
  obtain ⟨ht0, ht0o⟩ := hto j0 hj0
  obtain ⟨hne, hord⟩ := order_sum_of_unique_min (Finset.range n) t j0 hj0r ht0 fun j hj hne ↦ by
    by_cases hc : W.coeff j = 0
    · left; rw [ht]; dsimp only; rw [hc, map_zero, zero_mul]
    · right
      have hlt := hdist j hj hne hc
      have hlt' : (N : ℤ) * (wt j0 : ℕ) < N * (wt j : ℕ) :=
        mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hNpos
      have h2 := (hto j hc).2
      have key : (n : ℤ) * (t j0).order < n * (t j).order := by rw [ht0o, h2]; exact hlt'
      exact lt_of_mul_lt_mul_left key hnpos.le
  have hlc := leadingCoeff_sum_unique_min (Finset.range n) t j0 hj0r ht0 fun j hj hne ↦ by
    by_cases hc : W.coeff j = 0
    · left; rw [ht]; dsimp only; rw [hc, map_zero, zero_mul]
    · right
      have hlt := hdist j hj hne hc
      have hlt' : (N : ℤ) * (wt j0 : ℕ) < N * (wt j : ℕ) :=
        mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hNpos
      have h2 := (hto j hc).2
      have key : (n : ℤ) * (t j0).order < n * (t j).order := by rw [ht0o, h2]; exact hlt'
      exact lt_of_mul_lt_mul_left key hnpos.le
  rw [hev]
  refine ⟨j0, Finset.mem_range.mp hj0r, hj0, hwt0, hne, by rw [hord, ht0o, hwt0], ?_⟩
  rw [hlc, ht]
  dsimp only
  rw [HahnSeries.leadingCoeff_mul, leadingCoeff_branchSub_zero N hN _ hj0, leadingCoeff_pow_hahn]


end LeadZero

end Curves
