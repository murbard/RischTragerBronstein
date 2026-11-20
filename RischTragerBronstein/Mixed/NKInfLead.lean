import RischTragerBronstein.Mixed.NKLog

/-!
# Leading coefficients above infinity for a single place at infinity

For `F = Yⁿ + ∑ aᵢ(x) Yⁱ` of weighted shape (`deg a₀ = d`, `gcd(n, d) = 1`,
`n deg aᵢ < d (n − i)`) and a root `r` of `F(s⁻ᴺ, Y)`:

* `root_lead_inf`: the leading coefficient `γ` of `r` satisfies `γⁿ = −lc(a₀)`;
* `eval_lead_inf`: for `W = ∑ bⱼ Yʲ` (`deg_Y W < n`, `W ≠ 0`) the unique index `j₀` of largest
  weight `n deg bⱼ + j d` gives the order (`n · ord = −N wt(W)`) and the leading coefficient
  `lc(b_{j₀}) γ^{j₀}` of `W(s⁻ᴺ, r)`.
-/

open Polynomial HahnSeries LaurentSeries

namespace Curves

open Differential

section Lead

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma leadingCoeff_pow_hahn (z : LaurentSeries K) (k : ℕ) :
    (z ^ k).leadingCoeff = z.leadingCoeff ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

/-- The leading coefficient of `P(s⁻ᴺ)` is `lc P`. -/
lemma leadingCoeff_infSub (N : ℕ) (hN : 0 < N) (P : C[X]) (hP : P ≠ 0) :
    (infSub (K := K) N P).leadingCoeff = algebraMap C K P.leadingCoeff := by
  rw [HahnSeries.leadingCoeff_eq, order_infSub N hN P hP, infSub_eq]
  have e := HahnSeries.coeff_single_mul_add (r := (1 : K)) (b := -((N : ℤ) * P.natDegree)) (a := 0)
    (x := ofPowerSeries ℤ K (((P.reverse.map (algebraMap C K)).comp (X ^ N) : K[X]) : PowerSeries K))
  rw [zero_add] at e
  rw [e, one_mul, LaurentSeries.coeff_ofPS, if_pos le_rfl]
  have := infRev_const (C := C) (K := K) N hN P
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  simpa using this

/-- The leading coefficient of a sum with a unique term of least order. -/
lemma leadingCoeff_sum_unique_min {ι : Type*} (s : Finset ι) (t : ι → LaurentSeries K) (i0 : ι)
    (hi0 : i0 ∈ s) (h0 : t i0 ≠ 0) (hlt : ∀ i ∈ s, i ≠ i0 → t i = 0 ∨ (t i0).order < (t i).order) :
    (∑ i ∈ s, t i).leadingCoeff = (t i0).leadingCoeff := by
  obtain ⟨-, hord⟩ := order_sum_of_unique_min s t i0 hi0 h0 hlt
  rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord,
    coeff_sum_unique_min s t i0 hi0 hlt _ le_rfl]

/-- **The leading coefficient of a root above infinity**: `γⁿ = −lc(a₀)`. -/
theorem root_lead_inf (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ n * (F.coeff i).natDegree < d * (n - i))
    (r : LaurentSeries K) (hr : (F.map (infSub (K := K) N)).eval r = 0) :
    r.leadingCoeff ^ n = -algebraMap C K (F.coeff 0).leadingCoeff := by
  classical
  obtain ⟨hr0, hro⟩ := root_order_inf F hF n d N hn hn0 hN ha0 hd hw r hr
  have hdeg : (F.map (infSub (K := K) N)).natDegree = n := by rw [hF.natDegree_map, hn]
  rw [eval_eq_sum_range' (by omega : (F.map (infSub (K := K) N)).natDegree < n + 1)] at hr
  simp only [coeff_map] at hr
  set k : ℤ := -((N : ℤ) * d) with hk
  have hc := congrArg (fun z : LaurentSeries K ↦ z.coeff k) hr
  simp only [HahnSeries.coeff_sum, HahnSeries.coeff_zero] at hc
  have hlead : F.coeff n = 1 := by rw [← hn]; exact hF.leadingCoeff
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hc
  -- the middle terms have larger order
  have hmid : ∑ i ∈ Finset.range m, (infSub (K := K) N (F.coeff (i + 1)) * r ^ (i + 1)).coeff k
      = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi' : i + 1 < m + 1 := by have := Finset.mem_range.mp hi; omega
    by_cases hci : F.coeff (i + 1) = 0
    · rw [hci, map_zero, zero_mul, HahnSeries.coeff_zero]
    · refine HahnSeries.coeff_eq_zero_of_lt_order ?_
      have h1 := infSub_ne_zero (K := K) N hN _ hci
      have h2 : r ^ (i + 1) ≠ 0 := pow_ne_zero _ hr0
      rw [HahnSeries.order_mul h1 h2, order_infSub N hN _ hci, HahnSeries.order_pow, nsmul_eq_mul]
      rcases hw (i + 1) (by omega) hi' with h0 | hlt'
      · exact absurd h0 hci
      · have h1 : ((m + 1 : ℕ) : ℤ) * (F.coeff (i + 1)).natDegree < d * (m - i) := by
          have hsub : m + 1 - (i + 1) = m - i := by omega
          rw [hsub] at hlt'
          have := hlt'; rw [← Nat.cast_lt (α := ℤ)] at this
          push_cast [Nat.cast_sub (by omega : i ≤ m)] at this; push_cast; linarith
        have h3 : (N : ℤ) * (((m + 1 : ℕ) : ℤ) * (F.coeff (i + 1)).natDegree) < N * (d * (m - i)) :=
          mul_lt_mul_of_pos_left h1 hNpos
        have key : ((m + 1 : ℕ) : ℤ) * k < ((m + 1 : ℕ) : ℤ) *
            (-((N : ℤ) * (F.coeff (i + 1)).natDegree) + (i + 1 : ℕ) * r.order) := by
          rw [hk]; push_cast at h3 hro ⊢; nlinarith
        exact lt_of_mul_lt_mul_left key hnpos.le
  rw [hmid, zero_add] at hc
  -- the top term
  have htop : (infSub (K := K) N (F.coeff (m + 1)) * r ^ (m + 1)).coeff k = r.leadingCoeff ^ (m + 1) := by
    rw [hlead, map_one, one_mul, ← leadingCoeff_pow_hahn, HahnSeries.leadingCoeff_eq,
      HahnSeries.order_pow, nsmul_eq_mul, hk, hro]
  -- the bottom term
  have hbot : (infSub (K := K) N (F.coeff 0) * r ^ 0).coeff k =
      algebraMap C K (F.coeff 0).leadingCoeff := by
    rw [pow_zero, mul_one, ← leadingCoeff_infSub N hN _ ha0, HahnSeries.leadingCoeff_eq,
      order_infSub N hN _ ha0, hd]
  rw [htop, hbot] at hc
  linear_combination hc

/-- **The leading term at infinity**: the index `j₀` of largest weight gives the order and the
leading coefficient `lc(b_{j₀}) γ^{j₀}` of `W(s⁻ᴺ, r)`. -/
theorem eval_lead_inf (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ n * (F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d)
    (r : LaurentSeries K) (hr : (F.map (infSub (K := K) N)).eval r = 0)
    (W : C[X][X]) (hW0 : W ≠ 0) (hWn : W.natDegree < n) :
    ∃ j0 < n, W.coeff j0 ≠ 0 ∧ wtW n d W = n * (W.coeff j0).natDegree + j0 * d ∧
      (W.map (infSub (K := K) N)).eval r ≠ 0 ∧
      (n : ℤ) * ((W.map (infSub (K := K) N)).eval r).order = -((N : ℤ) * wtW n d W) ∧
      ((W.map (infSub (K := K) N)).eval r).leadingCoeff =
        algebraMap C K (W.coeff j0).leadingCoeff * r.leadingCoeff ^ j0 := by
  classical
  obtain ⟨hr0, hro⟩ := root_order_inf F hF n d N hn hn0 hN ha0 hd hw r hr
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  set t : ℕ → LaurentSeries K := fun j ↦ infSub (K := K) N (W.coeff j) * r ^ j with ht
  have hev : (W.map (infSub (K := K) N)).eval r = ∑ j ∈ Finset.range n, t j := by
    rw [eval_eq_sum_range' (by rw [natDegree_map_eq_of_injective (infSub_injective N hN)]; exact hWn)]
    simp only [coeff_map, ht]
  have hto : ∀ j, W.coeff j ≠ 0 → t j ≠ 0 ∧
      (n : ℤ) * (t j).order = -((N : ℤ) * (n * (W.coeff j).natDegree + j * d : ℕ)) := fun j hj ↦ by
    have h1 := infSub_ne_zero (K := K) N hN _ hj
    have h2 : r ^ j ≠ 0 := pow_ne_zero _ hr0
    refine ⟨mul_ne_zero h1 h2, ?_⟩
    rw [ht]; dsimp only
    rw [HahnSeries.order_mul h1 h2, order_infSub N hN _ hj, HahnSeries.order_pow, nsmul_eq_mul]
    push_cast
    linear_combination (j : ℤ) * hro
  -- the index of largest weight
  set wt : ℕ → ℕ := fun j ↦ n * (W.coeff j).natDegree + j * d with hwt
  have hnemp : ((Finset.range n).filter fun j ↦ W.coeff j ≠ 0).Nonempty :=
    ⟨W.natDegree, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hWn,
      mt leadingCoeff_eq_zero.mp hW0⟩⟩
  obtain ⟨j0, hj0m, hj0max⟩ := Finset.exists_max_image _ wt hnemp
  obtain ⟨hj0r, hj0⟩ := Finset.mem_filter.mp hj0m
  -- weights are distinct
  have hdist : ∀ j ∈ Finset.range n, j ≠ j0 → W.coeff j ≠ 0 → wt j < wt j0 := by
    intro j hj hne hc
    have hle := hj0max j (Finset.mem_filter.mpr ⟨hj, hc⟩)
    refine lt_of_le_of_ne hle fun heq ↦ hne ?_
    have hj' := Finset.mem_range.mp hj
    have hj0' := Finset.mem_range.mp hj0r
    have hmod : j * d ≡ j0 * d [MOD n] := by
      have e1 : wt j % n = j * d % n := by simp only [hwt]; rw [Nat.mul_add_mod]
      have e2 : wt j0 % n = j0 * d % n := by simp only [hwt]; rw [Nat.mul_add_mod]
      unfold Nat.ModEq; rw [← e1, ← e2, heq]
    have := Nat.ModEq.cancel_right_of_coprime (c := d) (by rw [Nat.gcd_comm]; exact hcop.symm) hmod
    exact Nat.ModEq.eq_of_lt_of_lt this hj' hj0'
  have hwtW : wtW n d W = wt j0 := by
    unfold wtW
    refine le_antisymm (Finset.sup_le fun j hj ↦ ?_) ?_
    · by_cases hc : W.coeff j = 0
      · rw [if_pos hc]; exact Nat.zero_le _
      · rw [if_neg hc]; exact hj0max j (Finset.mem_filter.mpr ⟨hj, hc⟩)
    · refine le_trans ?_ (Finset.le_sup hj0r)
      rw [if_neg hj0]
  obtain ⟨ht0, ht0o⟩ := hto j0 hj0
  obtain ⟨hne, hord⟩ := order_sum_of_unique_min (Finset.range n) t j0 hj0r ht0 fun j hj hne ↦ by
    by_cases hc : W.coeff j = 0
    · left; rw [ht]; dsimp only; rw [hc, map_zero, zero_mul]
    · right
      have hlt := hdist j hj hne hc
      have hlt' : (N : ℤ) * (wt j : ℕ) < N * (wt j0 : ℕ) :=
        mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hNpos
      have h2 := (hto j hc).2
      have key : (n : ℤ) * (t j0).order < n * (t j).order := by
        rw [ht0o, h2]; simp only [hwt] at hlt' ⊢; linarith
      exact lt_of_mul_lt_mul_left key hnpos.le
  have hlc := leadingCoeff_sum_unique_min (Finset.range n) t j0 hj0r ht0 fun j hj hne ↦ by
    by_cases hc : W.coeff j = 0
    · left; rw [ht]; dsimp only; rw [hc, map_zero, zero_mul]
    · right
      have hlt := hdist j hj hne hc
      have hlt' : (N : ℤ) * (wt j : ℕ) < N * (wt j0 : ℕ) :=
        mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hNpos
      have h2 := (hto j hc).2
      have key : (n : ℤ) * (t j0).order < n * (t j).order := by
        rw [ht0o, h2]; simp only [hwt] at hlt' ⊢; linarith
      exact lt_of_mul_lt_mul_left key hnpos.le
  rw [hev]
  refine ⟨j0, Finset.mem_range.mp hj0r, hj0, hwtW, hne, by rw [hord, ht0o, hwtW], ?_⟩
  rw [hlc, ht]
  dsimp only
  rw [HahnSeries.leadingCoeff_mul, leadingCoeff_infSub N hN _ hj0, leadingCoeff_pow_hahn]


end Lead

end Curves
