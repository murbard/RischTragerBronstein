import RischTragerBronstein.Mixed.NKLog
import RischTragerBronstein.Torsion.ValidExist

/-!
# A single place above `x = 0`

The analogue at `x = 0` of `root_order_inf`/`eval_order_inf`: if `F = Yⁿ + ∑ aᵢ(x) Yⁱ` has
`ord₀ a₀ = d` with `gcd(n, d) = 1` and `n ord₀ aᵢ > d (n − i)` for `0 < i < n` (orders of vanishing
at `0`), then above `x = 0` there is a single, totally ramified place: along every branch
`x = Tᴺ`, `n · ord r = N d` (`root_order_zero`), and for `W = ∑_{j<n} bⱼ Yʲ`,
`n · ord W(x, r) = N · wt₀(W)` with `wt₀(W) = min_j (n ord₀ bⱼ + j d)`, the same for all branches
(`eval_order_zero`).
-/

open Polynomial HahnSeries LaurentSeries Differential

set_option linter.unusedSectionVars false

namespace Curves

section RootZero

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The order of `P(Tᴺ)`. -/
lemma order_branchSub_zero (N : ℕ) (hN : 0 < N) (P : C[X]) (hP : P ≠ 0) :
    (branchSub (K := K) N 0 P).order = ((N * P.natTrailingDegree : ℕ) : ℤ) := by
  rw [order_branchSub N hN 0 P hP, rootMultiplicity_eq_natTrailingDegree',
    natTrailingDegree_map_inj _ (algebraMap C K).injective]

lemma branchSub_zero_ne_zero (N : ℕ) (hN : 0 < N) (P : C[X]) (hP : P ≠ 0) :
    branchSub (K := K) N 0 P ≠ 0 :=
  (map_ne_zero_iff _ (branchSub_injective N hN 0)).mpr hP

/-- **The single place above `0`**: every root above `x = 0` has `n · ord = N d`. -/
theorem root_order_zero (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natTrailingDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ d * (n - i) < n * (F.coeff i).natTrailingDegree)
    (r : LaurentSeries K) (hr : (F.map (branchSub (K := K) N 0)).eval r = 0) :
    r ≠ 0 ∧ (n : ℤ) * r.order = (N : ℤ) * d := by
  classical
  have hdeg : (F.map (branchSub (K := K) N 0)).natDegree = n := by
    rw [hF.natDegree_map, hn]
  rw [eval_eq_sum_range' (by omega : (F.map (branchSub (K := K) N 0)).natDegree < n + 1)] at hr
  simp only [coeff_map] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Finset.sum_eq_single 0 (fun i _ hi ↦ by rw [zero_pow hi, mul_zero]) (by simp)] at hr
    simp only [pow_zero, mul_one] at hr
    exact branchSub_zero_ne_zero N hN _ ha0 hr
  refine ⟨hr0, ?_⟩
  set v := r.order
  set t : ℕ → LaurentSeries K := fun i ↦ branchSub (K := K) N 0 (F.coeff i) * r ^ i with ht
  have hto : ∀ i, F.coeff i ≠ 0 → t i ≠ 0 ∧
      (t i).order = ((N : ℤ) * (F.coeff i).natTrailingDegree) + i * v := fun i hi ↦ by
    have h1 := branchSub_zero_ne_zero (K := K) N hN _ hi
    have h2 : r ^ i ≠ 0 := pow_ne_zero _ hr0
    refine ⟨mul_ne_zero h1 h2, ?_⟩
    rw [ht]; dsimp only
    rw [HahnSeries.order_mul h1 h2, order_branchSub_zero N hN _ hi, HahnSeries.order_pow,
      nsmul_eq_mul]
    push_cast; ring
  have hlead : F.coeff n = 1 := by rw [← hn]; exact hF.leadingCoeff
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hcast : ∀ i, 0 < i → i < n → F.coeff i ≠ 0 →
      (d : ℤ) * (n - i) < n * (F.coeff i).natTrailingDegree := fun i hi hin hc ↦ by
    rcases hw i hi hin with h0 | h1
    · exact absurd h0 hc
    · have := h1; rw [← Nat.cast_lt (α := ℤ)] at this; push_cast [Nat.cast_sub hin.le] at this
      exact this
  rcases lt_trichotomy ((n : ℤ) * v) ((N : ℤ) * d) with hlt | heq | hgt
  · -- the top term alone has least order
    exfalso
    refine sum_ne_zero_of_unique_min (Finset.range (n + 1)) t n (by simp) ?_ (fun i hi hin ↦ ?_) hr
    · exact (hto n (by rw [hlead]; exact one_ne_zero)).1
    · have hi' : i < n := by have := Finset.mem_range.mp hi; omega
      by_cases hci : F.coeff i = 0
      · left; rw [ht]; dsimp only; rw [hci, map_zero, zero_mul]
      · right
        rw [(hto n (by rw [hlead]; exact one_ne_zero)).2, (hto i hci).2, hlead]
        simp only [natTrailingDegree_one, Nat.cast_zero, mul_zero, zero_add]
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [hd]; push_cast; simp only [zero_mul, add_zero]
          exact lt_of_mul_lt_mul_left (by nlinarith) hnpos.le
        · have h1 := hcast i hipos hi' hci
          have h2 : ((n : ℤ) - i) * (n * v) < ((n : ℤ) - i) * (N * d) :=
            mul_lt_mul_of_pos_left hlt (by omega)
          have h3 : (N : ℤ) * (d * (n - i)) < N * (n * (F.coeff i).natTrailingDegree) :=
            mul_lt_mul_of_pos_left h1 hNpos
          have key : (n : ℤ) * (n * v) < n * ((N : ℤ) * (F.coeff i).natTrailingDegree + i * v) := by
            nlinarith
          exact lt_of_mul_lt_mul_left key hnpos.le
  · exact heq
  · -- the constant term alone has least order
    exfalso
    refine sum_ne_zero_of_unique_min (Finset.range (n + 1)) t 0 (by simp) (hto 0 ha0).1
      (fun i hi hi0 ↦ ?_) hr
    by_cases hci : F.coeff i = 0
    · left; rw [ht]; dsimp only; rw [hci, map_zero, zero_mul]
    · right
      rw [(hto 0 ha0).2, (hto i hci).2, hd]
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have hipos : (0 : ℤ) < i := by exact_mod_cast (Nat.pos_of_ne_zero hi0)
      rcases Nat.lt_or_ge i n with hi' | hi'
      · have h1 := hcast i (Nat.pos_of_ne_zero hi0) hi' hci
        have h2 : (i : ℤ) * (N * d) < i * (n * v) := mul_lt_mul_of_pos_left hgt hipos
        have h3 : (N : ℤ) * (d * (n - i)) < N * (n * (F.coeff i).natTrailingDegree) :=
          mul_lt_mul_of_pos_left h1 hNpos
        have key : (n : ℤ) * ((N : ℤ) * d + ((0 : ℕ) : ℤ) * v) <
            n * ((N : ℤ) * (F.coeff i).natTrailingDegree + i * v) := by
          push_cast; nlinarith
        exact lt_of_mul_lt_mul_left key hnpos.le
      · have hin' : i = n := by omega
        subst hin'
        rw [hlead]
        simp only [natTrailingDegree_one, Nat.cast_zero, mul_zero, zero_add, CharP.cast_eq_zero]
        push_cast
        nlinarith

open Classical in
/-- The weight `min_j (n ord₀ bⱼ + j d)` of `∑ bⱼ Yʲ` (over the non-zero `bⱼ`, `j < n`). -/
noncomputable def wt0W (n d : ℕ) (W : C[X][X]) : ℕ :=
  if h : ((Finset.range n).filter fun j ↦ W.coeff j ≠ 0).Nonempty then
    ((Finset.range n).filter fun j ↦ W.coeff j ≠ 0).inf' h fun j ↦
      n * (W.coeff j).natTrailingDegree + j * d
  else 0

/-- **The weighted order above `0`**: along every branch `x = Tᴺ`,
`n · ord W(x, y) = N · wt₀(W)`, the same for all branches. -/
theorem eval_order_zero (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natTrailingDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ d * (n - i) < n * (F.coeff i).natTrailingDegree)
    (hcop : Nat.Coprime n d)
    (r : LaurentSeries K) (hr : (F.map (branchSub (K := K) N 0)).eval r = 0)
    (W : C[X][X]) (hW0 : W ≠ 0) (hWn : W.natDegree < n) :
    (W.map (branchSub (K := K) N 0)).eval r ≠ 0 ∧
      (n : ℤ) * ((W.map (branchSub (K := K) N 0)).eval r).order = (N : ℤ) * wt0W n d W := by
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
  rw [hev]
  exact ⟨hne, by rw [hord, ht0o, hwt0]⟩

end RootZero

end Curves
