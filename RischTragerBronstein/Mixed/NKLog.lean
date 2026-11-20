import RischTragerBronstein.Mixed.NKExact
import RischTragerBronstein.Mixed.NKLocal
import RischTragerBronstein.Torsion.Degree
import RischTragerBronstein.Algebraic.SuperInfinity

/-!
# The logarithmic part for a curve with a single place at infinity

For `F(x, Y) = Yⁿ + a_{n−1}(x) Yⁿ⁻¹ + … + a₀(x)` with `deg a₀ = d`, `gcd(n, d) = 1` and
`n deg aᵢ < d (n − i)` (a single, totally ramified place at infinity):

* `root_order_inf`: every root above infinity (`x = T^{−N}`) has `n · ord = −N d`;
* the order of `∑ bⱼ yʲ` along any branch above infinity is `−(N/n) max_j (n deg bⱼ + j d)`, the
  same for all branches (weights distinct mod `n`).
-/

open Polynomial HahnSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential LaurentSeries

section Laurent

variable {K : Type*} [Field K]

/-- **A unique term of least order**: the sum does not vanish. -/
lemma sum_ne_zero_of_unique_min {ι : Type*} (s : Finset ι) (t : ι → LaurentSeries K) (i0 : ι)
    (hi0 : i0 ∈ s) (h0 : t i0 ≠ 0) (hlt : ∀ i ∈ s, i ≠ i0 → t i = 0 ∨ (t i0).order < (t i).order) :
    ∑ i ∈ s, t i ≠ 0 := by
  classical
  intro hs
  have hc := congrArg (fun z : LaurentSeries K ↦ z.coeff (t i0).order) hs
  simp only [HahnSeries.coeff_sum, HahnSeries.coeff_zero] at hc
  rw [← Finset.add_sum_erase _ _ hi0, Finset.sum_eq_zero fun i hi ↦ ?_, add_zero] at hc
  · exact h0 (HahnSeries.coeff_order_eq_zero.mp hc)
  · rcases hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi) with h | h
    · rw [h, HahnSeries.coeff_zero]
    · exact HahnSeries.coeff_eq_zero_of_lt_order h

/-- The coefficient of a sum at the order of its unique least term. -/
lemma coeff_sum_unique_min {ι : Type*} (s : Finset ι) (t : ι → LaurentSeries K) (i0 : ι)
    (hi0 : i0 ∈ s) (hlt : ∀ i ∈ s, i ≠ i0 → t i = 0 ∨ (t i0).order < (t i).order) (k : ℤ)
    (hk : k ≤ (t i0).order) : (∑ i ∈ s, t i).coeff k = (t i0).coeff k := by
  classical
  rw [HahnSeries.coeff_sum, ← Finset.add_sum_erase _ _ hi0, Finset.sum_eq_zero fun i hi ↦ ?_,
    add_zero]
  rcases hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi) with h | h
  · rw [h, HahnSeries.coeff_zero]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_le_of_lt hk h)

/-- **The order of a sum with a unique least term.** -/
lemma order_sum_of_unique_min {ι : Type*} (s : Finset ι) (t : ι → LaurentSeries K) (i0 : ι)
    (hi0 : i0 ∈ s) (h0 : t i0 ≠ 0) (hlt : ∀ i ∈ s, i ≠ i0 → t i = 0 ∨ (t i0).order < (t i).order) :
    ∑ i ∈ s, t i ≠ 0 ∧ (∑ i ∈ s, t i).order = (t i0).order := by
  have hne := sum_ne_zero_of_unique_min s t i0 hi0 h0 hlt
  refine ⟨hne, le_antisymm ?_ ?_⟩
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [coeff_sum_unique_min s t i0 hi0 hlt _ le_rfl]
    exact (not_congr HahnSeries.coeff_order_eq_zero).mpr h0
  · by_contra h
    push Not at h
    have hc := (not_congr HahnSeries.coeff_order_eq_zero).mpr hne
    rw [coeff_sum_unique_min s t i0 hi0 hlt _ h.le,
      HahnSeries.coeff_eq_zero_of_lt_order h] at hc
    exact hc rfl

end Laurent

section RootInf

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- **The single place at infinity**: every root above infinity has `n · ord = −N d`. -/
theorem root_order_inf (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ n * (F.coeff i).natDegree < d * (n - i))
    (r : LaurentSeries K) (hr : (F.map (infSub (K := K) N)).eval r = 0) :
    r ≠ 0 ∧ (n : ℤ) * r.order = -((N : ℤ) * d) := by
  classical
  have hdeg : (F.map (infSub (K := K) N)).natDegree = n := by
    rw [hF.natDegree_map, hn]
  rw [eval_eq_sum_range' (by omega : (F.map (infSub (K := K) N)).natDegree < n + 1)] at hr
  simp only [coeff_map] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Finset.sum_eq_single 0 (fun i _ hi ↦ by rw [zero_pow hi, mul_zero]) (by simp)] at hr
    simp only [pow_zero, mul_one] at hr
    exact infSub_ne_zero N hN _ ha0 hr
  refine ⟨hr0, ?_⟩
  set v := r.order
  set t : ℕ → LaurentSeries K := fun i ↦ infSub (K := K) N (F.coeff i) * r ^ i with ht
  have hto : ∀ i, F.coeff i ≠ 0 → t i ≠ 0 ∧ (t i).order = -((N : ℤ) * (F.coeff i).natDegree) + i * v :=
    fun i hi ↦ by
      have h1 := infSub_ne_zero (K := K) N hN _ hi
      have h2 : r ^ i ≠ 0 := pow_ne_zero _ hr0
      refine ⟨mul_ne_zero h1 h2, ?_⟩
      rw [ht]; dsimp only
      rw [HahnSeries.order_mul h1 h2, order_infSub N hN _ hi, HahnSeries.order_pow, nsmul_eq_mul]
  have hlead : F.coeff n = 1 := by rw [← hn]; exact hF.leadingCoeff
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  rcases lt_trichotomy ((n : ℤ) * v) (-((N : ℤ) * d)) with hlt | heq | hgt
  · -- the top term alone has least order
    exfalso
    refine sum_ne_zero_of_unique_min (Finset.range (n + 1)) t n (by simp) ?_ (fun i hi hin ↦ ?_) hr
    · exact (hto n (by rw [hlead]; exact one_ne_zero)).1
    · have hi' : i < n := by have := Finset.mem_range.mp hi; omega
      by_cases hci : F.coeff i = 0
      · left; rw [ht]; dsimp only; rw [hci, map_zero, zero_mul]
      · right
        rw [(hto n (by rw [hlead]; exact one_ne_zero)).2, (hto i hci).2, hlead]
        simp only [natDegree_one, Nat.cast_zero, mul_zero, neg_zero, zero_add]
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [hd]; push_cast; simp only [zero_mul, add_zero]; linarith
        · rcases hw i hipos hi' with h0 | hlt'
          · exact absurd h0 hci
          · -- `n (−N deg aᵢ + i v) > n · n v`
            have h1 : (n : ℤ) * (F.coeff i).natDegree < d * (n - i) := by
              have := hlt'; rw [← Nat.cast_lt (α := ℤ)] at this; push_cast [Nat.cast_sub hi'.le] at this
              exact this
            have h2 : ((n : ℤ) - i) * (n * v) < ((n : ℤ) - i) * (-(N * d)) :=
              mul_lt_mul_of_pos_left hlt (by omega)
            have h3 : (N : ℤ) * (n * (F.coeff i).natDegree) < N * (d * (n - i)) :=
              mul_lt_mul_of_pos_left h1 hNpos
            have key : (n : ℤ) * (n * v) < n * (-((N : ℤ) * (F.coeff i).natDegree) + i * v) := by
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
      rcases Nat.lt_or_ge i n with hi' | hi'
      · rcases hw i (by omega) hi' with h0 | hlt'
        · exact absurd h0 hci
        · have h1 : (n : ℤ) * (F.coeff i).natDegree < d * (n - i) := by
            have := hlt'; rw [← Nat.cast_lt (α := ℤ)] at this; push_cast [Nat.cast_sub hi'.le] at this
            exact this
          have hipos : (0 : ℤ) < i := by exact_mod_cast (Nat.pos_of_ne_zero hi0)
          have h2 : (i : ℤ) * (-(N * d)) < i * (n * v) := mul_lt_mul_of_pos_left hgt hipos
          have h3 : (N : ℤ) * (n * (F.coeff i).natDegree) < N * (d * (n - i)) :=
            mul_lt_mul_of_pos_left h1 hNpos
          have key : (n : ℤ) * (-((N : ℤ) * d) + ((0 : ℕ) : ℤ) * v) <
              n * (-((N : ℤ) * (F.coeff i).natDegree) + i * v) := by
            push_cast; nlinarith
          exact lt_of_mul_lt_mul_left key hnpos.le
      · have hin' : i = n := by omega
        subst hin'
        rw [hlead]
        simp only [natDegree_one, Nat.cast_zero, mul_zero, neg_zero, zero_add, CharP.cast_eq_zero]
        push_cast
        linarith

open Classical in
/-- The weight `max_j (n deg bⱼ + j d)` of `∑ bⱼ Yʲ`. -/
noncomputable def wtW (n d : ℕ) (W : C[X][X]) : ℕ :=
  (Finset.range n).sup fun j ↦ if W.coeff j = 0 then 0 else n * (W.coeff j).natDegree + j * d

/-- **The weighted order at infinity**: along every branch above infinity,
`n · ord W(x, y) = −N · wt(W)`, the same for all branches. -/
theorem eval_order_inf (F : C[X][X]) (hF : F.Monic) (n d N : ℕ) (hn : F.natDegree = n)
    (hn0 : 0 < n) (hN : 0 < N) (ha0 : F.coeff 0 ≠ 0) (hd : (F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ n * (F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d)
    (r : LaurentSeries K) (hr : (F.map (infSub (K := K) N)).eval r = 0)
    (W : C[X][X]) (hW0 : W ≠ 0) (hWn : W.natDegree < n) :
    (W.map (infSub (K := K) N)).eval r ≠ 0 ∧
      (n : ℤ) * ((W.map (infSub (K := K) N)).eval r).order = -((N : ℤ) * wtW n d W) := by
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
  rw [hev]
  exact ⟨hne, by rw [hord, ht0o, hwtW]⟩

end RootInf

section Irr

lemma list_order_mul {K : Type*} [Field K] (n : ℕ) (c : ℤ) (l : List (LaurentSeries K))
    (h : ∀ a ∈ l, (n : ℤ) * a.order = c) : (n : ℤ) * (l.map HahnSeries.order).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, mul_add, h a List.mem_cons_self,
      ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb), List.length_cons]
    push_cast
    ring

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- **Irreducibility from a single place at infinity**: no non-zero `G` of `Y`-degree `< n`
vanishes at a root `y` of `F` (the minimal polynomial of `y` over `C[x]` has degree `k` with
`n ∣ k d` by the orders of its roots above infinity). -/
theorem irr_of_weights [CharZero C] (x y : L) (htr : Transcendental C x) (F : C[X][X]) (hF : F.Monic)
    (n d : ℕ) (hn : F.natDegree = n) (hn0 : 0 < n) (ha0 : F.coeff 0 ≠ 0)
    (hd : (F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ n * (F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (hroot : (F.map (aeval x).toRingHom).eval y = 0)
    (G : C[X][X]) (hG : G.natDegree < n) (hGy : (G.map (aeval x).toRingHom).eval y = 0) :
    G = 0 := by
  classical
  letI : Algebra C[X] L := (aeval x).toRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap C[X] L) := fun p q h ↦ by
    have : aeval x (p - q) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp ((transcendental_iff.mp htr) _ this)
  haveI : Module.IsTorsionFree C[X] L := Module.IsTorsionFree.of_smul_eq_zero fun r m h ↦ by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h0 ↦ hinj (by rw [h0, map_zero])
  have haev : ∀ P : C[X][X], aeval y P = (P.map (aeval x).toRingHom).eval y := fun P ↦ by
    rw [aeval_def, eval_map]; rfl
  have hint : IsIntegral C[X] y := ⟨F, hF, by rw [← aeval_def, haev]; exact hroot⟩
  set μ := minpoly C[X] y with hμ
  have hμm : μ.Monic := minpoly.monic hint
  have hμF : μ ∣ F := minpoly.isIntegrallyClosed_dvd hint (by rw [haev]; exact hroot)
  have hμG : μ ∣ G := minpoly.isIntegrallyClosed_dvd hint (by rw [haev]; exact hGy)
  have hk0 : 0 < μ.natDegree := minpoly.natDegree_pos hint
  by_contra hG0
  have hkG : μ.natDegree ≤ G.natDegree := natDegree_le_of_dvd hμG hG0
  -- the branches above infinity, over an algebraic closure
  let K := AlgebraicClosure C
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap C K).injective
  have hbd : ∀ i, (F.coeff i).natDegree ≤
      (Finset.range (F.natDegree + 1)).sup fun i ↦ (F.coeff i).natDegree := fun i ↦ by
    by_cases hi : i ≤ F.natDegree
    · exact Finset.le_sup (f := fun i ↦ (F.coeff i).natDegree)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), natDegree_zero]; exact Nat.zero_le _
  obtain ⟨N, hN, l, -, hs, -⟩ := split_inf (K := K) F hF _ hbd
  have hNp := Nat.pos_of_ne_zero hN
  set g := infSub (C := C) (K := K) N with hg
  have hFs : Splits (F.map g) := by
    rw [hs]
    exact Splits.listProd fun f hf ↦ by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hf
      exact Splits.X_sub_C r
  have hF0 : F.map g ≠ 0 := (hF.map g).ne_zero
  have hμd : μ.map g ∣ F.map g := Polynomial.map_dvd g hμF
  have hμs : Splits (μ.map g) := hFs.of_dvd hF0 hμd
  have hμmg : (μ.map g).Monic := hμm.map g
  have hdegμ : (μ.map g).natDegree = μ.natDegree := hμm.natDegree_map g
  -- every root has order `−N d / n`
  have hroots : ∀ a ∈ (μ.map g).roots, a ≠ 0 ∧ (n : ℤ) * a.order = -((N : ℤ) * d) := by
    intro a ha
    have hra : (F.map g).eval a = 0 :=
      eval_eq_zero_of_dvd_of_eval_eq_zero hμd ((mem_roots hμmg.ne_zero).mp ha)
    exact root_order_inf F hF n d N hn hn0 hNp ha0 hd hw a hra
  -- the constant coefficient
  have hc0 := hμs.coeff_zero_eq_prod_roots_of_monic hμmg
  rw [coeff_map, hdegμ, ← Multiset.prod_toList] at hc0
  have hl0 : ∀ a ∈ (μ.map g).roots.toList, a ≠ 0 := fun a ha ↦
    (hroots a (Multiset.mem_toList.mp ha)).1
  have hprod : ((μ.map g).roots.toList).prod ≠ 0 := List.prod_ne_zero fun h0 ↦ hl0 0 h0 rfl
  have hsign : ((-1 : LaurentSeries K) ^ μ.natDegree) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hμ0 : μ.coeff 0 ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hc0
    exact mul_ne_zero hsign hprod hc0.symm
  have ho := congrArg HahnSeries.order hc0
  rw [order_infSub N hNp _ hμ0, HahnSeries.order_mul hsign hprod, HahnSeries.order_pow,
    HahnSeries.order_neg, HahnSeries.order_one, smul_zero, zero_add,
    CurveData.order_list_prod _ hl0] at ho
  have hsum := list_order_mul n (-((N : ℤ) * d)) _ fun a ha ↦
    (hroots a (Multiset.mem_toList.mp ha)).2
  rw [Multiset.length_toList, ← hμs.natDegree_eq_card_roots, hdegμ, ← ho] at hsum
  -- `n deg μ₀ = k d`, so `n ∣ k`
  have hkd : n * (μ.coeff 0).natDegree = μ.natDegree * d := by
    have hNpos : (0 : ℤ) < N := by exact_mod_cast hNp
    have : (N : ℤ) * (n * (μ.coeff 0).natDegree) = N * (μ.natDegree * d) := by linarith
    exact_mod_cast mul_left_cancel₀ hNpos.ne' this
  have hdvd : n ∣ μ.natDegree := (Nat.Coprime.dvd_of_dvd_mul_right hcop ⟨_, hkd.symm⟩)
  have := Nat.le_of_dvd hk0 hdvd
  omega

end Irr

section Unit

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

lemma coeff_zero_list_prod {R : Type*} [CommRing R] (l : List R) :
    ((l.map fun r ↦ X - Polynomial.C r).prod).coeff 0 = (l.map fun r ↦ -r).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_coeff_zero, ih, List.map_cons, List.prod_cons]
    simp

lemma order_inv_nk (z : LaurentSeries K) (hz : z ≠ 0) : z⁻¹.order = -z.order := by
  have h := congrArg HahnSeries.order (mul_inv_cancel₀ hz)
  rw [HahnSeries.order_mul hz (inv_ne_zero hz), HahnSeries.order_one] at h
  linarith

lemma infSub_mapK (N : ℕ) (P : C[X]) :
    infSub (C := K) (K := K) N (P.map (algebraMap C K)) = infSub N P := by
  simp only [infSub, coe_eval₂RingHom, eval₂_map]
  rfl

lemma infSub_CK (N : ℕ) (c : K) : infSub (C := K) (K := K) N (Polynomial.C c) = HahnSeries.C c := by
  simp only [infSub, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

/-- **A root in `K⸨X⸩` of a non-zero polynomial over an algebraically closed `K` is a constant.** -/
lemma const_of_root [IsAlgClosed K] (μ : K[X]) (hμ : μ ≠ 0) (z : LaurentSeries K)
    (hz : (μ.map HahnSeries.C).eval z = 0) : ∃ c : K, z = HahnSeries.C c := by
  classical
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := K) (p := μ))
  rw [← hsplit, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C,
    Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.map_map, Multiset.map_map] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd ((map_eq_zero_iff _ HahnSeries.C_injective).mp h)
      (leadingCoeff_ne_zero.mpr hμ)
  · obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
    refine ⟨a, ?_⟩
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      eval_sub, eval_X, eval_C] at ha
    exact sub_eq_zero.mp ha

namespace CurveData

variable (S : CurveData C L)

/-- `u = W(x, y)/Q(x)` with `deg_Y W < deg F`. -/
lemma exists_repr_lt (u : C⟮S.x⟯⟮S.y⟯) (hF1 : S.F ≠ 1) :
    ∃ (W : C[X][X]) (Q : C[X]), Q ≠ 0 ∧ (u : L) * aeval S.x Q = S.evXY W ∧
      W.natDegree < S.F.natDegree := by
  obtain ⟨W0, Q, hQ, hWQ0⟩ := S.exists_repr u
  refine ⟨W0 %ₘ S.F, Q, hQ, ?_, natDegree_modByMonic_lt W0 S.monic hF1⟩
  rw [hWQ0]
  conv_lhs => rw [← modByMonic_add_div W0 S.F]
  simp only [evXY, Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul]
  rw [S.root, zero_mul, add_zero]

/-- **A function that is constant along one branch above infinity is a constant** (single place
at infinity). -/
theorem mem_const_of_branch_inf (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (u : C⟮S.x⟯⟮S.y⟯) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (c : K)
    (hc : S.embG (infSub N) (infSub_injective N hN) r hr u = HahnSeries.C c) :
    ∃ c' : C, (u : L) = algebraMap C L c' := by
  classical
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt u hF1
  rw [hn] at hWn
  have hinj := infSub_injective (C := C) (K := K) N hN
  have he := S.eval_W_branch (infSub N) hinj r hr u W Q hWQ
  rw [hc] at he
  set φ : C[X] →+* K[X] := Polynomial.mapRingHom (algebraMap C K) with hφ
  have hφi : Function.Injective φ := Polynomial.map_injective _ (algebraMap C K).injective
  have hcomp : (infSub (C := K) (K := K) N).comp φ = infSub N :=
    RingHom.ext fun P ↦ infSub_mapK N P
  set W' : K[X][X] := W.map φ - Polynomial.C (Polynomial.C c * Q.map (algebraMap C K)) with hW'
  have hev : (W'.map (infSub (C := K) (K := K) N)).eval r = 0 := by
    rw [hW', Polynomial.map_sub, Polynomial.map_map, hcomp, eval_sub, Polynomial.map_C, eval_C,
      he, map_mul, infSub_CK, infSub_mapK, sub_self]
  -- the curve over `K`
  set F' : K[X][X] := S.F.map φ with hF'
  have hF'c : ∀ i, F'.coeff i = (S.F.coeff i).map (algebraMap C K) := fun i ↦ by
    rw [hF', coeff_map]; rfl
  have hdegφ : ∀ P : C[X], (φ P).natDegree = P.natDegree := fun P ↦
    natDegree_map_eq_of_injective (algebraMap C K).injective P
  have hW'0 : W' = 0 := by
    by_contra hne
    have hW'n : W'.natDegree < n := by
      rw [hW']
      refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (natDegree_map_le) hWn
      · rw [natDegree_C]; exact hn0
    have hr' : (F'.map (infSub (C := K) (K := K) N)).eval r = 0 := by
      rw [hF', Polynomial.map_map, hcomp, hr]
    refine (eval_order_inf F' (S.monic.map φ) n d N (by rw [hF', S.monic.natDegree_map, hn]) hn0 hN
      (by rw [hF'c]; exact (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr ha0)
      (by rw [hF'c]; exact (hdegφ _).trans hd)
      (fun i hi hin ↦ by
        rw [hF'c, show ((S.F.coeff i).map (algebraMap C K)).natDegree = (S.F.coeff i).natDegree
          from hdegφ _]
        rcases hw i hi hin with h | h
        · left; rw [h, Polynomial.map_zero]
        · right; exact h)
      hcop r hr' W' hne hW'n).1 hev
  -- read off the coefficients
  have hcoef : ∀ j, φ (W.coeff j) = if j = 0 then Polynomial.C c * Q.map (algebraMap C K) else 0 :=
    fun j ↦ by
      have := congrArg (fun P ↦ P.coeff j) hW'0
      simp only [hW', Polynomial.coeff_sub, coeff_map, coeff_C, Polynomial.coeff_zero] at this
      rw [sub_eq_zero] at this
      rw [this]
  have hQ0 : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  set c' : C := (W.coeff 0).leadingCoeff / Q.leadingCoeff with hc'
  have h0 := hcoef 0
  rw [if_pos rfl] at h0
  have hcc : c = algebraMap C K c' := by
    have hl := congrArg Polynomial.leadingCoeff h0
    rw [hφ, coe_mapRingHom, leadingCoeff_map_of_injective (algebraMap C K).injective,
      Polynomial.leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_map_of_injective (algebraMap C K).injective] at hl
    rw [hc', map_div₀, hl]
    field_simp [(map_ne_zero_iff _ (algebraMap C K).injective).mpr hQ0]
  have hW0 : W.coeff 0 = Polynomial.C c' * Q := by
    apply hφi
    rw [h0, hcc, map_mul, hφ, coe_mapRingHom, Polynomial.map_C]
  have hWC : W = Polynomial.C (W.coeff 0) := by
    refine Polynomial.ext fun j ↦ ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [coeff_C_zero]
    · rw [coeff_C, if_neg hj.ne']
      apply hφi
      rw [hcoef j, if_neg hj.ne', map_zero]
  refine ⟨c', ?_⟩
  have hx0 : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
  rw [hWC, hW0] at hWQ
  rw [evXY, Polynomial.map_C, eval_C] at hWQ
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, aeval_C] at hWQ
  exact mul_right_cancel₀ hx0 hWQ

variable [IsAlgClosed K] [CharZero K]

/-- A function without finite poles has order `≤ 0` along some branch above infinity. -/
lemma exists_order_nonpos_inf (f : C⟮S.x⟯⟮S.y⟯) (hf : f ≠ 0) (hfin : S.RegularFinite K f)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (hl0 : l ≠ []) :
    ∃ r, ∃ hr : r ∈ l, (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
      (S.root_of_mem hl hr) f).order ≤ 0 := by
  classical
  obtain ⟨W, Q, M, hQ, hWQ, hM, hPM, -⟩ :=
    S.integral_of_regular_dataG (S.hasBranches (K := K)) f hfin
  have hinj := infSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN)
  obtain ⟨v, hv, hMg⟩ := S.M_map_split f W Q M hQ hWQ hPM (infSub (K := K) N) hinj l hl
  by_contra hcon
  push Not at hcon
  have hv0 : ∀ z ∈ l.map (fun r ↦ -v r), z ≠ 0 := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    rw [hv r hr, neg_ne_zero]
    exact (map_ne_zero_iff _ (S.embG _ _ r _).injective).mpr hf
  have hc := congrArg (fun P ↦ P.coeff 0) hMg
  simp only [coeff_map] at hc
  rw [show (l.map fun r ↦ (X - Polynomial.C (v r) : (LaurentSeries K)[X])) =
    ((l.map v).map fun s ↦ X - Polynomial.C s) by rw [List.map_map]; rfl,
    coeff_zero_list_prod, List.map_map] at hc
  have hc2 : infSub (K := K) N (M.coeff 0) = (l.map fun r ↦ -v r).prod := by rw [hc]; rfl
  have hprod : (l.map fun r ↦ -v r).prod ≠ 0 := List.prod_ne_zero (fun h0 ↦ hv0 0 h0 rfl)
  have hM0 : M.coeff 0 ≠ 0 := fun h ↦ hprod (by rw [← hc2, h, map_zero])
  have ho := congrArg HahnSeries.order hc2
  rw [order_infSub N (Nat.pos_of_ne_zero hN) _ hM0, order_list_prod _ hv0, List.map_map] at ho
  have hpos : 0 < (l.map (HahnSeries.order ∘ fun r ↦ -v r)).sum := by
    refine List.sum_pos _ (fun z hz ↦ ?_) (by simpa using hl0)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    simp only [Function.comp_apply, HahnSeries.order_neg]
    rw [hv r hr]
    exact hcon r hr
  have : (0 : ℤ) ≤ N * (M.coeff 0).natDegree := by positivity
  omega

/-- **Units at the finite places are algebraic over the constants** (single place at infinity):
a function with order `0` along every finite branch satisfies a monic equation over `C`. -/
theorem algebraic_of_unit_inf (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hfin : ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u).order = 0) :
    ∃ M0 : C[X], M0.Monic ∧ aeval (u : L) M0 = 0 := by
  classical
  have hreg : S.RegularFinite K u := fun a N hN l hl r hr ↦ (hfin a N hN l hl r hr).ge
  have hregI : S.RegularFinite K u⁻¹ := fun a N hN l hl r hr ↦ by
    rw [map_inv₀, order_inv_nk _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr hu),
      hfin a N hN l hl r hr, neg_zero]
  -- `u = W / Q` with `deg_Y W < n`
  obtain ⟨W0, Q, hQ, hWQ0⟩ := S.exists_repr u
  set W := W0 %ₘ S.F with hW
  have hWQ : (u : L) * aeval S.x Q = S.evXY W := by
    rw [hWQ0]
    conv_lhs => rw [← modByMonic_add_div W0 S.F]
    simp only [evXY, Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul]
    rw [S.root, zero_mul, add_zero]
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  have hWn : W.natDegree < n := by rw [← hn]; exact natDegree_modByMonic_lt W0 S.monic hF1
  refine S.algebraic_of_regularG (S.hasBranches (K := K)) (S.hasBranchesInf (K := K)) u hreg ?_
  intro N hN l hl r hr
  have hNp := Nat.pos_of_ne_zero hN
  have hinj := infSub_injective (C := C) (K := K) N hNp
  -- all branches above infinity give the same order
  have hsame : ∀ r (hr : r ∈ l),
      (n : ℤ) * (S.embG (infSub N) hinj r (S.root_of_mem hl hr) u).order =
        -((N : ℤ) * wtW n d W) + n * (N * Q.natDegree) := by
    intro r hr
    have he := S.eval_W_branch (infSub N) hinj r (S.root_of_mem hl hr) u W Q hWQ
    have hE0 : S.embG (infSub N) hinj r (S.root_of_mem hl hr) u ≠ 0 :=
      (map_ne_zero_iff _ (RingHom.injective _)).mpr hu
    have hQ0 := infSub_ne_zero (K := K) N hNp Q hQ
    have hW0 : W ≠ 0 := fun h ↦ by
      rw [h, Polynomial.map_zero, eval_zero] at he
      exact mul_ne_zero hE0 hQ0 he.symm
    obtain ⟨-, ho⟩ := eval_order_inf S.F S.monic n d N hn hn0 hNp ha0 hd hw hcop r
      (S.root_of_mem hl hr) W hW0 hWn
    rw [he, HahnSeries.order_mul hE0 hQ0, order_infSub N hNp _ hQ] at ho
    linear_combination ho
  have hl0 : l ≠ [] := by
    intro h
    have := congrArg natDegree hl
    rw [h, S.monic.natDegree_map, hn] at this
    simp at this
    omega
  obtain ⟨r1, hr1, h1⟩ := S.exists_order_nonpos_inf u hu hreg N hN l hl hl0
  obtain ⟨r2, hr2, h2⟩ := S.exists_order_nonpos_inf u⁻¹ (inv_ne_zero hu) hregI N hN l hl hl0
  rw [map_inv₀, order_inv_nk _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr hu)] at h2
  have e1 := hsame r1 hr1
  have e2 := hsame r2 hr2
  have e := hsame r hr
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  nlinarith

/-- The expansion of a constant. -/
lemma embG_algebraMapC (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C K c))
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    (S.embG g hg Y hY).comp (algebraMap C C⟮S.x⟯⟮S.y⟯) = (HahnSeries.C).comp (algebraMap C K) := by
  letI := algebraAdjoinSimple (F := C) S.x
  refine RingHom.ext fun c ↦ ?_
  have e : algebraMap C C⟮S.x⟯⟮S.y⟯ c =
      algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ (Polynomial.C c)) :=
    Subtype.ext (by
      show algebraMap C L c = ((algebraMap C[X] C⟮S.x⟯ (Polynomial.C c) : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple, aeval_C])
  rw [RingHom.comp_apply, e, S.embG_algebraMap, S.embXG_algebraMap, hgC]
  rfl

/-- **Units at the finite places are constants** (single place at infinity). -/
theorem mem_const_of_unit_inf (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hfin : ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u).order = 0) :
    ∃ c' : C, (u : L) = algebraMap C L c' := by
  classical
  obtain ⟨M0, hM0m, hM0⟩ := S.algebraic_of_unit_inf n d hn hn0 ha0 hd hw hcop u hu hfin
  obtain ⟨N, hN, l, hlen, hl⟩ := S.hasBranchesInf (K := K)
  have hNp := Nat.pos_of_ne_zero hN
  obtain ⟨r, hr⟩ : ∃ r, r ∈ l := List.exists_mem_of_length_pos (by rw [hlen, hn]; exact hn0)
  have hroot := S.root_of_mem hl hr
  have h1 : aeval u M0 = 0 := by
    apply (algebraMap (C⟮S.x⟯⟮S.y⟯) L).injective
    have e : (algebraMap (C⟮S.x⟯⟮S.y⟯) L).comp (algebraMap C (C⟮S.x⟯⟮S.y⟯)) = algebraMap C L :=
      RingHom.ext fun c ↦ rfl
    rw [map_zero, aeval_def, hom_eval₂, e, ← aeval_def]
    exact hM0
  have h2 := congrArg (S.embG (infSub N) (infSub_injective N hNp) r hroot) h1
  rw [map_zero, aeval_def, hom_eval₂, S.embG_algebraMapC (infSub N) (infSub_injective N hNp)
    (fun c ↦ by simp only [infSub, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]) r hroot,
    ← eval_map, ← Polynomial.map_map] at h2
  obtain ⟨c, hc⟩ := const_of_root _ ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr
    hM0m.ne_zero) _ h2
  exact S.mem_const_of_branch_inf n d hn hn0 ha0 hd hw hcop u N hNp r hroot c hc

end CurveData

end Unit

end Curves

namespace Curves

namespace CurveData

open Differential

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **The logarithms lie in the base** (general curve with a single place at infinity, every
finite place good): if `f = v′ + ∑ dⱼ wⱼ′/wⱼ` with `ℚ`-independent constants `dⱼ` and `f` has no
pole at any finite place, then every `wⱼ` is a constant of `C`. -/
theorem logs_in_base_inf (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (n dd : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = dd)
    (hw' : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < dd * (n - i))
    (hcop : Nat.Coprime n dd) (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (hind : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (hreg : S.RegularFinite K ⟨f, hf⟩) :
    ∀ j < k, ∃ c : C, w j = algebraMap C L c := by
  intro j hj
  have hu0 : (⟨w j, (hw j hj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦
    (hw j hj).2 (congrArg Subtype.val h)
  exact S.mem_const_of_unit_inf (K := K) n dd hn hn0 ha0 hd hw' hcop _ hu0
    fun a N hN l hl r hr ↦ S.logs_zero_branchW ω hx hK k d w hw hind v f hv hf heq a (hnd a) N
      (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (Or.inr (hreg a N hN l hl r hr)) j hj

end CurveData

end Curves
