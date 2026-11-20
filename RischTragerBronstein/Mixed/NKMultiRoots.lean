import RischTragerBronstein.Mixed.NKInitForm

/-!
# The roots above infinity from the residual polynomials of the segments

If for weights `σ₀ > σ₁ > ⋯` the initial forms of `∏ (X − r)` are `c Z^{loₖ} ∏_{γ ∈ Γₖ} (Z − γ)`
(`c ≠ 0`, `Γₖ` without repetition and without `0`) with `lo₀ + |Γ₀| = n`,
`loₖ = loₖ₊₁ + |Γₖ₊₁|` and `lo_last = 0`, then every root has order `−σₖ` for some `k` and leading
coefficient in `Γₖ`, and roots with the same order and leading coefficient are equal
(`roots_of_segments`). The counts come from the roots of the initial forms: a factor `Z − [r T^σ]₀`
for each root of order `≥ −σ`, the root `0` exactly for the orders `> −σ` (`roots_prod_initRed`).
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

variable {K : Type*} [Field K]

open Classical in
lemma initRed_ne_zero (σ : ℤ) (r : LaurentSeries K) (hr : r ≠ 0) : initRed σ r ≠ 0 := by
  unfold initRed
  split_ifs
  · exact X_sub_C_ne_zero _
  · rw [Ne, Polynomial.C_eq_zero, neg_eq_zero]
    exact fun h ↦ hr (HahnSeries.coeff_order_eq_zero.mp h)

open Classical in
lemma roots_initRed (σ : ℤ) (r : LaurentSeries K) :
    (initRed σ r).roots = if LowerBd r (-σ) then {r.coeff (-σ)} else 0 := by
  unfold initRed
  split_ifs
  · rw [roots_X_sub_C, coeff_mul_single_one, zero_sub]
  · exact roots_C _

open Classical in
lemma roots_prod_initRed (σ : ℤ) (l : List (LaurentSeries K)) (hl0 : ∀ r ∈ l, r ≠ 0) :
    (l.map (initRed σ)).prod.roots =
      (((l.filter fun r ↦ decide (LowerBd r (-σ))).map fun r ↦ r.coeff (-σ) : List K) :
        Multiset K) := by
  induction l with
  | nil => simp
  | cons r l ih =>
    have hr := hl0 r (List.mem_cons_self ..)
    have hl' : ∀ r' ∈ l, r' ≠ 0 := fun r' h ↦ hl0 r' (List.mem_cons_of_mem _ h)
    have hP : (l.map (initRed σ)).prod ≠ 0 := by
      rw [Ne, List.prod_eq_zero_iff]
      intro h
      obtain ⟨r', hr', h0⟩ := List.mem_map.mp h
      exact initRed_ne_zero σ r' (hl' r' hr') h0
    rw [List.map_cons, List.prod_cons, roots_mul (mul_ne_zero (initRed_ne_zero σ r hr) hP),
      ih hl', roots_initRed]
    by_cases h : LowerBd r (-σ)
    · simp [h]
    · simp [h]

lemma coeff_neg_eq_zero_iff {r : LaurentSeries K} (hr : r ≠ 0) (σ : ℤ) (h : LowerBd r (-σ)) :
    r.coeff (-σ) = 0 ↔ LowerBd r (-σ + 1) := by
  rw [lowerBd_iff_le_order hr] at h ⊢
  constructor
  · intro h0
    by_contra hlt
    push Not at hlt
    have : r.order = -σ := by omega
    rw [← this] at h0
    exact hr (HahnSeries.coeff_order_eq_zero.mp h0)
  · intro h1
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

/-- Equal counts of nested filters: the filters agree. -/
lemma filter_imp_of_length {α : Type*} (l : List α) (p q : α → Bool) (hpq : ∀ x ∈ l, p x → q x)
    (hlen : l.countP q ≤ l.countP p) : ∀ x ∈ l, q x → p x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hpq' : ∀ x ∈ l, p x → q x := fun x h ↦ hpq x (List.mem_cons_of_mem _ h)
    have hmono : l.countP p ≤ l.countP q := List.countP_mono_left hpq'
    rw [List.countP_cons, List.countP_cons] at hlen
    intro x hx hqx
    rcases List.mem_cons.mp hx with rfl | hx
    · by_contra hpx
      have hqa : q x = true := hqx
      simp only [hqa, if_true, Bool.eq_false_iff.mpr hpx, Bool.false_eq_true, if_false] at hlen
      omega
    · by_cases hpa : p a = true
      · have hqa := hpq a (List.mem_cons_self ..) hpa
        simp only [hpa, hqa, if_true] at hlen
        exact ih hpq' (by omega) x hx hqx
      · by_cases hqa : q a = true
        · simp only [hqa, if_true, Bool.eq_false_iff.mpr hpa, Bool.false_eq_true, if_false] at hlen
          omega
        · simp only [Bool.eq_false_iff.mpr hqa, Bool.eq_false_iff.mpr hpa, Bool.false_eq_true,
            if_false] at hlen
          exact ih hpq' (by omega) x hx hqx

open Classical in
/-- **The multiset of the initial form's roots.** -/
lemma initForm_roots (σ : ℤ) (l : List (LaurentSeries K)) (hl0 : ∀ r ∈ l, r ≠ 0) (lo : ℕ)
    (Γ : List K) (c : K) (hc : c ≠ 0)
    (hR : (l.map (initRed σ)).prod = Polynomial.C c * X ^ lo * (Γ.map fun γ ↦ X - Polynomial.C γ).prod) :
    (((l.filter fun r ↦ decide (LowerBd r (-σ))).map fun r ↦ r.coeff (-σ) : List K) :
      Multiset K) = lo • {0} + (Γ : Multiset K) := by
  rw [← roots_prod_initRed σ l hl0, hR, mul_assoc, roots_C_mul _ hc]
  have hX : (X : K[X]) ^ lo ≠ 0 := pow_ne_zero _ X_ne_zero
  have hΓ : (Γ.map fun γ ↦ X - Polynomial.C γ).prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]
    intro h
    obtain ⟨γ, -, h0⟩ := List.mem_map.mp h
    exact X_sub_C_ne_zero γ h0
  rw [roots_mul (mul_ne_zero hX hΓ), roots_X_pow]
  congr 1
  have := roots_multiset_prod_X_sub_C (Γ : Multiset K)
  rw [Multiset.map_coe, Multiset.prod_coe] at this
  exact this

open Classical in
/-- **The roots above infinity from the residual polynomials of the segments.** -/
theorem roots_of_segments (l : List (LaurentSeries K)) (hl0 : ∀ r ∈ l, r ≠ 0) {q : ℕ}
    (σ : Fin (q + 1) → ℤ) (hσ : StrictAnti σ) (lo : Fin (q + 1) → ℕ) (Γ : Fin (q + 1) → List K)
    (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : K) ∉ Γ k)
    (hR : ∀ k, ∃ c : K, c ≠ 0 ∧ (l.map (initRed (σ k))).prod =
      Polynomial.C c * X ^ (lo k) * ((Γ k).map fun γ ↦ X - Polynomial.C γ).prod)
    (htop : lo 0 + (Γ 0).length = l.length)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0) :
    (∀ r ∈ l, ∃ k, r.order = -σ k ∧ r.coeff r.order ∈ Γ k) ∧
    (∀ r ∈ l, ∀ r' ∈ l, r.order = r'.order → r.coeff r.order = r'.coeff r'.order → r = r') := by
  -- the multisets of the roots of the initial forms
  have hM : ∀ k, (((l.filter fun r ↦ decide (LowerBd r (-σ k))).map fun r ↦ r.coeff (-σ k) :
      List K) : Multiset K) = lo k • {0} + (Γ k : Multiset K) := fun k ↦ by
    obtain ⟨c, hc, h⟩ := hR k
    exact initForm_roots (σ k) l hl0 (lo k) (Γ k) c hc h
  -- the counts
  have hcard : ∀ k, l.countP (fun r ↦ decide (LowerBd r (-σ k))) = lo k + (Γ k).length := by
    intro k
    have := congrArg Multiset.card (hM k)
    simp only [Multiset.coe_card, List.length_map, Multiset.card_add, Multiset.card_nsmul,
      Multiset.card_singleton, mul_one] at this
    rw [List.countP_eq_length_filter, this]
  have hzero : ∀ k, l.countP (fun r ↦ decide (LowerBd r (-σ k + 1))) = lo k := by
    intro k
    have h1 := congrArg (Multiset.count (0 : K)) (hM k)
    have hR0 : Multiset.count (0 : K) (lo k • {0} + (Γ k : Multiset K)) = lo k := by
      rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one,
        Multiset.count_eq_zero.mpr (by simpa using (hΓ k).2), add_zero]
    rw [hR0, Multiset.coe_count, List.count_eq_countP, List.countP_map, List.countP_filter] at h1
    rw [← h1]
    refine List.countP_congr fun r hr ↦ ?_
    have hr0 := hl0 r hr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hle : -σ k ≤ -σ k + 1 := by omega
    constructor
    · intro h
      refine ⟨?_, h.mono hle⟩
      exact (coeff_neg_eq_zero_iff hr0 _ (h.mono hle)).mpr h
    · rintro ⟨hc, h0⟩
      exact (coeff_neg_eq_zero_iff hr0 _ h0).mp hc
  -- every root has order `≥ −σ₀`
  have hall0 : ∀ r ∈ l, LowerBd r (-σ 0) := by
    have := hcard 0
    rw [htop] at this
    intro r hr
    have h := List.countP_eq_length.mp this r hr
    simpa using h
  -- no root has order `> −σ_last`
  have hnone : ∀ r ∈ l, ¬ LowerBd r (-σ (Fin.last q) + 1) := by
    have := hzero (Fin.last q)
    rw [hlast] at this
    intro r hr h
    have h' := List.countP_eq_zero.mp this r hr
    simp [h] at h'
  -- between consecutive segments
  have hstep : ∀ k : Fin q, ∀ r ∈ l, LowerBd r (-σ k.castSucc + 1) → LowerBd r (-σ k.succ) := by
    intro k
    have hlt : σ k.succ < σ k.castSucc := hσ Fin.castSucc_lt_succ
    refine fun r hr h ↦ ?_
    have himp : ∀ x ∈ l, decide (LowerBd x (-σ k.succ)) = true →
        decide (LowerBd x (-σ k.castSucc + 1)) = true := fun x _ hx ↦ by
      simp only [decide_eq_true_eq] at hx ⊢
      exact hx.mono (by omega)
    have hcnt : l.countP (fun x ↦ decide (LowerBd x (-σ k.castSucc + 1))) ≤
        l.countP (fun x ↦ decide (LowerBd x (-σ k.succ))) := by
      rw [hzero, hcard, hchain k]
    have := filter_imp_of_length l _ _ himp hcnt r hr (by simpa using h)
    simpa using this
  -- the orders
  have horder : ∀ r ∈ l, ∃ k, r.order = -σ k := by
    intro r hr
    have hr0 := hl0 r hr
    have key : ∀ j (hj : j ≤ q), (∃ k : Fin (q + 1), r.order = -σ k) ∨
        LowerBd r (-σ ⟨j, by omega⟩) := by
      intro j
      induction j with
      | zero => intro _; exact Or.inr (hall0 r hr)
      | succ j ih =>
        intro hj
        rcases ih (by omega) with h | h
        · exact Or.inl h
        · by_cases he : r.order = -σ ⟨j, by omega⟩
          · exact Or.inl ⟨_, he⟩
          · have h1 : LowerBd r (-σ ⟨j, by omega⟩ + 1) := by
              rw [lowerBd_iff_le_order hr0] at h ⊢; omega
            exact Or.inr (hstep ⟨j, by omega⟩ r hr h1)
    rcases key q le_rfl with h | h
    · exact h
    · by_cases he : r.order = -σ (Fin.last q)
      · exact ⟨_, he⟩
      · exfalso
        apply hnone r hr
        rw [lowerBd_iff_le_order hr0] at h ⊢
        have : -σ ⟨q, by omega⟩ = -σ (Fin.last q) := rfl
        omega
  -- the leading coefficients
  have hlead : ∀ k, ∀ r ∈ l, r.order = -σ k → r.coeff r.order ∈ Γ k := by
    intro k r hr ho
    have hr0 := hl0 r hr
    have hin : r.coeff (-σ k) ∈ (((l.filter fun r ↦ decide (LowerBd r (-σ k))).map
        fun r ↦ r.coeff (-σ k) : List K) : Multiset K) :=
      Multiset.mem_coe.mpr (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by
        simpa using (lowerBd_iff_le_order hr0 _).mpr (le_of_eq ho.symm)⟩, rfl⟩)
    rw [hM k, Multiset.mem_add] at hin
    rw [ho]
    rcases hin with h | h
    · exfalso
      have h0 : r.coeff (-σ k) = 0 := by
        rw [Multiset.nsmul_singleton] at h
        exact Multiset.eq_of_mem_replicate h
      rw [← ho] at h0
      exact hr0 (HahnSeries.coeff_order_eq_zero.mp h0)
    · exact Multiset.mem_coe.mp h
  refine ⟨fun r hr ↦ ?_, fun r hr r' hr' ho hc ↦ ?_⟩
  · obtain ⟨k, hk⟩ := horder r hr
    exact ⟨k, hk, hlead k r hr hk⟩
  · obtain ⟨k, hk⟩ := horder r hr
    have hk' : r'.order = -σ k := by rw [← ho, hk]
    -- the non-zero roots of the initial form are without repetition
    set f : LaurentSeries K → K := fun r ↦ r.coeff (-σ k) with hf
    set L := (l.filter fun r ↦ decide (LowerBd r (-σ k))).filter fun r ↦ decide (f r ≠ 0) with hL
    have hnd : (L.map f).Nodup := by
      have h1 := congrArg (Multiset.filter fun x : K ↦ x ≠ 0) (hM k)
      rw [Multiset.filter_add, Multiset.filter_coe, Multiset.filter_coe] at h1
      have h2 : (lo k • ({0} : Multiset K)).filter (fun x : K ↦ x ≠ 0) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro x hx
        rw [Multiset.nsmul_singleton] at hx
        simp [Multiset.eq_of_mem_replicate hx]
      have h3 : (Γ k).filter (fun x : K ↦ decide (x ≠ 0)) = Γ k := by
        rw [List.filter_eq_self]
        intro x hx
        simp only [decide_eq_true_eq]
        exact fun h ↦ (hΓ k).2 (h ▸ hx)
      rw [h2, zero_add, h3] at h1
      have h4 : ((List.map f (List.filter (fun r ↦ decide (LowerBd r (-σ k))) l)).filter
          fun x ↦ decide (x ≠ 0)) = L.map f := by
        rw [hL, List.filter_map]
        rfl
      rw [h4] at h1
      have := (Multiset.coe_nodup).mpr (hΓ k).1
      rw [← h1] at this
      exact Multiset.coe_nodup.mp this
    have hmemL : ∀ x ∈ l, x.order = -σ k → x ∈ L := fun x hx hxo ↦ by
      have hx0 := hl0 x hx
      rw [hL, List.mem_filter, List.mem_filter]
      refine ⟨⟨hx, by simpa using (lowerBd_iff_le_order hx0 _).mpr (le_of_eq hxo.symm)⟩, ?_⟩
      simp only [hf, decide_eq_true_eq]
      rw [← hxo]
      exact fun h ↦ hx0 (HahnSeries.coeff_order_eq_zero.mp h)
    refine List.inj_on_of_nodup_map hnd (hmemL r hr hk) (hmemL r' hr' hk') ?_
    show r.coeff (-σ k) = r'.coeff (-σ k)
    calc r.coeff (-σ k) = r.coeff r.order := by rw [hk]
      _ = r'.coeff r'.order := hc
      _ = r'.coeff (-σ k) := by rw [hk']

open Classical in
/-- **The roots above infinity are distinct** under the hypotheses of `roots_of_segments`. -/
theorem roots_nodup_of_segments (l : List (LaurentSeries K)) (hl0 : ∀ r ∈ l, r ≠ 0) {q : ℕ}
    (σ : Fin (q + 1) → ℤ) (hσ : StrictAnti σ) (lo : Fin (q + 1) → ℕ) (Γ : Fin (q + 1) → List K)
    (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : K) ∉ Γ k)
    (hR : ∀ k, ∃ c : K, c ≠ 0 ∧ (l.map (initRed (σ k))).prod =
      Polynomial.C c * X ^ (lo k) * ((Γ k).map fun γ ↦ X - Polynomial.C γ).prod)
    (htop : lo 0 + (Γ 0).length = l.length)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0) : l.Nodup := by
  obtain ⟨hord, -⟩ := roots_of_segments l hl0 σ hσ lo Γ hΓ hR htop hchain hlast
  rw [List.nodup_iff_count_le_one]
  intro r
  by_cases hr : r ∈ l
  swap
  · rw [List.count_eq_zero_of_not_mem hr]; omega
  obtain ⟨k, hk, -⟩ := hord r hr
  have hr0 := hl0 r hr
  -- the roots of order exactly `−σₖ` have distinct leading coefficients
  have hM := initForm_roots (σ k) l hl0 (lo k) (Γ k) _ (hR k).choose_spec.1 (hR k).choose_spec.2
  set f : LaurentSeries K → K := fun r ↦ r.coeff (-σ k) with hf
  set P : LaurentSeries K → Bool := fun r ↦ decide (f r ≠ 0) && decide (LowerBd r (-σ k)) with hP
  have hnd : ((l.filter P).map f).Nodup := by
    have h1 := congrArg (Multiset.filter fun x : K ↦ x ≠ 0) hM
    rw [Multiset.filter_add, Multiset.filter_coe, Multiset.filter_coe] at h1
    have h2 : (lo k • ({0} : Multiset K)).filter (fun x : K ↦ x ≠ 0) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx
      rw [Multiset.nsmul_singleton] at hx
      simp [Multiset.eq_of_mem_replicate hx]
    have h3 : (Γ k).filter (fun x : K ↦ decide (x ≠ 0)) = Γ k := by
      rw [List.filter_eq_self]
      intro x hx
      simp only [decide_eq_true_eq]
      exact fun h ↦ (hΓ k).2 (h ▸ hx)
    rw [h2, zero_add, h3] at h1
    have h4 : ((List.map f (List.filter (fun r ↦ decide (LowerBd r (-σ k))) l)).filter
        fun x ↦ decide (x ≠ 0)) = (l.filter P).map f := by
      rw [List.filter_map, List.filter_filter]
      rfl
    rw [h4] at h1
    have := (Multiset.coe_nodup).mpr (hΓ k).1
    rw [← h1] at this
    exact Multiset.coe_nodup.mp this
  have hPr : P r = true := by
    simp only [hP, Bool.and_eq_true, decide_eq_true_eq, hf]
    refine ⟨?_, (lowerBd_iff_le_order hr0 _).mpr (le_of_eq hk.symm)⟩
    rw [← hk]
    exact fun h ↦ hr0 (HahnSeries.coeff_order_eq_zero.mp h)
  rw [← List.count_filter hPr]
  exact List.nodup_iff_count_le_one.mp (List.Nodup.of_map f hnd) r

end Curves
