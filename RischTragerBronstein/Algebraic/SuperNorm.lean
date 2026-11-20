import RischTragerBronstein.Algebraic.SuperInfinity

/-!
# The norm on a superelliptic function field

For a primitive `n`-th root of unity `ζ ∈ C`, the conjugations `σⱼ : y ↦ ζʲ y` generate the
automorphism group of `C⟮x⟯⟮y⟯ / C⟮x⟯`.

* `conj_comp`: `σ_a ∘ σ_b = σ_{ab}`;
* `mem_base_of_invariant`: a `σ_ζ`-invariant element lies in `C⟮x⟯`;
* `normS w = ∏ⱼ σⱼ w` lies in `C⟮x⟯` (`normS_mem`).
-/

open Polynomial IntermediateField HahnSeries

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- Two sums whose terms have the same, pairwise distinct, orders have the same order. -/
lemma orderTop_sum_congr {ι : Type*} (s : Finset ι) (t t' : ι → K⸨X⸩)
    (h : ∀ i ∈ s, (t' i).orderTop = (t i).orderTop)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (t i).orderTop ≠ (t j).orderTop) :
    (∑ i ∈ s, t' i).orderTop = (∑ i ∈ s, t i).orderTop := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨i0, hi0, hmin⟩ := s.exists_min_image (fun i ↦ (t i).orderTop) hne
  have hlt : ∀ i ∈ s, i ≠ i0 → (t i0).orderTop < (t i).orderTop := fun i hi hii0 ↦
    lt_of_le_of_ne (hmin i hi) (hd i0 hi0 i hi (Ne.symm hii0))
  rw [orderTop_sum_eq s t hi0 hlt, orderTop_sum_eq s t' hi0 (fun i hi hii0 ↦ by
    rw [h i hi, h i0 hi0]; exact hlt i hi hii0), h i0 hi0]

lemma orderTop_prod {ι : Type*} (s : Finset ι) (t : ι → K⸨X⸩) :
    (∏ i ∈ s, t i).orderTop = ∑ i ∈ s, (t i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, HahnSeries.orderTop_mul, ih]

end LaurentSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K]

variable (S : SuperData C L)

lemma conj_gen' (ζ : C) (hζ : ζ ^ S.n = 1) :
    S.conj ζ hζ (AdjoinSimple.gen C⟮S.x⟯ S.y) = S.cst ζ * AdjoinSimple.gen C⟮S.x⟯ S.y :=
  S.conj_gen ζ hζ

lemma conj_congr {a b : C} (ha : a ^ S.n = 1) (hb : b ^ S.n = 1) (h : a = b) :
    S.conj a ha = S.conj b hb := by
  subst h; rfl

lemma conj_comp (a b : C) (ha : a ^ S.n = 1) (hb : b ^ S.n = 1) :
    (S.conj a ha).comp (S.conj b hb) = S.conj (a * b) (by rw [mul_pow, ha, hb, one_mul]) := by
  refine S.ringHom_ext_XY _ _ (fun c ↦ ?_) ?_
  · rw [RingHom.comp_apply, S.conj_algebraMap, S.conj_algebraMap, S.conj_algebraMap]
  · rw [RingHom.comp_apply, S.conj_gen', map_mul, S.conj_cst, S.conj_gen', S.conj_gen', S.cst_mul]
    ring

lemma conj_one : S.conj 1 (one_pow _) = RingHom.id _ := by
  refine S.ringHom_ext_XY _ _ (fun c ↦ ?_) ?_
  · rw [S.conj_algebraMap, RingHom.id_apply]
  · rw [S.conj_gen', RingHom.id_apply, show S.cst 1 = 1 from Subtype.ext (by simp [cst]), one_mul]

lemma conj_pow_invariant (ζ : C) (hζ : ζ ^ S.n = 1) (w : C⟮S.x⟯⟮S.y⟯) (hw : S.conj ζ hζ w = w)
    (j : ℕ) : S.conj (ζ ^ j) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]) w = w := by
  induction j with
  | zero =>
    rw [S.conj_congr _ (one_pow _) (pow_zero ζ), S.conj_one, RingHom.id_apply]
  | succ j ih =>
    have hj : (ζ ^ j) ^ S.n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [S.conj_congr (a := ζ ^ (j + 1)) (b := ζ * ζ ^ j) _ (by rw [mul_pow, hζ, hj, one_mul])
      (by rw [pow_succ, mul_comm]), ← S.conj_comp ζ (ζ ^ j) hζ hj, RingHom.comp_apply, ih, hw]

/-- **Invariants**: an element fixed by `σ_ζ` (`ζ` primitive) lies in `C⟮x⟯`. -/
theorem mem_base_of_invariant (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (w : C⟮S.x⟯⟮S.y⟯)
    (hw : S.conj ζ hζ.pow_eq_one w = w) : ∃ a : C⟮S.x⟯, w = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := by
  obtain ⟨a, ha⟩ := S.power_repr w
  have hzero : ∀ i : Fin S.n, (i : ℕ) ≠ 0 → a i = 0 := by
    intro i hi
    have hF := S.fourier ζ hζ a i
    rw [← ha] at hF
    have hs : ∑ j : Fin S.n, S.cst ((ζ ^ (j : ℕ)) ^ (S.n - i)) *
        S.conj (ζ ^ (j : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) w =
        S.cst (∑ j : Fin S.n, (ζ ^ (j : ℕ)) ^ (S.n - i) * (ζ ^ (j : ℕ)) ^ ((⟨0, S.hn⟩ : Fin S.n) :
          ℕ)) * w := by
      rw [S.cst_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [S.conj_pow_invariant ζ hζ.pow_eq_one w hw, pow_zero, mul_one]
    rw [hs, S.root_sum ζ hζ i ⟨0, S.hn⟩, if_neg (fun h ↦ hi (by rw [← h])),
      show S.cst 0 = 0 from Subtype.ext (by simp [cst]), zero_mul] at hF
    have hn0 : (S.n : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦ S.hnK L (by
      have := congrArg Subtype.val h; simpa using this)
    have hy0 : AdjoinSimple.gen C⟮S.x⟯ S.y ≠ 0 := fun h ↦ S.y_ne_zero (by
      have := congrArg Subtype.val h; simpa using this)
    have := (mul_eq_zero.mp hF.symm).resolve_left hn0
    have := (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hy0)
    exact (map_eq_zero_iff _ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).injective).mp this
  refine ⟨a ⟨0, S.hn⟩, ?_⟩
  rw [ha, Finset.sum_eq_single ⟨0, S.hn⟩ (fun i _ hi ↦ by
      rw [hzero i (fun h ↦ hi (Fin.ext h)), map_zero, zero_mul])
    (fun h ↦ absurd (Finset.mem_univ _) h), pow_zero, mul_one]

/-- **The norm** `∏ⱼ σ_{ζʲ} w`. -/
noncomputable def normS (ζ : C) (hζ : ζ ^ S.n = 1) (w : C⟮S.x⟯⟮S.y⟯) : C⟮S.x⟯⟮S.y⟯ :=
  ∏ j ∈ Finset.range S.n, S.conj (ζ ^ j) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]) w

lemma conj_normS (ζ : C) (hζ : ζ ^ S.n = 1) (w : C⟮S.x⟯⟮S.y⟯) :
    S.conj ζ hζ (S.normS ζ hζ w) = S.normS ζ hζ w := by
  have hpow : ∀ j : ℕ, (ζ ^ j) ^ S.n = 1 := fun j ↦ by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  set f : ℕ → C⟮S.x⟯⟮S.y⟯ := fun j ↦ S.conj (ζ ^ j) (hpow j) w
  have hf : ∀ j, S.conj ζ hζ (f j) = f (j + 1) := fun j ↦ by
    simp only [f]
    rw [← RingHom.comp_apply, S.conj_comp, S.conj_congr _ (hpow (j + 1)) (by rw [pow_succ,
      mul_comm])]
  have hn : f S.n = f 0 := by
    simp only [f]
    rw [S.conj_congr _ (hpow 0) (by rw [hζ, pow_zero])]
  unfold normS
  rw [map_prod]
  change ∏ j ∈ Finset.range S.n, S.conj ζ hζ (f j) = ∏ j ∈ Finset.range S.n, f j
  simp_rw [hf]
  obtain ⟨m, hm⟩ : ∃ m, S.n = m + 1 := ⟨S.n - 1, by have := S.hn; omega⟩
  rw [hm, Finset.prod_range_succ (fun j ↦ f (j + 1)) m, Finset.prod_range_succ' f m, ← hm, hn]

/-- The norm lies in `C⟮x⟯`. -/
theorem normS_mem (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (w : C⟮S.x⟯⟮S.y⟯) :
    ∃ a : C⟮S.x⟯, S.normS ζ hζ.pow_eq_one w = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a :=
  S.mem_base_of_invariant ζ hζ _ (S.conj_normS ζ hζ.pow_eq_one w)

/-! ### Orders of conjugates and of norms -/

section Graded

variable (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (Y : LaurentSeries K)
  (hY : Y ^ S.n = g S.p)

lemma embG_cst (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C K c)) (c : C) :
    S.embG g hg Y hY (S.cst c) = HahnSeries.C (algebraMap C K c) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have e : (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ _⟩ : C⟮S.x⟯) =
      algebraMap C[X] C⟮S.x⟯ (Polynomial.C c) :=
    Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_C])
  rw [cst_eq, S.embG_algebraMap, e, S.embXG_algebraMap, hgC]

/-- Under a "graded" expansion (orders of `C⟮x⟯` multiples of `n`, `ord Y` prime to `n`), the
terms of `∑ aᵢ yⁱ` have pairwise distinct orders. -/
lemma embG_terms_distinct
    (hmod : ∀ a : C⟮S.x⟯, a ≠ 0 → ∃ k : ℤ, (S.embXG g hg a).order = S.n * k) (hY0 : Y ≠ 0)
    (hr : IsCoprime Y.order (S.n : ℤ)) (a : Fin S.n → C⟮S.x⟯) (s : Finset (Fin S.n))
    (hs : ∀ i ∈ s, a i ≠ 0) :
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (S.embXG g hg (a i) * Y ^ (i : ℕ)).orderTop ≠
        (S.embXG g hg (a j) * Y ^ (j : ℕ)).orderTop := by
  intro i hi j hj hij heq
  have hai := hs i hi
  have haj := hs j hj
  have hGi : S.embXG g hg (a i) ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hai
  have hGj : S.embXG g hg (a j) ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr haj
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero hGi (pow_ne_zero _ hY0)),
    ← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero hGj (pow_ne_zero _ hY0)),
    WithTop.coe_eq_coe, HahnSeries.order_mul hGi (pow_ne_zero _ hY0),
    HahnSeries.order_mul hGj (pow_ne_zero _ hY0), HahnSeries.order_pow, HahnSeries.order_pow] at heq
  obtain ⟨ki, hki⟩ := hmod (a i) hai
  obtain ⟨kj, hkj⟩ := hmod (a j) haj
  rw [hki, hkj] at heq
  have hdvd : (S.n : ℤ) ∣ Y.order * ((j : ℤ) - i) := ⟨ki - kj, by simp only [nsmul_eq_mul] at heq; linear_combination (-1 : ℤ) * heq⟩
  obtain ⟨q, hq⟩ := hr.symm.dvd_of_dvd_mul_left hdvd
  have hi2 := i.2
  have hj2 := j.2
  have : q = 0 := by
    by_contra hq0
    rcases lt_or_gt_of_ne hq0 with hq0 | hq0
    · have : (S.n : ℤ) * q ≤ -(S.n : ℤ) := by nlinarith
      omega
    · have : (S.n : ℤ) ≤ (S.n : ℤ) * q := by nlinarith
      omega
  subst this
  exact hij (Fin.ext (by omega))

/-- **Conjugation preserves graded orders.** -/
theorem orderTop_embG_conj (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C K c))
    (hmod : ∀ a : C⟮S.x⟯, a ≠ 0 → ∃ k : ℤ, (S.embXG g hg a).order = S.n * k) (hY0 : Y ≠ 0)
    (hr : IsCoprime Y.order (S.n : ℤ)) (c : C) (hc : c ^ S.n = 1) (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embG g hg Y hY (S.conj c hc w)).orderTop = (S.embG g hg Y hY w).orderTop := by
  classical
  obtain ⟨a, rfl⟩ := S.power_repr w
  rw [S.conj_sum]
  set t : Fin S.n → LaurentSeries K := fun i ↦ S.embXG g hg (a i) * Y ^ (i : ℕ)
  set t' : Fin S.n → LaurentSeries K := fun i ↦ HahnSeries.C (algebraMap C K (c ^ (i : ℕ))) * t i
  have e1 : S.embG g hg Y hY (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) = ∑ i, t i := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, S.embG_algebraMap, S.embG_gen]
  have e2 : S.embG g hg Y hY (∑ i : Fin S.n, S.cst (c ^ (i : ℕ)) * (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))) = ∑ i, t' i := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_mul, map_pow, S.embG_algebraMap, S.embG_gen, S.embG_cst g hg Y hY hgC]
  rw [e1, e2]
  set s := Finset.univ.filter fun i : Fin S.n ↦ a i ≠ 0
  have hsplit : ∀ u : Fin S.n → LaurentSeries K, (∀ i : Fin S.n, a i = 0 → u i = 0) →
      ∑ i, u i = ∑ i ∈ s, u i := fun u hu ↦ by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ a i ≠ 0),
      Finset.sum_eq_zero (s := Finset.univ.filter fun i ↦ ¬ a i ≠ 0) (fun i hi ↦ hu i
        (not_not.mp (Finset.mem_filter.mp hi).2)), add_zero]
  have ht0 : ∀ i, a i = 0 → t i = 0 := fun i hi ↦ by simp [t, hi]
  rw [hsplit t ht0, hsplit t' (fun i hi ↦ by simp [t', ht0 i hi])]
  refine LaurentSeries.orderTop_sum_congr s t t' (fun i _ ↦ ?_)
    (S.embG_terms_distinct g hg Y hmod hY0 hr a s (fun i hi ↦ (Finset.mem_filter.mp hi).2))
  have hc0 : algebraMap C K (c ^ (i : ℕ)) ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr
    (pow_ne_zero _ (fun h ↦ by rw [h, zero_pow S.hn.ne'] at hc; exact zero_ne_one hc))
  simp only [t']
  rw [HahnSeries.orderTop_mul, HahnSeries.C_apply, HahnSeries.orderTop_single hc0, WithTop.coe_zero, zero_add]

/-- **Order of the norm** under a graded expansion: `n` times the order. -/
theorem orderTop_embG_normS (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C K c))
    (hmod : ∀ a : C⟮S.x⟯, a ≠ 0 → ∃ k : ℤ, (S.embXG g hg a).order = S.n * k) (hY0 : Y ≠ 0)
    (hr : IsCoprime Y.order (S.n : ℤ)) (ζ : C) (hζ : ζ ^ S.n = 1) (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embG g hg Y hY (S.normS ζ hζ w)).orderTop = S.n • (S.embG g hg Y hY w).orderTop := by
  rw [normS, map_prod, LaurentSeries.orderTop_prod]
  rw [Finset.sum_congr rfl fun j _ ↦ S.orderTop_embG_conj g hg Y hY hgC hmod hY0 hr _ _ w,
    Finset.sum_const, Finset.card_range]

end Graded

/-- **Order of the norm at a non-branch point**: the sum of the orders at the points above. -/
theorem orderTop_embXY_normS (ζ : C) (hζ : ζ ^ S.n = 1) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embXY α β hβ hβp (S.normS ζ hζ w)).orderTop =
      ∑ j ∈ Finset.range S.n, (S.embXY α (algebraMap C K (ζ ^ j) * β)
        (mul_ne_zero (S.root_ne_zero (ζ ^ j) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]))
          hβ) (by rw [mul_pow, ← map_pow, ← pow_mul, mul_comm j S.n, pow_mul, hζ, one_pow, map_one,
            one_mul, hβp]) w).orderTop := by
  rw [normS, map_prod, LaurentSeries.orderTop_prod]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← RingHom.comp_apply, S.embXY_conj]

end SuperData

end Differential
