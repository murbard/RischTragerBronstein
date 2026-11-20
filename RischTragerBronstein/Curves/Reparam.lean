import RischTragerBronstein.Curves.Lift

/-!
# Reparametrizing branches: `T ↦ Tᴹ`

`lsub M` is the substitution `T ↦ Tᴹ` on Laurent series. Two branch systems above the same
point (for `x = a + Tᴺ` and `x = a + Tᴺ'`) become equal after `T ↦ Tᴺ'` resp. `T ↦ Tᴺ`
(uniqueness of the roots of a split polynomial), so every branch of one system is a
reparametrization of a branch of the other (`branch_transfer`). Orders and residues scale by the
same factor, so all branch-wise statements can be checked on a single system per point.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Lsub

variable {K : Type*} [Field K]

/-- `T ↦ Tᴹ`. -/
noncomputable def lsub (M : ℕ) (hM : 0 < M) : LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (M : ℤ))
    (fun a b h ↦ by
      simp only [AddMonoidHom.coe_mulLeft] at h
      exact mul_left_cancel₀ (by exact_mod_cast hM.ne') h)
    (fun a b ↦ by
      simp only [AddMonoidHom.coe_mulLeft]
      exact mul_le_mul_iff_of_pos_left (by exact_mod_cast hM))

variable (M : ℕ) (hM : 0 < M)

lemma lsub_coeff_mul (z : LaurentSeries K) (k : ℤ) : (lsub M hM z).coeff (M * k) = z.coeff k := by
  simp only [lsub, embDomainRingHom_apply]
  exact embDomain_mk_coeff _ _

lemma lsub_coeff_not_dvd (z : LaurentSeries K) (j : ℤ) (hj : ¬ (M : ℤ) ∣ j) :
    (lsub M hM z).coeff j = 0 := by
  simp only [lsub, embDomainRingHom_apply]
  refine embDomain_of_notMem_range ?_
  rintro ⟨k, hk⟩
  exact hj ⟨k, by simpa using hk.symm⟩

lemma lsub_single (k : ℤ) (r : K) : lsub M hM (single k r) = single (M * k) r := by
  ext j
  by_cases hd : (M : ℤ) ∣ j
  · obtain ⟨i, rfl⟩ := hd
    rw [lsub_coeff_mul]
    by_cases hik : i = k
    · rw [hik, coeff_single_same, coeff_single_same]
    · rw [coeff_single_of_ne hik, coeff_single_of_ne]
      intro h
      exact hik (mul_left_cancel₀ (by exact_mod_cast hM.ne') h)
  · rw [lsub_coeff_not_dvd M hM _ j hd, coeff_single_of_ne]
    rintro rfl
    exact hd ⟨k, rfl⟩

lemma lsub_C (r : K) : lsub M hM (HahnSeries.C r) = HahnSeries.C r := by
  rw [HahnSeries.C_apply, lsub_single, mul_zero]

lemma lsub_injective : Function.Injective (lsub (K := K) M hM) := fun a b h ↦ by
  ext k
  have := congrArg (fun z : LaurentSeries K ↦ z.coeff (M * k)) h
  simpa only [lsub_coeff_mul] using this

lemma lowerBd_lsub_iff (z : LaurentSeries K) (m : ℤ) :
    LowerBd (lsub M hM z) (M * m) ↔ LowerBd z m := by
  constructor
  · intro h k hk
    rw [← lsub_coeff_mul M hM]
    exact h _ (by
      have : (0 : ℤ) < M := by exact_mod_cast hM
      nlinarith)
  · intro h j hj
    by_cases hd : (M : ℤ) ∣ j
    · obtain ⟨k, rfl⟩ := hd
      rw [lsub_coeff_mul]
      refine h k ?_
      have : (0 : ℤ) < M := by exact_mod_cast hM
      nlinarith
    · exact lsub_coeff_not_dvd M hM z j hd

variable [CharZero K]

/-- The chain rule for `T ↦ Tᴹ`. -/
lemma derivation_lsub (z : LaurentSeries K) :
    LaurentSeries.derivation (lsub M hM z) =
      HahnSeries.C (M : K) * (single ((M : ℤ) - 1) (1 : K) *
        lsub M hM (LaurentSeries.derivation z)) := by
  ext j
  rw [LaurentSeries.derivation_apply, derivative_coeff, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, LaurentSeries.coeff_single_mul, LaurentSeries.derivation_apply,
    smul_eq_mul]
  by_cases hd : (M : ℤ) ∣ j + 1
  · obtain ⟨k, hk⟩ := hd
    have e1 : j - ((M : ℤ) - 1) = M * (k - 1) := by rw [mul_sub, ← hk]; ring
    rw [hk, lsub_coeff_mul, e1, lsub_coeff_mul, derivative_coeff, sub_add_cancel]
    push_cast; ring
  · have hd' : ¬ (M : ℤ) ∣ j - ((M : ℤ) - 1) := fun ⟨k, hk⟩ ↦
      hd ⟨k + 1, by rw [mul_add, ← hk]; ring⟩
    rw [lsub_coeff_not_dvd M hM _ _ hd, lsub_coeff_not_dvd M hM _ _ hd', mul_zero, mul_zero]

/-- **Residues scale by `M`.** -/
lemma res_lsub (w Xh : LaurentSeries K) :
    LaurentSeries.res (lsub M hM w * LaurentSeries.derivation (lsub M hM Xh)) =
      (M : K) * LaurentSeries.res (w * LaurentSeries.derivation Xh) := by
  rw [derivation_lsub, show lsub M hM w * (HahnSeries.C (M : K) * (single ((M : ℤ) - 1) (1 : K) *
      lsub M hM (LaurentSeries.derivation Xh))) = HahnSeries.C (M : K) *
      (single ((M : ℤ) - 1) (1 : K) * lsub M hM (w * LaurentSeries.derivation Xh)) by
    rw [map_mul]; ring]
  rw [SuperData.res_C_mul, LaurentSeries.res, LaurentSeries.coeff_single_mul,
    show (-1 : ℤ) - ((M : ℤ) - 1) = M * (-1) by ring, lsub_coeff_mul]
  rfl

lemma order_lsub (z : LaurentSeries K) : (lsub M hM z).order = M * z.order := by
  by_cases hz : z = 0
  · rw [hz, map_zero, HahnSeries.order_zero, mul_zero]
  have hz' : lsub M hM z ≠ 0 := fun h ↦ hz (lsub_injective M hM (h.trans (map_zero _).symm))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [lsub_coeff_mul]; exact HahnSeries.coeff_order_eq_zero.not.mpr hz
  · by_contra hlt
    push Not at hlt
    have hc := HahnSeries.coeff_order_eq_zero.not.mpr hz'
    by_cases hd : (M : ℤ) ∣ (lsub M hM z).order
    · obtain ⟨k, hk⟩ := hd
      rw [hk, lsub_coeff_mul] at hc
      have : k < z.order := by
        have h0 : (0 : ℤ) < M := by exact_mod_cast hM
        nlinarith
      exact hc (HahnSeries.coeff_eq_zero_of_lt_order this)
    · exact hc (lsub_coeff_not_dvd M hM z _ hd)

end Lsub

section Subst

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma bs_C (N : ℕ) (a : K) (c : C) :
    branchSub N a (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [branchSub_apply, Polynomial.map_C, C_comp, Polynomial.coe_C, ofPowerSeries_C]

lemma bs_X (N : ℕ) (a : K) :
    branchSub (C := C) N a X = HahnSeries.C a + single (N : ℤ) (1 : K) := by
  rw [branchSub_apply, Polynomial.map_X, X_comp, Polynomial.coe_add, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X, map_add, ofPowerSeries_C, ofPowerSeries_X_pow]

lemma is_C (N : ℕ) (c : C) :
    infSub (K := K) N (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [infSub, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]

lemma is_X (N : ℕ) : infSub (C := C) (K := K) N X = single (-(N : ℤ)) 1 := by
  rw [infSub, coe_eval₂RingHom, eval₂_X]

lemma lsub_comp_branchSub (M : ℕ) (hM : 0 < M) (N : ℕ) (a : K) :
    (lsub M hM).comp (branchSub (C := C) N a) = branchSub (N * M) a := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [RingHom.comp_apply, bs_C, bs_C, lsub_C]
  · rw [RingHom.comp_apply, bs_X, bs_X, map_add, lsub_C, lsub_single]
    push_cast; ring_nf

lemma lsub_comp_infSub (M : ℕ) (hM : 0 < M) (N : ℕ) :
    (lsub M hM).comp (infSub (C := C) (K := K) N) = infSub (N * M) := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [RingHom.comp_apply, is_C, is_C, lsub_C]
  · rw [RingHom.comp_apply, is_X, is_X, lsub_single]
    push_cast; ring_nf

end Subst

section Generic

variable {K : Type*} [Field K] [CharZero K]

/-- The differential identity behind all transfers. -/
lemma lsub_diff (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (u u' Xh Xh' : LaurentSeries K)
    (hu : lsub M hM u' = lsub M' hM' u) (hX : lsub M hM Xh' = lsub M' hM' Xh) :
    lsub M hM u' * LaurentSeries.derivation (lsub M hM Xh') =
      lsub M' hM' u * LaurentSeries.derivation (lsub M' hM' Xh) := by rw [hu, hX]

/-- **Simple poles transfer.** -/
lemma transfer_simple (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (u u' Xh Xh' : LaurentSeries K)
    (hu : lsub M hM u' = lsub M' hM' u) (hX : lsub M hM Xh' = lsub M' hM' Xh)
    (h : LowerBd (u * LaurentSeries.derivation Xh) (-1)) :
    LowerBd (u' * LaurentSeries.derivation Xh') (-1) := by
  have e := lsub_diff M M' hM hM' u u' Xh Xh' hu hX
  rw [derivation_lsub, derivation_lsub] at e
  have e' : HahnSeries.C (M : K) * (single ((M : ℤ) - 1) (1 : K) *
      lsub M hM (u' * LaurentSeries.derivation Xh')) = HahnSeries.C (M' : K) *
      (single ((M' : ℤ) - 1) (1 : K) * lsub M' hM' (u * LaurentSeries.derivation Xh)) := by
    rw [map_mul, map_mul]; linear_combination e
  have hR : LowerBd (HahnSeries.C (M' : K) * (single ((M' : ℤ) - 1) (1 : K) *
      lsub M' hM' (u * LaurentSeries.derivation Xh))) (-1) := by
    have h1 := (lowerBd_lsub_iff M' hM' _ (-1)).mpr h
    have := (lowerBd_C (M' : K)).mul ((lowerBd_single ((M' : ℤ) - 1) (1 : K)).mul h1)
    convert this using 1; ring
  rw [← e'] at hR
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM.ne'
  have key : HahnSeries.C (M : K)⁻¹ * single (1 - (M : ℤ)) (1 : K) *
      (HahnSeries.C (M : K) * single ((M : ℤ) - 1) (1 : K)) = 1 := by
    rw [show HahnSeries.C (M : K)⁻¹ * single (1 - (M : ℤ)) (1 : K) *
        (HahnSeries.C (M : K) * single ((M : ℤ) - 1) (1 : K)) =
        (HahnSeries.C (M : K)⁻¹ * HahnSeries.C (M : K)) *
          (single (1 - (M : ℤ)) (1 : K) * single ((M : ℤ) - 1) 1) by ring,
      ← map_mul, inv_mul_cancel₀ hMK, map_one, one_mul, single_mul_single, mul_one,
      show 1 - (M : ℤ) + ((M : ℤ) - 1) = 0 by ring]
    rfl
  have h2 : lsub M hM (u' * LaurentSeries.derivation Xh') =
      HahnSeries.C (M : K)⁻¹ * (single (1 - (M : ℤ)) (1 : K) * (HahnSeries.C (M : K) *
        (single ((M : ℤ) - 1) (1 : K) * lsub M hM (u' * LaurentSeries.derivation Xh')))) := by
    calc lsub M hM (u' * LaurentSeries.derivation Xh')
        = (HahnSeries.C (M : K)⁻¹ * single (1 - (M : ℤ)) (1 : K) *
            (HahnSeries.C (M : K) * single ((M : ℤ) - 1) (1 : K))) *
              lsub M hM (u' * LaurentSeries.derivation Xh') := by rw [key, one_mul]
      _ = _ := by ring
  have h3 : LowerBd (lsub M hM (u' * LaurentSeries.derivation Xh')) (M * (-1)) := by
    rw [h2]
    have := (lowerBd_C (M : K)⁻¹).mul ((lowerBd_single (1 - (M : ℤ)) (1 : K)).mul hR)
    convert this using 1; ring
  exact (lowerBd_lsub_iff M hM _ (-1)).mp h3

/-- **Residues transfer** (scaled). -/
lemma transfer_res (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (u u' Xh Xh' : LaurentSeries K)
    (hu : lsub M hM u' = lsub M' hM' u) (hX : lsub M hM Xh' = lsub M' hM' Xh) :
    (M : K) * LaurentSeries.res (u' * LaurentSeries.derivation Xh') =
      (M' : K) * LaurentSeries.res (u * LaurentSeries.derivation Xh) := by
  rw [← res_lsub M hM, ← res_lsub M' hM', lsub_diff M M' hM hM' u u' Xh Xh' hu hX]

/-- **Orders transfer** (scaled). -/
lemma transfer_order (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (z z' : LaurentSeries K)
    (hz : lsub M hM z' = lsub M' hM' z) : (M : ℤ) * z'.order = M' * z.order := by
  rw [← order_lsub M hM, ← order_lsub M' hM', hz]

end Generic

section Transfer

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- Ring homomorphisms out of `C⟮x⟯⟮y⟯` agreeing on `C⟮x⟯` and on `y` are equal. -/
lemma ringHom_ext {R : Type*} [Field R] (φ ψ : C⟮S.x⟯⟮S.y⟯ →+* R)
    (h1 : ∀ a : C⟮S.x⟯, φ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) = ψ (algebraMap _ _ a))
    (h2 : φ (AdjoinSimple.gen C⟮S.x⟯ S.y) = ψ (AdjoinSimple.gen C⟮S.x⟯ S.y)) : φ = ψ := by
  refine RingHom.ext fun w ↦ ?_
  obtain ⟨w, hw⟩ := w
  induction hw using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact h2
  | algebraMap a => exact h1 a
  | add u v hu hv ihu ihv =>
    have e : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e, map_mul, map_mul, ihu, ihv]
  | inv u hu ihu =>
    have e : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯⟮S.y⟯) = (⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ := rfl
    rw [e, map_inv₀, map_inv₀, ihu]

lemma embG_congr {g g' : C[X] →+* LaurentSeries K} (hgg : g = g') (hg : Function.Injective g)
    (hg' : Function.Injective g') {Y Y' : LaurentSeries K} (hYY : Y = Y')
    (hY : (S.F.map g).eval Y = 0) (hY' : (S.F.map g').eval Y' = 0) :
    S.embG g hg Y hY = S.embG g' hg' Y' hY' := by
  subst hgg hYY; rfl

variable [CharZero K]

lemma lsub_injective' (M : ℕ) (hM : 0 < M) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) : Function.Injective ((lsub M hM).comp g) :=
  (lsub_injective M hM).comp hg

lemma lsub_root (M : ℕ) (hM : 0 < M) (g : C[X] →+* LaurentSeries K) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) : (S.F.map ((lsub M hM).comp g)).eval (lsub M hM Y) = 0 := by
  rw [← Polynomial.map_map, eval_map, eval₂_at_apply, hY, map_zero]

/-- `T ↦ Tᴹ` after an expansion is the expansion along the substituted data. -/
lemma embG_lsub (M : ℕ) (hM : 0 < M) (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    (lsub M hM).comp (S.embG g hg Y hY) =
      S.embG ((lsub M hM).comp g) (lsub_injective' M hM g hg) (lsub M hM Y)
        (S.lsub_root M hM g Y hY) := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  refine S.ringHom_ext _ _ (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, S.embG_algebraMap, S.embG_algebraMap]
    have : (lsub M hM).comp (S.embXG g hg) = S.embXG ((lsub M hM).comp g)
        (lsub_injective' M hM g hg) :=
      IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ by
        simp only [RingHom.comp_apply, S.embXG_algebraMap])
    exact congrArg (fun φ : C⟮S.x⟯ →+* LaurentSeries K ↦ φ a) this
  · rw [RingHom.comp_apply, S.embG_gen, S.embG_gen]

/-- **Transfer between branch systems** related by `lsub M ∘ g' = lsub M' ∘ g`: every branch of the
second system is a reparametrization of a branch of the first. -/
theorem branch_transfer (g g' : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (hg' : Function.Injective g') (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M')
    (hcomp : (lsub M hM).comp g' = (lsub M' hM').comp g)
    (r r' : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map g = ∏ k, (X - Polynomial.C (r k)))
    (hs' : S.F.map g' = ∏ k, (X - Polynomial.C (r' k))) (k' : Fin S.F.natDegree) :
    ∃ k, (lsub M hM).comp (S.embG g' hg' (r' k') (S.root_of_split g' r' hs' k')) =
      (lsub M' hM').comp (S.embG g hg (r k) (S.root_of_split g r hs k)) := by
  classical
  have h1 : S.F.map ((lsub M' hM').comp g) = ∏ k, (X - Polynomial.C (lsub M' hM' (r k))) := by
    rw [← Polynomial.map_map, hs, Polynomial.map_prod]
    simp
  have h2 : S.F.map ((lsub M hM).comp g') = ∏ k, (X - Polynomial.C (lsub M hM (r' k))) := by
    rw [← Polynomial.map_map, hs', Polynomial.map_prod]
    simp
  have hroots : (Finset.univ.val.map fun k ↦ lsub M' hM' (r k)) =
      (Finset.univ.val.map fun k ↦ lsub M hM (r' k)) := by
    have e1 := roots_multiset_prod_X_sub_C (Finset.univ.val.map fun k ↦ lsub M' hM' (r k))
    have e2 := roots_multiset_prod_X_sub_C (Finset.univ.val.map fun k ↦ lsub M hM (r' k))
    rw [Multiset.map_map] at e1 e2
    rw [← e1, ← e2]
    congr 1
    have : ∏ k, (X - Polynomial.C (lsub M' hM' (r k))) =
        ∏ k, (X - Polynomial.C (lsub M hM (r' k))) := by rw [← h1, ← h2, hcomp]
    exact this
  have hmem : lsub M hM (r' k') ∈ (Finset.univ.val.map fun k ↦ lsub M' hM' (r k)) := by
    rw [hroots]; exact Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ _))
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hmem
  refine ⟨k, ?_⟩
  rw [S.embG_lsub, S.embG_lsub]
  exact S.embG_congr hcomp _ _ hk.symm _ _

/-- Two branch systems above the same finite point. -/
lemma fin_rel (a : K) (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (r r' : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k)))
    (hs' : S.F.map (branchSub N' a) = ∏ k, (X - Polynomial.C (r' k))) (k' : Fin S.F.natDegree) :
    ∃ k, ∀ z, lsub N hN (S.embG (branchSub N' a) (branchSub_injective N' hN' a) (r' k')
        (S.root_of_split _ r' hs' k') z) =
      lsub N' hN' (S.embG (branchSub N a) (branchSub_injective N hN a) (r k)
        (S.root_of_split _ r hs k) z) := by
  have hcomp : (lsub N hN).comp (branchSub (C := C) N' a) = (lsub N' hN').comp (branchSub N a) := by
    rw [lsub_comp_branchSub, lsub_comp_branchSub, mul_comm]
  obtain ⟨k, hk⟩ := S.branch_transfer _ _ (branchSub_injective N hN a)
    (branchSub_injective N' hN' a) N N' hN hN' hcomp r r' hs hs' k'
  exact ⟨k, fun z ↦ RingHom.congr_fun hk z⟩

/-- Two branch systems above infinity. -/
lemma inf_rel (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (r r' : Fin S.F.natDegree → LaurentSeries K)
    (hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k)))
    (hs' : S.F.map (infSub N') = ∏ k, (X - Polynomial.C (r' k))) (k' : Fin S.F.natDegree) :
    ∃ k, ∀ z, lsub N hN (S.embG (infSub N') (infSub_injective N' hN') (r' k')
        (S.root_of_split _ r' hs' k') z) =
      lsub N' hN' (S.embG (infSub N) (infSub_injective N hN) (r k)
        (S.root_of_split _ r hs k) z) := by
  have hcomp : (lsub N hN).comp (infSub (C := C) (K := K) N') = (lsub N' hN').comp (infSub N) := by
    rw [lsub_comp_infSub, lsub_comp_infSub, mul_comm]
  obtain ⟨k, hk⟩ := S.branch_transfer _ _ (infSub_injective N hN)
    (infSub_injective N' hN') N N' hN hN' hcomp r r' hs hs' k'
  exact ⟨k, fun z ↦ RingHom.congr_fun hk z⟩

lemma lsub_Xfin (M N : ℕ) (hM : 0 < M) (a : K) :
    lsub M hM (HahnSeries.C a + single (N : ℤ) (1 : K)) =
      HahnSeries.C a + single ((N * M : ℕ) : ℤ) (1 : K) := by
  rw [map_add, lsub_C, lsub_single]; push_cast; ring_nf

lemma lsub_Xinf (M N : ℕ) (hM : 0 < M) :
    lsub M hM (single (-(N : ℤ)) (1 : K)) = single (-((N * M : ℕ) : ℤ)) (1 : K) := by
  rw [lsub_single]; push_cast; ring_nf

/-- The torsion relation `ord φ(w) = m Λ(res φ(g) dX̂)` is independent of the branch system. -/
lemma tors_rel_transfer (M M' : ℕ) (hM : 0 < M) (hM' : 0 < M') (u u' w w' Xh Xh' : LaurentSeries K)
    (hu : lsub M hM u' = lsub M' hM' u) (hw : lsub M hM w' = lsub M' hM' w)
    (hX : lsub M hM Xh' = lsub M' hM' Xh) (m : ℕ) (Λ : K →ₗ[ℚ] ℚ)
    (h : (w.order : ℚ) = m * Λ (LaurentSeries.res (u * LaurentSeries.derivation Xh))) :
    (w'.order : ℚ) = m * Λ (LaurentSeries.res (u' * LaurentSeries.derivation Xh')) := by
  have ho := transfer_order M M' hM hM' w w' hw
  have hr := transfer_res M M' hM hM' u u' Xh Xh' hu hX
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM.ne'
  have hres : LaurentSeries.res (u' * LaurentSeries.derivation Xh') =
      ((M' / M : ℚ) : K) * LaurentSeries.res (u * LaurentSeries.derivation Xh) := by
    push_cast
    field_simp
    linear_combination hr
  rw [hres, show ((M' / M : ℚ) : K) * LaurentSeries.res (u * LaurentSeries.derivation Xh) =
    (M' / M : ℚ) • LaurentSeries.res (u * LaurentSeries.derivation Xh) by
      rw [Rat.smul_def], map_smul, smul_eq_mul]
  have ho' : (w'.order : ℚ) * M = w.order * M' := by
    have := congrArg (fun z : ℤ ↦ (z : ℚ)) ho
    push_cast at this; linarith
  rw [show (m : ℚ) * ((M' : ℚ) / M * Λ (LaurentSeries.res (u * LaurentSeries.derivation Xh))) =
    (M' : ℚ) / M * (m * Λ (LaurentSeries.res (u * LaurentSeries.derivation Xh))) by ring, ← h]
  field_simp
  linarith


end CurveData

end Transfer

end Curves
