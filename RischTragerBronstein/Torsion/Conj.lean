import RischTragerBronstein.Torsion.Count

/-!
# Conjugate branches (any characteristic)

* `rot ζ`: the automorphism `T ↦ ζ T` of `K⸨T⸩` (`ζ ≠ 0`), with `order_rot`, `lowerBd_rot_iff`;
* `rot_branchSub`: if `ζᴺ = 1` it fixes `x = a + Tᴺ`, so it permutes the roots of `F(a + Tᴺ, Y)`;
* `embG_rot`, `embG_lsub'`: expansions along `ζ`-conjugate and reparametrized roots are the
  transformed expansions (char-free versions of the `Reparam` lemmas);
* `lowerBd_conj_iff`: for `r = rot ζ (lsub s ρ)` the orders along `r` (at `x = a + T^{s e}`) are
  `s` times those along `ρ` (at `x = a + Tᵉ`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Rot

variable {K : Type*} [Field K]

lemma coeff_mul_sets {x y : LaurentSeries K} {s t : Set ℤ} (hs : s.IsPWO) (ht : t.IsPWO)
    (hxs : x.support ⊆ s) (hyt : y.support ⊆ t) (a : ℤ) :
    (x * y).coeff a = ∑ ij ∈ Finset.antidiagonal hs ht a, x.coeff ij.1 * y.coeff ij.2 := by
  classical
  rw [HahnSeries.coeff_mul_left' hs hxs]
  refine Finset.sum_subset (Finset.antidiagonal_mono_right hyt) fun ij hij hij' ↦ ?_
  rw [Finset.mem_antidiagonal] at hij hij'
  have : ij.2 ∉ y.support := fun h ↦ hij' ⟨hij.1, h, hij.2.2⟩
  rw [HahnSeries.mem_support, not_not] at this
  rw [this, mul_zero]

/-- The series `∑ ζᵏ zₖ Tᵏ`. -/
noncomputable def rotS (ζ : K) (z : LaurentSeries K) : LaurentSeries K where
  coeff k := ζ ^ k * z.coeff k
  isPWO_support' := z.isPWO_support.mono fun k hk ↦ by
    simp only [Function.mem_support, ne_eq] at hk ⊢
    exact fun h ↦ hk (by rw [h, mul_zero])

@[simp] lemma rotS_coeff (ζ : K) (z : LaurentSeries K) (k : ℤ) :
    (rotS ζ z).coeff k = ζ ^ k * z.coeff k := rfl

lemma rotS_support (ζ : K) (z : LaurentSeries K) : (rotS ζ z).support ⊆ z.support := fun k hk ↦ by
  simp only [HahnSeries.mem_support, rotS_coeff, ne_eq] at hk ⊢
  exact fun h ↦ hk (by rw [h, mul_zero])

/-- **The rotation `T ↦ ζ T`.** -/
noncomputable def rot (ζ : K) (hζ : ζ ≠ 0) : LaurentSeries K →+* LaurentSeries K where
  toFun := rotS ζ
  map_one' := by
    ext k
    simp only [rotS_coeff, HahnSeries.coeff_one]
    split_ifs with h
    · rw [h, zpow_zero, one_mul]
    · rw [mul_zero]
  map_mul' x y := by
    ext a
    rw [coeff_mul_sets x.isPWO_support y.isPWO_support (rotS_support ζ x) (rotS_support ζ y),
      rotS_coeff, coeff_mul_sets x.isPWO_support y.isPWO_support subset_rfl subset_rfl,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [rotS_coeff, rotS_coeff, ← hij.2.2, zpow_add₀ hζ]
    ring
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp [mul_add]

variable (ζ : K) (hζ : ζ ≠ 0)

@[simp] lemma rot_coeff (z : LaurentSeries K) (k : ℤ) : (rot ζ hζ z).coeff k = ζ ^ k * z.coeff k :=
  rfl

lemma rot_eq_zero_iff (z : LaurentSeries K) : rot ζ hζ z = 0 ↔ z = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  ext k
  have := congrArg (fun w : LaurentSeries K ↦ w.coeff k) h
  simp only [rot_coeff, HahnSeries.coeff_zero] at this
  simpa [zpow_ne_zero k hζ] using this

lemma rot_injective : Function.Injective (rot ζ hζ) := fun a b h ↦ by
  rw [← sub_eq_zero, ← rot_eq_zero_iff ζ hζ, map_sub, h, sub_self]

lemma lowerBd_rot_iff (z : LaurentSeries K) (m : ℤ) : LowerBd (rot ζ hζ z) m ↔ LowerBd z m := by
  refine ⟨fun h k hk ↦ ?_, fun h k hk ↦ by rw [rot_coeff, h k hk, mul_zero]⟩
  have := h k hk
  rw [rot_coeff] at this
  exact (mul_eq_zero.mp this).resolve_left (zpow_ne_zero k hζ)

lemma order_rot (z : LaurentSeries K) : (rot ζ hζ z).order = z.order := by
  by_cases h0 : z = 0
  · rw [h0, map_zero]
  have h0' : rot ζ hζ z ≠ 0 := fun h ↦ h0 ((rot_eq_zero_iff ζ hζ z).mp h)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) (HahnSeries.order_le_of_coeff_ne_zero ?_)
  · rw [rot_coeff]; exact mul_ne_zero (zpow_ne_zero _ hζ) (HahnSeries.coeff_order_eq_zero.not.mpr h0)
  · have := HahnSeries.coeff_order_eq_zero.not.mpr h0'
    rw [rot_coeff] at this
    exact right_ne_zero_of_mul this

lemma rot_single (k : ℤ) (r : K) : rot ζ hζ (single k r) = single k (ζ ^ k * r) := by
  ext j
  rw [rot_coeff]
  by_cases h : j = k
  · subst h; rw [coeff_single_same, coeff_single_same]
  · rw [coeff_single_of_ne h, coeff_single_of_ne h, mul_zero]

lemma rot_C (r : K) : rot ζ hζ (HahnSeries.C r) = HahnSeries.C r := by
  rw [HahnSeries.C_apply, rot_single, zpow_zero, one_mul]

variable {C : Type*} [Field C] [Algebra C K]

lemma rot_branchSub (N : ℕ) (hN : ζ ^ N = 1) (a : K) :
    (rot ζ hζ).comp (branchSub (C := C) N a) = branchSub N a := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · have e : branchSub (C := C) (K := K) N a (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
      ext k
      rw [branchSub_apply, Polynomial.map_C, C_comp, coeff_ofPS, HahnSeries.C_apply]
      split_ifs with hk
      · rw [Polynomial.coeff_coe, coeff_C]
        by_cases hk0 : k = 0
        · subst hk0; simp
        · rw [if_neg (by omega), coeff_single_of_ne hk0]
      · rw [coeff_single_of_ne (by omega)]
    rw [RingHom.comp_apply, e, rot_C]
  · have e : branchSub (C := C) (K := K) N a X = HahnSeries.C a + single (N : ℤ) 1 := by
      ext k
      rw [branchSub_apply, Polynomial.map_X, X_comp, coeff_ofPS, HahnSeries.coeff_add,
        HahnSeries.C_apply]
      split_ifs with hk
      · rw [Polynomial.coeff_coe, Polynomial.coeff_add, coeff_C, coeff_X_pow]
        obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
        simp only [Int.toNat_natCast]
        by_cases h0 : k' = 0
        · subst h0
          rcases Nat.eq_zero_or_pos N with hN0 | hN0
          · subst hN0; simp
          · rw [if_pos rfl, if_neg (by omega)]
            simp only [Nat.cast_zero, coeff_single_same, add_zero]
            rw [coeff_single_of_ne (show (0 : ℤ) ≠ N by omega), add_zero]
        · rw [if_neg h0, coeff_single_of_ne (by exact_mod_cast h0)]
          by_cases hkN : k' = N
          · subst hkN; rw [if_pos rfl, coeff_single_same, zero_add]
          · rw [if_neg hkN, coeff_single_of_ne (by exact_mod_cast hkN), add_zero]
      · rw [coeff_single_of_ne (by omega), coeff_single_of_ne (by omega), add_zero]
    rw [RingHom.comp_apply, e, map_add, rot_C, rot_single, zpow_natCast, hN, one_mul]

lemma rot_root (N : ℕ) (hN : ζ ^ N = 1) (a : K) (F : C[X][X]) (r : LaurentSeries K)
    (hr : (F.map (branchSub N a)).eval r = 0) : (F.map (branchSub N a)).eval (rot ζ hζ r) = 0 := by
  rw [← rot_branchSub ζ hζ N hN a, ← Polynomial.map_map, eval_map, eval₂_at_apply, hr, map_zero]

end Rot

section Curve

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- Ring homomorphisms out of `C⟮x⟯⟮y⟯` agreeing on `C⟮x⟯` and on `y` are equal (char-free). -/
lemma ringHom_ext' {R : Type*} [Field R] (φ ψ : C⟮S.x⟯⟮S.y⟯ →+* R)
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

/-- Composing an expansion with a ring map `h` of Laurent series. -/
lemma embG_comp (h : LaurentSeries K →+* LaurentSeries K) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (hhg : Function.Injective (h.comp g)) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) (hY' : (S.F.map (h.comp g)).eval (h Y) = 0) :
    h.comp (S.embG g hg Y hY) = S.embG (h.comp g) hhg (h Y) hY' := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  refine S.ringHom_ext' _ _ (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, S.embG_algebraMap, S.embG_algebraMap]
    have : h.comp (S.embXG g hg) = S.embXG (h.comp g) hhg :=
      IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ by
        simp only [RingHom.comp_apply, S.embXG_algebraMap])
    exact congrArg (fun φ : C⟮S.x⟯ →+* LaurentSeries K ↦ φ a) this
  · rw [RingHom.comp_apply, S.embG_gen, S.embG_gen]

lemma embG_congr' {g g' : C[X] →+* LaurentSeries K} (hgg : g = g') (hg : Function.Injective g)
    (hg' : Function.Injective g') {Y Y' : LaurentSeries K} (hYY : Y = Y')
    (hY : (S.F.map g).eval Y = 0) (hY' : (S.F.map g').eval Y' = 0) :
    S.embG g hg Y hY = S.embG g' hg' Y' hY' := by
  subst hgg hYY; rfl

/-- **Conjugate branches**: the expansion along `rot ζ r` is the rotated expansion along `r`. -/
lemma embG_rot (ζ : K) (hζ : ζ ≠ 0) (N : ℕ) (hN : 0 < N) (hζN : ζ ^ N = 1) (a : K)
    (r : LaurentSeries K) (hr : (S.F.map (branchSub N a)).eval r = 0) (f : C⟮S.x⟯⟮S.y⟯) :
    S.embG (branchSub N a) (branchSub_injective N hN a) (rot ζ hζ r) (rot_root ζ hζ N hζN a S.F r hr) f =
      rot ζ hζ (S.embG (branchSub N a) (branchSub_injective N hN a) r hr f) := by
  have hc := rot_branchSub (C := C) ζ hζ N hζN a
  have hinj : Function.Injective ((rot ζ hζ).comp (branchSub (C := C) N a)) := by
    rw [hc]; exact branchSub_injective N hN a
  have h := S.embG_comp (rot ζ hζ) (branchSub N a) (branchSub_injective N hN a) hinj r hr
    (by rw [hc]; exact rot_root ζ hζ N hζN a S.F r hr)
  have := congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) h
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) (S.embG_congr' hc.symm _ _ rfl _ _)

/-- **Reparametrized branches** (char-free). -/
lemma embG_lsub_fin (s : ℕ) (hs : 0 < s) (e : ℕ) (he : 0 < e) (a : K)
    (ρ : LaurentSeries K) (hρ : (S.F.map (branchSub e a)).eval ρ = 0)
    (hρ' : (S.F.map (branchSub (s * e) a)).eval (lsub s hs ρ) = 0) (f : C⟮S.x⟯⟮S.y⟯) :
    S.embG (branchSub (s * e) a) (branchSub_injective (s * e) (Nat.mul_pos hs he) a) (lsub s hs ρ) hρ' f =
      lsub s hs (S.embG (branchSub e a) (branchSub_injective e he a) ρ hρ f) := by
  have hc : (lsub s hs).comp (branchSub (C := C) e a) = branchSub (s * e) a := by
    have := lsub_comp_branchSub (C := C) (K := K) s hs e a
    rw [this, mul_comm]
  have hinj : Function.Injective ((lsub s hs).comp (branchSub (C := C) e a)) := by
    rw [hc]; exact branchSub_injective _ (Nat.mul_pos hs he) a
  have h := S.embG_comp (lsub s hs) (branchSub e a) (branchSub_injective e he a) hinj ρ hρ
    (by rw [hc]; exact hρ')
  have := congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) h
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) (S.embG_congr' hc.symm _ _ rfl _ _)

end CurveData

end Curve

end Curves
