import RischTragerBronstein.Curves.Reparam

/-!
# Rotating branches: `T ↦ ζ T`

`lscale ζ` is the substitution `T ↦ ζ T` on Laurent series (`ζ ≠ 0`). For `ζᴺ = 1` it fixes
`x = a + Tᴺ` only for `a = 0` and fixes `x = T^{−N}`; it then permutes the roots of `F(x, Y)`, so
a power `ζ^{d}` with `1 ≤ d ≤ deg F` fixes a given root `r` and hence the whole expansion along `r`
(`embG_lscale_fixed`). For a primitive `N`-th root `ζ` this means the expansion only has terms
`Tʲ` with `N ∣ d j` (`coeff_eq_zero_of_lscale_fixed`): the Puiseux exponents `j / N` have
denominators at most `deg F`.
-/

open Polynomial HahnSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential LaurentSeries

section LScale

variable {K : Type*} [Field K]

/-- The coefficients of `z(ζ T)`. -/
noncomputable def lscaleF (ζ : K) (z : LaurentSeries K) : LaurentSeries K where
  coeff j := ζ ^ j * z.coeff j
  isPWO_support' := z.isPWO_support.mono fun j hj ↦ by
    simp only [Function.mem_support] at hj ⊢; exact right_ne_zero_of_mul hj

@[simp] lemma lscaleF_coeff (ζ : K) (z : LaurentSeries K) (j : ℤ) :
    (lscaleF ζ z).coeff j = ζ ^ j * z.coeff j := rfl

lemma support_lscaleF {ζ : K} (hζ : ζ ≠ 0) (z : LaurentSeries K) :
    (lscaleF ζ z).support = z.support := by
  ext j
  simp only [HahnSeries.mem_support, lscaleF_coeff, ne_eq, mul_eq_zero, zpow_ne_zero j hζ,
    false_or]

/-- **`T ↦ ζ T`** as a ring homomorphism. -/
noncomputable def lscale (ζ : K) (hζ : ζ ≠ 0) : LaurentSeries K →+* LaurentSeries K where
  toFun := lscaleF ζ
  map_one' := by
    ext j
    rw [lscaleF_coeff, HahnSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · simp
  map_mul' x y := by
    ext k
    rw [lscaleF_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, Finset.mul_sum]
    have hfin : Finset.antidiagonal (lscaleF ζ x).isPWO_support (lscaleF ζ y).isPWO_support k =
        Finset.antidiagonal x.isPWO_support y.isPWO_support k := by
      ext ij
      simp only [Finset.mem_antidiagonal, support_lscaleF hζ]
    rw [hfin]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [Finset.mem_antidiagonal] at hij
    simp only [lscaleF_coeff]
    rw [← hij.2.2, zpow_add₀ hζ]
    ring
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp [mul_add]

@[simp] lemma lscale_coeff {ζ : K} (hζ : ζ ≠ 0) (z : LaurentSeries K) (j : ℤ) :
    (lscale ζ hζ z).coeff j = ζ ^ j * z.coeff j := rfl

lemma lscale_single {ζ : K} (hζ : ζ ≠ 0) (k : ℤ) (c : K) :
    lscale ζ hζ (single k c) = single k (ζ ^ k * c) := by
  ext j
  rw [lscale_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs with h
  · subst h; rfl
  · simp

lemma lscale_C {ζ : K} (hζ : ζ ≠ 0) (c : K) : lscale ζ hζ (HahnSeries.C c) = HahnSeries.C c := by
  rw [HahnSeries.C_apply, lscale_single, zpow_zero, one_mul]

lemma lscale_mul_lscale {ζ ξ : K} (hζ : ζ ≠ 0) (hξ : ξ ≠ 0) (z : LaurentSeries K) :
    lscale ζ hζ (lscale ξ hξ z) = lscale (ζ * ξ) (mul_ne_zero hζ hξ) z := by
  ext j
  simp only [lscale_coeff, mul_zpow]
  ring

lemma lscale_pow {ζ : K} (hζ : ζ ≠ 0) (d : ℕ) (z : LaurentSeries K) :
    (lscale ζ hζ)^[d] z = lscale (ζ ^ d) (pow_ne_zero d hζ) z := by
  induction d generalizing z with
  | zero => ext j; simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih, lscale_mul_lscale]
    ext j
    simp only [lscale_coeff, pow_succ']

/-- **A series fixed by `T ↦ ζ T`, `ζ` a primitive `N`-th root of unity**, only has terms `Tʲ`
with `N ∣ j`. -/
lemma coeff_eq_zero_of_lscale_fixed {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hζ0 : ζ ≠ 0)
    (d : ℕ) (z : LaurentSeries K) (hz : lscale (ζ ^ d) (pow_ne_zero d hζ0) z = z) (j : ℤ)
    (hj : ¬ (N : ℤ) ∣ d * j) : z.coeff j = 0 := by
  have h := congrArg (fun u : LaurentSeries K ↦ u.coeff j) hz
  simp only [lscale_coeff] at h
  have hne : (ζ ^ d) ^ j ≠ 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    intro h1
    exact hj ((hζ.zpow_eq_one_iff_dvd _).mp h1)
  have : ((ζ ^ d) ^ j - 1) * z.coeff j = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

end LScale

section Subst

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma lscale_comp_branchSub {ζ : K} (hζ : ζ ≠ 0) (N : ℕ) (hN : ζ ^ N = 1) :
    (lscale ζ hζ).comp (branchSub (C := C) N 0) = branchSub N 0 := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [RingHom.comp_apply, bs_C, lscale_C]
  · rw [RingHom.comp_apply, bs_X, map_add, lscale_C, lscale_single, zpow_natCast, hN, one_mul]

lemma lscale_comp_infSub {ζ : K} (hζ : ζ ≠ 0) (N : ℕ) (hN : ζ ^ N = 1) :
    (lscale ζ hζ).comp (infSub (C := C) (K := K) N) = infSub N := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [RingHom.comp_apply, is_C, lscale_C]
  · rw [RingHom.comp_apply, is_X, lscale_single, zpow_neg, zpow_natCast, hN, inv_one, one_mul]

end Subst

section Orbit

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- An automorphism of the expansions fixing `g` maps the expansion along `Y` to the expansion
along its image. -/
lemma embG_comp_fix (ψ : LaurentSeries K →+* LaurentSeries K) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (hψ : ψ.comp g = g) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) (hY' : (S.F.map g).eval (ψ Y) = 0) :
    ψ.comp (S.embG g hg Y hY) = S.embG g hg (ψ Y) hY' := by
  let _ := algebraAdjoinSimple (F := C) S.x
  have _ := isFractionRing_adjoin_simple S.x S.htr
  refine S.ringHom_ext _ _ (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, S.embG_algebraMap, S.embG_algebraMap]
    have : ψ.comp (S.embXG g hg) = S.embXG g hg :=
      IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ by
        simp only [RingHom.comp_apply, S.embXG_algebraMap]
        exact congrArg (fun φ : C[X] →+* LaurentSeries K ↦ φ P) hψ)
    exact congrArg (fun φ : C⟮S.x⟯ →+* LaurentSeries K ↦ φ a) this
  · rw [RingHom.comp_apply, S.embG_gen, S.embG_gen]

lemma root_fix (ψ : LaurentSeries K →+* LaurentSeries K) (g : C[X] →+* LaurentSeries K)
    (hψ : ψ.comp g = g) (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    (S.F.map g).eval (ψ Y) = 0 := by
  have : S.F.map g = (S.F.map g).map ψ := by rw [Polynomial.map_map, hψ]
  rw [this, eval_map, eval₂_at_apply, hY, map_zero]

/-- The roots of a split polynomial fixed by `ψ` are permuted by `ψ`. -/
lemma mem_of_fix (ψ : LaurentSeries K →+* LaurentSeries K) (g : C[X] →+* LaurentSeries K)
    (hψ : ψ.comp g = g) {l : List (LaurentSeries K)}
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) {r : LaurentSeries K}
    (hr : r ∈ l) : ψ r ∈ l := by
  have h0 := S.root_fix ψ g hψ r (S.root_of_mem hl hr)
  rw [hl, eval_list_prod, List.prod_eq_zero_iff] at h0
  obtain ⟨v, hv, hv0⟩ := List.mem_map.mp h0
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hv0
  rw [hv0]; exact hu

/-- **Orbits**: some power `ψᵈ`, `1 ≤ d ≤ |l|`, fixes a given root. -/
lemma exists_iterate_fix (ψ : LaurentSeries K →+* LaurentSeries K) (g : C[X] →+* LaurentSeries K)
    (hψ : ψ.comp g = g) {l : List (LaurentSeries K)}
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) {r : LaurentSeries K}
    (hr : r ∈ l) : ∃ d, 1 ≤ d ∧ d ≤ l.length ∧ ψ^[d] r = r := by
  classical
  have hmem : ∀ i, ψ^[i] r ∈ l := by
    intro i
    induction i with
    | zero => exact hr
    | succ i ih => rw [Function.iterate_succ_apply']; exact S.mem_of_fix ψ g hψ hl ih
  have hcard : l.toFinset.card < (Finset.range (l.length + 1)).card := by
    rw [Finset.card_range]; exact Nat.lt_succ_of_le (List.toFinset_card_le l)
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun i ↦ ψ^[i] r) (fun i _ ↦ List.mem_toFinset.mpr (hmem i))
  have hinj : ∀ k, Function.Injective ψ^[k] := fun k ↦ ψ.injective.iterate k
  have key : ∀ a b, a < b → b ≤ l.length → ψ^[a] r = ψ^[b] r →
      ∃ d, 1 ≤ d ∧ d ≤ l.length ∧ ψ^[d] r = r := by
    intro a b hab hb he
    refine ⟨b - a, by omega, by omega, hinj a ?_⟩
    rw [← Function.iterate_add_apply, show a + (b - a) = b by omega]
    exact he.symm
  have hi' : i ≤ l.length := by have := Finset.mem_range.mp hi; omega
  have hj' : j ≤ l.length := by have := Finset.mem_range.mp hj; omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hj' heq
  · exact key j i h hi' heq.symm

lemma length_le_of_split {g : C[X] →+* LaurentSeries K} {l : List (LaurentSeries K)}
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) : l.length ≤ S.F.natDegree := by
  have h1 : ((l.map fun r ↦ X - Polynomial.C r).prod).natDegree = l.length := by
    have := Polynomial.natDegree_multiset_prod_X_sub_C_eq_card (l : Multiset (LaurentSeries K))
    rwa [Multiset.map_coe, Multiset.prod_coe, Multiset.coe_card] at this
  rw [← h1, ← hl]
  exact natDegree_map_le

/-- **Puiseux support**: along a branch whose parametrization is fixed by every `T ↦ ξ T` with
`ξᴺ = 1`, there is `1 ≤ d ≤ deg F` such that every expansion only has terms `Tʲ` with `N ∣ d j`. -/
theorem branch_support (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) {N : ℕ}
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hζ0 : ζ ≠ 0)
    (hfix : ∀ (ξ : K) (hξ : ξ ≠ 0), ξ ^ N = 1 → (lscale ξ hξ).comp g = g)
    {l : List (LaurentSeries K)} (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod)
    {r : LaurentSeries K} (hr : r ∈ l) :
    ∃ d, 1 ≤ d ∧ d ≤ S.F.natDegree ∧ ∀ (f : C⟮S.x⟯⟮S.y⟯) (j : ℤ), ¬ (N : ℤ) ∣ d * j →
      (S.embG g hg r (S.root_of_mem hl hr) f).coeff j = 0 := by
  obtain ⟨d, hd1, hdl, hdr⟩ := S.exists_iterate_fix (lscale ζ hζ0) g (hfix ζ hζ0 hζ.pow_eq_one) hl hr
  refine ⟨d, hd1, hdl.trans (S.length_le_of_split hl), fun f j hj ↦ ?_⟩
  have hd0 : ζ ^ d ≠ 0 := pow_ne_zero d hζ0
  have hfd := hfix (ζ ^ d) hd0 (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  have hr' : lscale (ζ ^ d) hd0 r = r := by rw [← lscale_pow hζ0 d r]; exact hdr
  have hfixf : lscale (ζ ^ d) hd0 (S.embG g hg r (S.root_of_mem hl hr) f) =
      S.embG g hg r (S.root_of_mem hl hr) f := by
    have := S.embG_comp_fix (lscale (ζ ^ d) hd0) g hg hfd r (S.root_of_mem hl hr)
      (S.root_fix _ g hfd r (S.root_of_mem hl hr))
    have h2 := congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) this
    simp only [RingHom.comp_apply] at h2
    rw [h2]
    exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f)
      (S.embG_congr rfl hg hg hr' _ _)
  exact coeff_eq_zero_of_lscale_fixed hζ hζ0 d _ hfixf j hj

end CurveData

end Orbit

end Curves
