import RischTragerBronstein.Mixed.KPClass
import RischTragerBronstein.Mixed.KPMain

/-!
# The exponent classes of the expansion at a branch point

At a branch point `x = e + Xⁿ` of `yⁿ = p(x)` the expansion of `C(x)` has only exponents divisible
by `n` and `y = X · U(Xⁿ)`; so, with `σ = (X ↦ z X)`, `zⁿ = 1`:

* `scaleL_embXG_branch`: `σ` fixes the expansions of `C(x)`;
* `scaleL_branchYe`: `σ y = z y` (uniqueness of `n`-th roots with a given constant coefficient,
  `eq_of_pow_eq`: two such roots differ by a series `W` with `Wⁿ = 1`, hence `W′ = 0`);
* `projL_embB_zero`: the class-`0` part of the expansion of `b yʲ` (`b ∈ C(x)`, `0 < j < n`)
  vanishes.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace LaurentSeries

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- **Uniqueness of `n`-th roots** with a given non-zero constant coefficient. -/
theorem eq_of_pow_eq (n : ℕ) (hn : 0 < n) (U V : K⸨X⸩) (hU : U ≠ 0) (hUo : U.order = 0)
    (hpow : V ^ n = U ^ n) (hc : V.coeff 0 = U.coeff 0) : V = U := by
  set W := V * U⁻¹ with hW
  have hWn : W ^ n = 1 := by
    rw [hW, mul_pow, hpow, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hU)]
  have hW0 : W ≠ 0 := fun h ↦ by rw [h, zero_pow hn.ne'] at hWn; exact zero_ne_one hWn
  -- `W′ = 0`
  have hd : LaurentSeries.derivation W = 0 := by
    have h := congrArg (LaurentSeries.derivation (K := K)) hWn
    rw [Derivation.leibniz_pow, Derivation.map_one_eq_zero, nsmul_eq_mul, smul_eq_mul] at h
    have h1 : (n : K⸨X⸩) * W ^ (n - 1) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ hW0)
      rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := K))]
      exact HahnSeries.C_ne_zero (by exact_mod_cast hn.ne')
    rw [← mul_assoc] at h
    exact (mul_eq_zero.mp h).resolve_left h1
  -- so `W` is the constant `W₀ = 1`
  have hcoef : ∀ k : ℤ, k ≠ 0 → W.coeff k = 0 := fun k hk ↦ by
    have := congrArg (fun G ↦ G.coeff (k - 1)) hd
    simp only [LaurentSeries.derivation_apply, derivative_coeff, sub_add_cancel,
      HahnSeries.coeff_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hk)
  have hinv : ∀ k < 0, (U⁻¹).coeff k = 0 := fun k hk ↦
    HahnSeries.coeff_eq_zero_of_lt_order (by rw [Differential.order_inv' U hU, hUo]; omega)
  have hVo : ∀ k < 0, V.coeff k = 0 := fun k hk ↦ by
    by_contra h
    have hV0 : V ≠ 0 := fun h0 ↦ h (by rw [h0]; rfl)
    have h1 : V.order < 0 := lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h) hk
    have h2 := congrArg HahnSeries.order hpow
    rw [HahnSeries.order_pow, HahnSeries.order_pow, hUo, smul_zero, nsmul_eq_mul] at h2
    have : (n : ℤ) * V.order < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hn) h1
    omega
  have hWc0 : W.coeff 0 = 1 := by
    have h1 := coeff_mul_add (x := V) (y := U⁻¹) (a := 0) (b := 0) hVo hinv
    rw [add_zero] at h1
    rw [hW, h1, hc]
    have h2 := coeff_mul_add (x := U) (y := U⁻¹) (a := 0) (b := 0) (fun k hk ↦
      HahnSeries.coeff_eq_zero_of_lt_order (by rw [hUo]; exact hk)) hinv
    rw [add_zero, mul_inv_cancel₀ hU, HahnSeries.coeff_one, if_pos rfl] at h2
    exact h2.symm
  have hW1 : W = 1 := by
    ext k
    rw [HahnSeries.coeff_one]
    split_ifs with h
    · rw [h, hWc0]
    · exact hcoef k h
  rw [hW, mul_inv_eq_one₀ (inv_ne_zero hU |> fun _ ↦ hU)] at hW1
  exact hW1

lemma order_scaleL (z : K) (hz : z ≠ 0) (F : K⸨X⸩) : (scaleL z hz F).order = F.order := by
  by_cases hF : F = 0
  · rw [hF, map_zero]
  have hσ : scaleL z hz F ≠ 0 := fun h ↦ hF (by
    ext k
    have := congrArg (fun G ↦ G.coeff k) h
    simp only [coeff_scaleL, HahnSeries.coeff_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (zpow_ne_zero _ hz))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by
    rw [coeff_scaleL]
    exact mul_ne_zero (zpow_ne_zero _ hz) ((not_congr HahnSeries.coeff_order_eq_zero).mpr hF)))
    (HahnSeries.order_le_of_coeff_ne_zero (by
      have := (not_congr HahnSeries.coeff_order_eq_zero).mpr hσ
      rw [coeff_scaleL] at this
      exact right_ne_zero_of_mul this))

/-- `σ` fixes the series with exponents divisible by `n`. -/
lemma scaleL_fix (z : K) (hz : z ≠ 0) (n : ℕ) (hzn : z ^ n = 1) (F : K⸨X⸩)
    (hF : ∀ k, F.coeff k ≠ 0 → (n : ℤ) ∣ k) : scaleL z hz F = F := by
  ext k
  rw [coeff_scaleL]
  by_cases h : F.coeff k = 0
  · rw [h, mul_zero]
  · obtain ⟨q, rfl⟩ := hF k h
    rw [zpow_mul, zpow_natCast, hzn, one_zpow, one_mul]

end LaurentSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Differential C] [Field L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]
variable (S : SuperData C L)

/-- `σ` fixes the substitution `x ↦ e + Xⁿ`. -/
lemma scaleL_branchSub (z : K) (hz : z ≠ 0) (hzn : z ^ S.n = 1) (e : K) :
    (scaleL z hz).comp (branchSub (C := C) S.n e) = branchSub S.n e := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [RingHom.comp_apply, branchSub_C, scaleL_C]
  · rw [RingHom.comp_apply, branchSub_eq_subst, substHom_apply, Polynomial.map_X, aeval_X, map_add,
      scaleL_C, scaleL_single, zpow_natCast, hzn, one_mul]

/-- `σ` fixes the expansions of `C(x)` at a branch point. -/
lemma scaleL_embXG_branch (z : K) (hz : z ≠ 0) (hzn : z ^ S.n = 1) (e : K) (a : C⟮S.x⟯) :
    scaleL z hz (S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) a) =
      S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) a := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have h : (scaleL z hz).comp (S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e)) =
      S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ ?_)
    simp only [RingHom.comp_apply, S.embXG_algebraMap]
    exact congrArg (fun φ : C[X] →+* LaurentSeries K ↦ φ P) (S.scaleL_branchSub z hz hzn e)
  exact congrArg (fun φ : C⟮S.x⟯ →+* LaurentSeries K ↦ φ a) h

variable [IsAlgClosed K]

/-- **`σ y = z y`** at a branch point. -/
lemma scaleL_branchYe (z : K) (hz : z ≠ 0) (hzn : z ^ S.n = 1) (e γ : K) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    scaleL z hz (S.branchYe e γ hγ hγp) = HahnSeries.C z * S.branchYe e γ hγ hγp := by
  obtain ⟨hU, hU0⟩ := S.branchU_spec e γ hγ hγp
  set U := ofPowerSeries ℤ K (S.branchU e γ hγ hγp) with hUdef
  have hUc : U.coeff 0 = γ := by
    rw [hUdef, coeff_ofPS, if_pos le_rfl, Int.toNat_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0]
  have hUne : U ≠ 0 := fun h ↦ hγ (by rw [← hUc, h]; rfl)
  have hco : ∀ k < 0, U.coeff k = 0 := fun k hk ↦ by
    rw [hUdef, coeff_ofPS, if_neg (by omega)]
  have hUo : U.order = 0 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hUc]; exact hγ)) ?_
    by_contra hlt
    push Not at hlt
    exact (not_congr HahnSeries.coeff_order_eq_zero).mpr hUne (hco _ hlt)
  set V := scaleL z hz U with hV
  have hUn : U ^ S.n = ofPowerSeries ℤ K
      (((S.pBranch e).comp (X ^ S.n) : K[X]) : PowerSeries K) := by
    rw [hUdef, ← map_pow, hU]
  have hGfix : ∀ k, (U ^ S.n).coeff k ≠ 0 → (S.n : ℤ) ∣ k := fun k hk ↦ by
    rw [hUn, coeff_ofPS] at hk
    split_ifs at hk with h0
    · rw [Polynomial.coeff_coe, ← expand_eq_comp_X_pow, coeff_expand S.hn] at hk
      split_ifs at hk with hd
      · obtain ⟨q, hq⟩ := hd
        exact ⟨q, by rw [← Int.toNat_of_nonneg h0, hq]; push_cast; ring⟩
      · exact absurd rfl hk
    · exact absurd rfl hk
  have hpow : V ^ S.n = U ^ S.n := by
    rw [hV, ← map_pow, scaleL_fix z hz S.n hzn _ hGfix]
  have hc : V.coeff 0 = U.coeff 0 := by rw [hV, coeff_scaleL, zpow_zero, one_mul]
  have hVU : scaleL z hz U = U := eq_of_pow_eq S.n S.hn U V hUne hUo hpow hc
  rw [branchYe, map_mul, ← hUdef, hVU, scaleL_single, zpow_one, mul_one, HahnSeries.C_apply,
    ← mul_assoc, HahnSeries.single_mul_single, zero_add, mul_one]

/-- **The class-`0` part of the expansion of `b yʲ` vanishes** at a branch point (`0 < j < n`). -/
theorem projL_embB_zero (ζ : K) (hζ : IsPrimitiveRoot ζ S.n) (hζ0 : ζ ≠ 0) (e γ : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) (b : C⟮S.x⟯)
    (j : ℕ) (hj0 : 0 < j) (hjn : j < S.n) :
    projL ζ hζ0 S.n (S.embB e γ he hγ hγp
      (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ b * AdjoinSimple.gen C⟮S.x⟯ S.y ^ j)) = 0 := by
  set φ := S.embB e γ he hγ hγp
  have hφ : φ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ b * AdjoinSimple.gen C⟮S.x⟯ S.y ^ j) =
      S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) b *
        S.branchYe e γ hγ hγp ^ j := by
    rw [map_mul, map_pow]
    simp only [φ, embB, S.embG_algebraMap, S.embG_gen]
  have hk : ∀ k ∈ Finset.range S.n, scaleL (ζ ^ k) (pow_ne_zero k hζ0) (φ
      (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ b * AdjoinSimple.gen C⟮S.x⟯ S.y ^ j)) =
      HahnSeries.C ((ζ ^ j) ^ k) * φ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ b *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ j) := fun k _ ↦ by
    have hzn : (ζ ^ k) ^ S.n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hφ, map_mul, map_pow, S.scaleL_embXG_branch _ _ hzn, S.scaleL_branchYe _ _ hzn, mul_pow,
      ← map_pow, ← pow_mul, ← pow_mul, mul_comm k j]
    ring
  rw [projL, Finset.sum_congr rfl hk, ← Finset.sum_mul, ← map_sum]
  have hw : ζ ^ j ≠ 1 := fun h ↦ by
    have := hζ.dvd_of_pow_eq_one j h
    exact absurd (Nat.le_of_dvd hj0 this) (by omega)
  have hwn : (ζ ^ j) ^ S.n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [geom_sum_eq hw, hwn, sub_self, zero_div, map_zero, zero_mul, mul_zero]

end SuperData

end Differential
