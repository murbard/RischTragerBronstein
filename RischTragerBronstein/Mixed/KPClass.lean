import RischTragerBronstein.Mixed.KPLocal

/-!
# Exponent classes of Laurent series and the residue at a branch point

For `z ∈ K`, `z ≠ 0`, `scaleL z : K⸨X⸩ →+* K⸨X⸩` is the substitution `X ↦ z X`
(`∑ cₖ Xᵏ ↦ ∑ zᵏ cₖ Xᵏ`). With `z = ζ` a primitive `n`-th root of unity it commutes with the local
derivation `dS s` of a branch point (`s` a monomial of exponent `1 − n`, `ζ` constant since
`ζⁿ = 1`), and the average `P₀ = (1/n) ∑ₖ σᵏ` keeps exactly the coefficients at the exponents
divisible by `n`.

`residue_eq_zero_class`: if `F = dS s V + ∑ κᵢ dS s Uᵢ / Uᵢ` and `P₀ F = 0` (for instance `F` lives in
a non-zero exponent class), then `∑ κᵢ ord Uᵢ = 0` — the residue argument of `residue_eq_zero`,
applied to the class-`0` parts.
-/

open Polynomial HahnSeries LaurentSeries Differential

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- The coefficients of `X ↦ z X`. -/
noncomputable def scaleFun (z : K) (F : K⸨X⸩) : K⸨X⸩ where
  coeff k := z ^ k * F.coeff k
  isPWO_support' := F.isPWO_support.mono fun k hk ↦
    Function.mem_support.mpr fun h ↦ (Function.mem_support.mp hk) (by rw [h, mul_zero])

lemma coeff_scaleFun (z : K) (F : K⸨X⸩) (k : ℤ) : (scaleFun z F).coeff k = z ^ k * F.coeff k := rfl

lemma support_scaleFun (z : K) (F : K⸨X⸩) : (scaleFun z F).support ⊆ F.support := fun k hk ↦
  Function.mem_support.mpr fun h ↦ (Function.mem_support.mp hk) (by rw [coeff_scaleFun, h, mul_zero])

/-- The coefficient of a product over enlarged supports of both factors. -/
lemma coeff_mul_supp {x y : K⸨X⸩} {s t : Set ℤ} (hs : s.IsPWO) (ht : t.IsPWO) (hxs : x.support ⊆ s)
    (hyt : y.support ⊆ t) (a : ℤ) :
    (x * y).coeff a = ∑ ij ∈ Finset.antidiagonal hs ht a, x.coeff ij.1 * y.coeff ij.2 := by
  classical
  rw [HahnSeries.coeff_mul_left' hs hxs]
  refine Finset.sum_subset (fun ij hij ↦ ?_) (fun ij hij hn ↦ ?_)
  · rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨hij.1, hyt hij.2.1, hij.2.2⟩
  · rw [Finset.mem_antidiagonal] at hij hn
    have : y.coeff ij.2 = 0 := by
      by_contra h
      exact hn ⟨hij.1, Function.mem_support.mpr h, hij.2.2⟩
    rw [this, mul_zero]

/-- **The substitution `X ↦ z X`**, a ring homomorphism. -/
noncomputable def scaleL (z : K) (hz : z ≠ 0) : K⸨X⸩ →+* K⸨X⸩ where
  toFun := scaleFun z
  map_one' := by
    ext k
    change z ^ k * (1 : K⸨X⸩).coeff k = (1 : K⸨X⸩).coeff k
    rw [HahnSeries.coeff_one]
    split_ifs with h
    · rw [h, zpow_zero, one_mul]
    · rw [mul_zero]
  map_mul' F G := by
    ext k
    change z ^ k * (F * G).coeff k = (scaleFun z F * scaleFun z G).coeff k
    rw [coeff_mul_supp F.isPWO_support G.isPWO_support (support_scaleFun z F)
      (support_scaleFun z G), HahnSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [coeff_scaleFun, coeff_scaleFun, ← hij.2.2, zpow_add₀ hz]
    ring
  map_zero' := by ext k; rw [coeff_scaleFun, HahnSeries.coeff_zero, mul_zero]
  map_add' F G := by
    ext k
    rw [HahnSeries.coeff_add, coeff_scaleFun, coeff_scaleFun, coeff_scaleFun, HahnSeries.coeff_add,
      mul_add]

lemma coeff_scaleL (z : K) (hz : z ≠ 0) (F : K⸨X⸩) (k : ℤ) :
    (scaleL z hz F).coeff k = z ^ k * F.coeff k := rfl

lemma scaleL_C (z : K) (hz : z ≠ 0) (c : K) : scaleL z hz (HahnSeries.C c) = HahnSeries.C c := by
  ext k
  rw [coeff_scaleL, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs with h
  · rw [h, zpow_zero, one_mul]
  · rw [mul_zero]

lemma scaleL_single (z : K) (hz : z ≠ 0) (m : ℤ) (c : K) :
    scaleL z hz (single m c) = single m (z ^ m * c) := by
  ext k
  rw [coeff_scaleL, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

variable [CharZero K]

/-- `(σ F)′ = z · σ (F′)`. -/
lemma derivative_scaleL (z : K) (hz : z ≠ 0) (F : K⸨X⸩) :
    derivative K (scaleL z hz F) = HahnSeries.C z * scaleL z hz (derivative K F) := by
  ext k
  rw [derivative_coeff, coeff_scaleL, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
    coeff_scaleL, derivative_coeff, zpow_add_one₀ hz]
  ring

variable [Differential K]

/-- A root of unity is a constant. -/
lemma deriv_root_of_unity {ζ : K} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ′ = 0 := by
  have hζ0 : ζ ≠ 0 := fun h ↦ by rw [h, zero_pow hn.ne'] at hζ; exact zero_ne_one hζ
  have h := congrArg (fun w ↦ w′) hζ
  simp only [Derivation.leibniz_pow, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at h
  have h1 : (n : K) * ζ ^ (n - 1) ≠ 0 := mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ hζ0)
  rw [← mul_assoc] at h
  exact (mul_eq_zero.mp h).resolve_left h1

lemma coefDeriv_scaleL (z : K) (hz : z ≠ 0) (hz' : z′ = 0) (F : K⸨X⸩) :
    coefDeriv (scaleL z hz F) = scaleL z hz (coefDeriv F) := by
  have hc : ∀ k : ℤ, (z ^ k)′ = 0 := fun k ↦ by
    have : z ^ k ∈ constants K := zpow_mem (show z ∈ constants K from hz') k
    exact this
  ext k
  rw [coeff_coefDeriv, coeff_scaleL, coeff_scaleL, coeff_coefDeriv, Derivation.leibniz, hc,
    smul_zero, add_zero, smul_eq_mul]

/-- **`X ↦ ζ X` commutes with the derivation of a branch point.** -/
lemma dS_scaleL (ζ : K) (n : ℕ) (hn : 0 < n) (hζ : ζ ^ n = 1) (hζ0 : ζ ≠ 0) (c : K)
    (F : K⸨X⸩) :
    dS (single (1 - (n : ℤ)) c) (scaleL ζ hζ0 F) = scaleL ζ hζ0 (dS (single (1 - (n : ℤ)) c) F) := by
  have hζ' : ζ′ = 0 := deriv_root_of_unity hn hζ
  have hs : scaleL ζ hζ0 (single (1 - (n : ℤ)) c) = HahnSeries.C ζ * single (1 - (n : ℤ)) c := by
    rw [scaleL_single, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add]
    congr 1
    rw [zpow_sub₀ hζ0, zpow_one, zpow_natCast, hζ, div_one]
  rw [dS_apply, dS_apply, map_add, map_mul, coefDeriv_scaleL ζ hζ0 hζ', derivative_scaleL, hs]
  ring

/-- The average of the `n` substitutions `X ↦ ζᵏ X`: the part in the exponents divisible by
`n`. -/
noncomputable def projL (ζ : K) (hζ0 : ζ ≠ 0) (n : ℕ) (F : K⸨X⸩) : K⸨X⸩ :=
  HahnSeries.C ((n : K)⁻¹) * ∑ k ∈ Finset.range n, scaleL (ζ ^ k) (pow_ne_zero k hζ0) F

lemma coeff_projL (ζ : K) (n : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (hζ0 : ζ ≠ 0)
    (F : K⸨X⸩) (i : ℤ) : (projL ζ hζ0 n F).coeff i = if (n : ℤ) ∣ i then F.coeff i else 0 := by
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  rw [projL, coeff_C_mul, HahnSeries.coeff_sum]
  simp_rw [coeff_scaleL]
  rw [← Finset.sum_mul]
  have hswap : ∀ k : ℕ, (ζ ^ k) ^ i = (ζ ^ i) ^ k := fun k ↦ by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hswap]
  by_cases hdiv : (n : ℤ) ∣ i
  · rw [if_pos hdiv, (hζ.zpow_eq_one_iff_dvd i).mpr hdiv]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp
  · rw [if_neg hdiv]
    have hw : ζ ^ i ≠ 1 := fun h ↦ hdiv ((hζ.zpow_eq_one_iff_dvd i).mp h)
    have hwn : (ζ ^ i) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [geom_sum_eq hw, hwn, sub_self, zero_div, zero_mul, mul_zero]

/-- The projection commutes with the derivation of a branch point. -/
lemma dS_projL (ζ : K) (n : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (hζ0 : ζ ≠ 0) (c : K)
    (F : K⸨X⸩) :
    dS (single (1 - (n : ℤ)) c) (projL ζ hζ0 n F) = projL ζ hζ0 n (dS (single (1 - (n : ℤ)) c) F) := by
  have hC : dS (single (1 - (n : ℤ)) c) (HahnSeries.C ((n : K)⁻¹)) = 0 := by
    rw [dS_C, Derivation.leibniz_inv, Derivation.map_natCast, smul_zero, map_zero]
  rw [projL, projL, Derivation.leibniz, hC, smul_zero, add_zero, smul_eq_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact dS_scaleL (ζ ^ k) n hn (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    (pow_ne_zero k hζ0) c F

lemma projL_add (ζ : K) (hζ0 : ζ ≠ 0) (n : ℕ) (F G : K⸨X⸩) :
    projL ζ hζ0 n (F + G) = projL ζ hζ0 n F + projL ζ hζ0 n G := by
  rw [projL, projL, projL, ← mul_add, ← Finset.sum_add_distrib]
  simp only [map_add]

/-- **The residue at a branch point, for an integrand without class-`0` part.** -/
theorem residue_eq_zero_class {ι : Type*} (I : Finset ι) (ζ : K) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (hζ0 : ζ ≠ 0) (c : K) (hc : c ≠ 0) (F V : K⸨X⸩)
    (U : ι → K⸨X⸩) (κ : ι → K) (hU : ∀ i ∈ I, U i ≠ 0)
    (heq : F = dS (single (1 - (n : ℤ)) c) V +
      ∑ i ∈ I, HahnSeries.C (κ i) * (dS (single (1 - (n : ℤ)) c) (U i) * (U i)⁻¹))
    (hF : projL ζ hζ0 n F = 0) :
    ∑ i ∈ I, κ i * ((U i).order : K) = 0 := by
  set s : K⸨X⸩ := single (1 - (n : ℤ)) c with hs
  have hsord : s.order = 1 - n := HahnSeries.order_single hc
  have hs0 : s ≠ 0 := HahnSeries.single_ne_zero hc
  have hσ : s.order ≤ 0 := by rw [hsord]; omega
  set Λ := ∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹) with hΛ
  have hlog : ∀ k, Λ.coeff k = ∑ i ∈ I, κ i * (dS s (U i) * (U i)⁻¹).coeff k := fun k ↦ by
    rw [hΛ, HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ ↦ coeff_C_mul _ _ _
  have hΛbelow : ∀ k < -(n : ℤ), Λ.coeff k = 0 := fun k hk ↦ by
    rw [hlog]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).1 k (by rw [hsord]; omega), mul_zero]
  have hΛn : Λ.coeff (-(n : ℤ)) = (∑ i ∈ I, κ i * ((U i).order : K)) * s.coeff s.order := by
    rw [hlog, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [show (-(n : ℤ)) = s.order - 1 by rw [hsord]; ring,
      (coeff_dS_logDeriv s (U i) (hU i hi) hσ).2]
    ring
  -- the class-`0` parts
  have hP := congrArg (projL ζ hζ0 n) heq
  rw [hF, projL_add, ← dS_projL ζ n hn hζ hζ0 c] at hP
  set V₀ := projL ζ hζ0 n V with hV₀
  have hPΛ : ∀ k, (projL ζ hζ0 n Λ).coeff k = if (n : ℤ) ∣ k then Λ.coeff k else 0 :=
    coeff_projL ζ n hn hζ hζ0 Λ
  have hV₀c : ∀ k, V₀.coeff k ≠ 0 → (n : ℤ) ∣ k := fun k hk ↦ by
    by_contra hd
    rw [hV₀, coeff_projL ζ n hn hζ hζ0, if_neg hd] at hk
    exact hk rfl
  -- `V₀` has no pole
  have hV : V₀ = 0 ∨ 0 ≤ V₀.order := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hV0, hm⟩ := hcon
    have hdiv : (n : ℤ) ∣ V₀.order :=
      hV₀c _ ((not_congr HahnSeries.coeff_order_eq_zero).mpr hV0)
    have hle : V₀.order ≤ -(n : ℤ) := by
      obtain ⟨q, hq⟩ := hdiv
      rw [hq] at hm ⊢
      have : q < 0 := by
        by_contra h
        push Not at h
        have : (0 : ℤ) ≤ (n : ℤ) * q := mul_nonneg (by omega) h
        omega
      nlinarith
    obtain ⟨-, hlead⟩ := coeff_dS_pole s V₀ hV0 hm.ne hσ
    have hc0 := congrArg (fun G ↦ G.coeff (V₀.order - 1 + s.order)) hP
    simp only [HahnSeries.coeff_zero, HahnSeries.coeff_add] at hc0
    rw [hlead, hPΛ] at hc0
    have hsm : V₀.order - 1 + s.order < -(n : ℤ) := by rw [hsord]; omega
    rw [hΛbelow _ hsm] at hc0
    simp only [ite_self, add_zero] at hc0
    have h1 : (V₀.order : K) ≠ 0 := by exact_mod_cast hm.ne
    have h2 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs0
    have h3 : V₀.coeff V₀.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hV0
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 hc0.symm
  -- the coefficient at `−n`
  have hc0 := congrArg (fun G ↦ G.coeff (-(n : ℤ))) hP
  simp only [HahnSeries.coeff_zero, HahnSeries.coeff_add] at hc0
  rw [coeff_dS_regular s V₀ hV (by rw [hsord]; omega) hσ, zero_add, hPΛ,
    if_pos (dvd_neg.mpr dvd_rfl), hΛn] at hc0
  have h2 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs0
  exact (mul_eq_zero.mp hc0.symm).resolve_right h2

end LaurentSeries
