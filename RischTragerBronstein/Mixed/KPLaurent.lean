import RischTragerBronstein.Algebraic.SuperExact

/-!
# Laurent series over a differential field: the derivations `δ + s d/dX`

For a differential field `K`, `coefDeriv` differentiates the coefficients of a Laurent series, and
`dS s = coefDeriv + s · d/dX` is the derivation with `dS s X = s` (`s` any Laurent series). These are
the local expansions of a derivation of a function field over a *differential* base: at a place
`t = α + X` of `F(t)` with `t′ = η`, the derivation is `dS (η − α′)`; at a branch point
`t = e + Xⁿ` it is `dS ((η − e′)/n · X^{1−n})`.

The coefficient facts used by the local analysis (`s` of order `σ ≤ 0`):

* `coeff_dS_pole`: a pole of order `m ≠ 0` of `f` gives `dS s f` the lowest coefficient
  `m · s_σ · f_m` at `m − 1 + σ`;
* `coeff_dS_regular`: for a regular `f`, `dS s f` has no coefficient below `σ`;
* `coeff_dS_logDeriv`: `dS s u / u` has no coefficient below `σ − 1`, and at `σ − 1` it is
  `ord u · s_σ`.
-/

open HahnSeries Differential

namespace LaurentSeries

variable {K : Type*} [Field K] [Differential K]

/-- Differentiating the coefficients. -/
noncomputable def coefDerivFun (f : K⸨X⸩) : K⸨X⸩ := f.map (Differential.deriv : Derivation ℤ K K)

lemma coeff_coefDerivFun (f : K⸨X⸩) (k : ℤ) : (coefDerivFun f).coeff k = (f.coeff k)′ := rfl

lemma coefDerivFun_add (f g : K⸨X⸩) : coefDerivFun (f + g) = coefDerivFun f + coefDerivFun g := by
  ext k
  rw [HahnSeries.coeff_add, coeff_coefDerivFun, coeff_coefDerivFun, coeff_coefDerivFun,
    HahnSeries.coeff_add, map_add]

lemma support_coefDerivFun (f : K⸨X⸩) : (coefDerivFun f).support ⊆ f.support :=
  HahnSeries.support_map_subset f (Differential.deriv : Derivation ℤ K K).toAddMonoidHom.toZeroHom

lemma coefDerivFun_mul (f g : K⸨X⸩) :
    coefDerivFun (f * g) = f * coefDerivFun g + g * coefDerivFun f := by
  ext k
  rw [coeff_coefDerivFun, HahnSeries.coeff_add, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_right' g.isPWO_support (support_coefDerivFun g) (a := k),
    mul_comm g, HahnSeries.coeff_mul_left' f.isPWO_support (support_coefDerivFun f)
      (a := k), map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [Derivation.leibniz, coeff_coefDerivFun, coeff_coefDerivFun, smul_eq_mul, smul_eq_mul]
  ring

/-- **The coefficient derivation.** -/
noncomputable def coefDeriv : Derivation ℤ K⸨X⸩ K⸨X⸩ where
  toFun := coefDerivFun
  map_add' := coefDerivFun_add
  map_smul' m f := by
    rw [RingHom.id_apply]
    ext k
    rw [Algebra.smul_def, HahnSeries.coeff_smul]
    show ((algebraMap ℤ K⸨X⸩ m * f).coeff k)′ = m • (f.coeff k)′
    rw [eq_intCast (algebraMap ℤ K⸨X⸩) m, ← zsmul_eq_mul, HahnSeries.coeff_smul, map_zsmul]
  map_one_eq_zero' := by
    change coefDerivFun 1 = 0
    ext k
    rw [coeff_coefDerivFun, HahnSeries.coeff_one, HahnSeries.coeff_zero]
    split_ifs <;> simp
  leibniz' f g := by
    change coefDerivFun (f * g) = f • coefDerivFun g + g • coefDerivFun f
    rw [smul_eq_mul, smul_eq_mul]
    exact coefDerivFun_mul f g

lemma coefDeriv_apply (f : K⸨X⸩) : coefDeriv f = coefDerivFun f := rfl

lemma coeff_coefDeriv (f : K⸨X⸩) (k : ℤ) : (coefDeriv f).coeff k = (f.coeff k)′ := rfl

lemma coefDeriv_single (m : ℤ) (c : K) :
    coefDeriv (HahnSeries.single m c : K⸨X⸩) = HahnSeries.single m c′ := by
  ext k
  rw [coeff_coefDeriv, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

lemma coefDeriv_C (c : K) : coefDeriv (HahnSeries.C c : K⸨X⸩) = HahnSeries.C c′ := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coefDeriv_single]

variable [CharZero K]

/-- **The derivation `δ + s d/dX`.** -/
noncomputable def dS (s : K⸨X⸩) : Derivation ℤ K⸨X⸩ K⸨X⸩ where
  toFun f := coefDeriv f + s * derivative K f
  map_add' f g := by rw [map_add, map_add]; ring
  map_smul' m f := by
    rw [RingHom.id_apply, Algebra.smul_def, eq_intCast (algebraMap ℤ K⸨X⸩) m, zsmul_eq_mul]
    have h1 : coefDeriv (m : K⸨X⸩) = 0 := by
      rw [← eq_intCast (algebraMap ℤ K⸨X⸩) m, Derivation.map_algebraMap]
    have h2 : derivative K (m : K⸨X⸩) = 0 := by
      rw [show (m : K⸨X⸩) = HahnSeries.C (m : K) by simp, derivative_laurent_C]
    rw [coefDeriv.leibniz, derivative_mul, h1, h2, smul_eq_mul, smul_eq_mul]
    ring
  map_one_eq_zero' := by
    change coefDeriv 1 + s * derivative K 1 = 0
    rw [coefDeriv.map_one_eq_zero, derivative_one, mul_zero, add_zero]
  leibniz' f g := by
    change coefDeriv (f * g) + s * derivative K (f * g) =
      f • (coefDeriv g + s * derivative K g) + g • (coefDeriv f + s * derivative K f)
    rw [coefDeriv.leibniz, derivative_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

lemma dS_apply (s f : K⸨X⸩) : dS s f = coefDeriv f + s * derivative K f := rfl

lemma dS_C (s : K⸨X⸩) (c : K) : dS s (HahnSeries.C c : K⸨X⸩) = HahnSeries.C c′ := by
  rw [dS_apply, coefDeriv_C, derivative_laurent_C, mul_zero, add_zero]

lemma coeff_coefDeriv_of_lt {f : K⸨X⸩} {k : ℤ} (hk : k < f.order) : (coefDeriv f).coeff k = 0 := by
  rw [coeff_coefDeriv, HahnSeries.coeff_eq_zero_of_lt_order hk]
  exact Differential.deriv.map_zero

/-- The formal derivative of a regular series has no pole. -/
lemma coeff_derivative_neg {f : K⸨X⸩} (hf : f = 0 ∨ 0 ≤ f.order) {k : ℤ} (hk : k < 0) :
    (derivative K f).coeff k = 0 := by
  rw [derivative_coeff]
  rcases hf with rfl | hf
  · simp
  · by_cases hk1 : k = -1
    · subst hk1; simp
    · rw [HahnSeries.coeff_eq_zero_of_lt_order (by omega), mul_zero]

/-- Vanishing of the coefficients of a product below `a + b`. -/
lemma coeff_mul_eq_zero_of_lt {x y : K⸨X⸩} {a b : ℤ}
    (hx : ∀ k < a, x.coeff k = 0) (hy : ∀ k < b, y.coeff k = 0) {k : ℤ} (hk : k < a + b) :
    (x * y).coeff k = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  by_cases h1 : ij.1 < a
  · rw [hx _ h1, zero_mul]
  · rw [hy _ (by omega), mul_zero]

/-- The coefficient of a product at `a + b`, when nothing lies below `a` and `b`. -/
lemma coeff_mul_add {x y : K⸨X⸩} {a b : ℤ}
    (hx : ∀ k < a, x.coeff k = 0) (hy : ∀ k < b, y.coeff k = 0) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  classical
  rw [HahnSeries.coeff_mul]
  by_cases hxa : x.coeff a = 0
  · rw [hxa, zero_mul]
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    rw [Finset.mem_antidiagonal] at hij
    by_cases h1 : ij.1 < a
    · rw [hx _ h1, zero_mul]
    · by_cases h2 : ij.1 = a
      · rw [h2, hxa, zero_mul]
      · rw [hy _ (by omega), mul_zero]
  by_cases hyb : y.coeff b = 0
  · rw [hyb, mul_zero]
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    rw [Finset.mem_antidiagonal] at hij
    by_cases h1 : ij.1 < a
    · rw [hx _ h1, zero_mul]
    · by_cases h2 : ij.1 = a
      · have : ij.2 = b := by omega
        rw [this, hyb, mul_zero]
      · rw [hy _ (by omega), mul_zero]
  rw [Finset.sum_eq_single (a, b)]
  · intro ij hij hne
    rw [Finset.mem_antidiagonal] at hij
    by_cases h1 : ij.1 < a
    · rw [hx _ h1, zero_mul]
    · by_cases h2 : ij.1 = a
      · exact absurd (Prod.ext h2 (by omega)) hne
      · rw [hy _ (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr ⟨Function.mem_support.mpr hxa,
      Function.mem_support.mpr hyb, rfl⟩) h

lemma coeff_lt_order_eq_zero (f : K⸨X⸩) : ∀ k < f.order, f.coeff k = 0 :=
  fun _ hk ↦ HahnSeries.coeff_eq_zero_of_lt_order hk

/-- **A pole propagates**: for `f` of order `m ≠ 0` and `s` of order `σ ≤ 0`, the lowest
coefficient of `dS s f` is `m · s_σ · f_m`, at `m − 1 + σ`. -/
theorem coeff_dS_pole (s f : K⸨X⸩) (hf : f ≠ 0) (hm : f.order ≠ 0) (hσ : s.order ≤ 0) :
    (∀ k < f.order - 1 + s.order, (dS s f).coeff k = 0) ∧
      (dS s f).coeff (f.order - 1 + s.order) =
        (f.order : K) * s.coeff s.order * f.coeff f.order := by
  have hd : ∀ k < f.order - 1, (derivative K f).coeff k = 0 := fun k hk ↦ by
    rw [derivative_coeff, HahnSeries.coeff_eq_zero_of_lt_order (by omega), mul_zero]
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · rw [dS_apply, HahnSeries.coeff_add, coeff_coefDeriv_of_lt (by omega), zero_add]
    exact coeff_mul_eq_zero_of_lt (coeff_lt_order_eq_zero s) hd (by omega)
  · rw [dS_apply, HahnSeries.coeff_add, coeff_coefDeriv_of_lt (by omega), zero_add,
      show f.order - 1 + s.order = s.order + (f.order - 1) by ring,
      coeff_mul_add (coeff_lt_order_eq_zero s) hd, derivative_coeff, sub_add_cancel]
    ring

/-- **A regular series**: `dS s f` has no coefficient below `σ`. -/
theorem coeff_dS_regular (s f : K⸨X⸩) (hf : f = 0 ∨ 0 ≤ f.order) {k : ℤ} (hk : k < s.order)
    (hσ : s.order ≤ 0) : (dS s f).coeff k = 0 := by
  rw [dS_apply, HahnSeries.coeff_add]
  have h1 : (coefDeriv f).coeff k = 0 := by
    rcases hf with rfl | hf
    · rw [map_zero]; rfl
    · exact coeff_coefDeriv_of_lt (by omega)
  rw [h1, zero_add]
  exact coeff_mul_eq_zero_of_lt (a := s.order) (b := 0) (coeff_lt_order_eq_zero s)
    (fun j hj ↦ coeff_derivative_neg hf hj) (by omega)

/-- The formal logarithmic derivative `u′/u`: nothing below `−1`, and `ord u` at `−1`. -/
lemma coeff_derivative_div (u : K⸨X⸩) (hu : u ≠ 0) :
    (∀ k < -1, (derivative K u * u⁻¹).coeff k = 0) ∧
      (derivative K u * u⁻¹).coeff (-1) = (u.order : K) := by
  have hinv : ∀ k < -u.order, (u⁻¹).coeff k = 0 := by
    have h := coeff_lt_order_eq_zero u⁻¹
    rwa [order_inv' u hu] at h
  have hd : ∀ k < u.order - 1, (derivative K u).coeff k = 0 := fun k hk ↦ by
    rw [derivative_coeff, HahnSeries.coeff_eq_zero_of_lt_order (by omega), mul_zero]
  refine ⟨fun k hk ↦ coeff_mul_eq_zero_of_lt hd hinv (by omega), ?_⟩
  rw [show (-1 : ℤ) = (u.order - 1) + -u.order by ring, coeff_mul_add hd hinv, derivative_coeff,
    sub_add_cancel]
  have h1 : u.coeff u.order * (u⁻¹).coeff (-u.order) = 1 := by
    have := coeff_mul_add (x := u) (y := u⁻¹) (coeff_lt_order_eq_zero u) hinv
    rw [add_neg_cancel, mul_inv_cancel₀ hu] at this
    rw [← this, HahnSeries.coeff_one, if_pos rfl]
  rw [mul_assoc, h1, mul_one]

/-- **The logarithmic derivative**: `dS s u / u` has nothing below `σ − 1`, and `ord u · s_σ` at
`σ − 1`. -/
theorem coeff_dS_logDeriv (s u : K⸨X⸩) (hu : u ≠ 0) (hσ : s.order ≤ 0) :
    (∀ k < s.order - 1, (dS s u * u⁻¹).coeff k = 0) ∧
      (dS s u * u⁻¹).coeff (s.order - 1) = (u.order : K) * s.coeff s.order := by
  have hinv : ∀ k < -u.order, (u⁻¹).coeff k = 0 := by
    have h := coeff_lt_order_eq_zero u⁻¹
    rwa [order_inv' u hu] at h
  have hc : ∀ k < u.order, (coefDeriv u).coeff k = 0 := fun k hk ↦ coeff_coefDeriv_of_lt hk
  have hc0 : ∀ k < 0, (coefDeriv u * u⁻¹).coeff k = 0 := fun k hk ↦
    coeff_mul_eq_zero_of_lt hc hinv (by omega)
  obtain ⟨hR, hR1⟩ := coeff_derivative_div u hu
  have hsplit : dS s u * u⁻¹ = coefDeriv u * u⁻¹ + s * (derivative K u * u⁻¹) := by
    rw [dS_apply]; ring
  rw [hsplit]
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · rw [HahnSeries.coeff_add, hc0 k (by omega), zero_add]
    exact coeff_mul_eq_zero_of_lt (coeff_lt_order_eq_zero s) hR (by omega)
  · rw [HahnSeries.coeff_add, hc0 _ (by omega), zero_add,
      show s.order - 1 = s.order + -1 by ring, coeff_mul_add (coeff_lt_order_eq_zero s) hR, hR1]
    ring

end LaurentSeries
