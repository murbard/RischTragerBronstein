import RischTragerBronstein.Mixed.KPEmbed

/-!
# Residues of a Liouville form at a place over a differential base

`residue_eq_zero`: in Laurent series over a differential field, with the derivation `dS s`
(`s` of order `σ ≤ 0`), if `F = dS s V + ∑ κᵢ dS s Uᵢ / Uᵢ` and `F` has no coefficient below `σ`,
then `∑ κᵢ ord Uᵢ = 0`. (A pole of `V` would propagate below `σ − 1`, where nothing else
lives; then the coefficient at `σ − 1` is `s_σ ∑ κᵢ ord Uᵢ`.)

The local derivations: at an ordinary point `x = α + X`, `s = η − α′` (`dS_shift`); at a branch
point `x = e + Xⁿ`, `s = (η − e′)/n · X^{1−n}` (`dS_branch`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

namespace LaurentSeries

variable {K : Type*} [Field K] [Differential K] [CharZero K]

lemma coeff_C_mul (c : K) (f : K⸨X⸩) (k : ℤ) : (HahnSeries.C c * f).coeff k = c * f.coeff k := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/-- **The residue of a Liouville form vanishes where the integrand has no pole.** -/
theorem residue_eq_zero {ι : Type*} (I : Finset ι) (s F V : K⸨X⸩) (U : ι → K⸨X⸩) (κ : ι → K)
    (hs : s ≠ 0) (hσ : s.order ≤ 0) (hU : ∀ i ∈ I, U i ≠ 0)
    (heq : F = dS s V + ∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹))
    (hF : ∀ k < s.order, F.coeff k = 0) :
    ∑ i ∈ I, κ i * ((U i).order : K) = 0 := by
  have hlog : ∀ k, (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k =
      ∑ i ∈ I, κ i * (dS s (U i) * (U i)⁻¹).coeff k := fun k ↦ by
    rw [HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ ↦ coeff_C_mul _ _ _
  have hlogBelow : ∀ k < s.order - 1,
      (∑ i ∈ I, HahnSeries.C (κ i) * (dS s (U i) * (U i)⁻¹)).coeff k = 0 := fun k hk ↦ by
    rw [hlog]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).1 k hk, mul_zero]
  -- `V` has no pole
  have hV : V = 0 ∨ 0 ≤ V.order := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hV0, hm⟩ := hcon
    obtain ⟨-, hlead⟩ := coeff_dS_pole s V hV0 hm.ne hσ
    have hc : F.coeff (V.order - 1 + s.order) = (dS s V + ∑ i ∈ I, HahnSeries.C (κ i) *
        (dS s (U i) * (U i)⁻¹)).coeff (V.order - 1 + s.order) :=
      congrArg (fun G ↦ G.coeff (V.order - 1 + s.order)) heq
    rw [HahnSeries.coeff_add, hlead, hlogBelow _ (by omega), add_zero,
      hF _ (by omega)] at hc
    have h1 : (V.order : K) ≠ 0 := by exact_mod_cast hm.ne
    have h2 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs
    have h3 : V.coeff V.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hV0
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 hc.symm
  -- the coefficient at `σ − 1`
  have hc : F.coeff (s.order - 1) = (dS s V + ∑ i ∈ I, HahnSeries.C (κ i) *
      (dS s (U i) * (U i)⁻¹)).coeff (s.order - 1) := congrArg (fun G ↦ G.coeff (s.order - 1)) heq
  rw [HahnSeries.coeff_add, coeff_dS_regular s V hV (by omega) hσ, zero_add, hlog,
    hF _ (by omega)] at hc
  have hs0 : s.coeff s.order ≠ 0 := (not_congr HahnSeries.coeff_order_eq_zero).mpr hs
  have : (∑ i ∈ I, κ i * ((U i).order : K)) * s.coeff s.order = 0 := by
    rw [Finset.sum_mul, hc]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(coeff_dS_logDeriv s (U i) (hU i hi) hσ).2]
    ring
  exact (mul_eq_zero.mp this).resolve_right hs0

lemma coefDeriv_single_one (k : ℤ) : coefDeriv (single k (1 : K) : K⸨X⸩) = 0 := by
  rw [coefDeriv_single, Derivation.map_one_eq_zero, HahnSeries.single_eq_zero]

lemma derivative_single_one (k : ℤ) :
    derivative K (single k (1 : K) : K⸨X⸩) = single (k - 1) (k : K) := by
  rw [← derivation_apply, Differential.derivation_single]

/-- **The derivation at an ordinary point** `x = α + X`: `dS (η − α′)`. -/
lemma dS_shift (α η : K) :
    dS (HahnSeries.C (η - α′)) (HahnSeries.C α + single 1 1) = HahnSeries.C η := by
  rw [map_add, dS_C, dS_apply, coefDeriv_single_one, derivative_single_one, zero_add,
    sub_self, Int.cast_one, ← HahnSeries.C_apply, map_one, mul_one, ← map_add]
  congr 1
  ring

/-- **The derivation at a branch point** `x = e + Xⁿ`: `dS ((η − e′)/n · X^{1−n})`. -/
lemma dS_branch (e η : K) (n : ℕ) (hn : 0 < n) :
    dS (HahnSeries.C ((η - e′) / n) * single (1 - (n : ℤ)) 1) (HahnSeries.C e + single (n : ℤ) 1) =
      HahnSeries.C η := by
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  rw [map_add, dS_C, dS_apply, coefDeriv_single_one, derivative_single_one, zero_add, mul_assoc,
    HahnSeries.single_mul_single, show (1 - (n : ℤ)) + ((n : ℤ) - 1) = 0 by ring, one_mul,
    ← HahnSeries.C_apply, ← map_mul, ← map_add]
  congr 1
  push_cast
  field_simp
  ring

/-- The order of the local derivation at a branch point. -/
lemma order_branch_s (c : K) (hc : c ≠ 0) (n : ℕ) :
    (HahnSeries.C c * single (1 - (n : ℤ)) (1 : K) : K⸨X⸩).order = 1 - n := by
  rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one,
    HahnSeries.order_single hc]

end LaurentSeries
