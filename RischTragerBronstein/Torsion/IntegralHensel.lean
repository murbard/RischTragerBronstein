import RischTragerBronstein.Torsion.StdCurve

/-!
# Integrality of Hensel roots

Let `ι : R → K` be an injective ring homomorphism (e.g. `ℤ_p → ℚ_p`). If `H ∈ R⟦T⟧[Y]`, the root
`y ∈ K⟦T⟧` of `H` is congruent to `ỹ ∈ R⟦T⟧` modulo `T^{A−B}`, and `H'(ỹ) = T^B u` with `u(0)` a
unit of `R` and `2B < A`, then `y` has coefficients in `R` (`root_integral`): each coefficient
`c_t` (`t ≥ A − B`) is `−[T^{t+B}] H(y_{<t}) / u(0)`.
-/

open Polynomial

namespace Curves

section Integral

variable {R K : Type*} [CommRing R] [Field K] (ι : R →+* K)

/-- Power series over `R`, pushed to `K`. -/
noncomputable abbrev psMap : PowerSeries R →+* PowerSeries K := PowerSeries.map ι

lemma coeff_trunc_mul_X_pow_dvd (y : PowerSeries K) (t : ℕ) :
    (PowerSeries.X : PowerSeries K) ^ t ∣ y - (PowerSeries.trunc t y : PowerSeries K) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro d hd
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hd, sub_self]

/-- **Integrality of the Hensel root.** -/
theorem root_integral (hι : Function.Injective ι) (HR : Polynomial (PowerSeries R))
    (y : PowerSeries K) (hy : (HR.map (psMap ι)).eval y = 0) (yR : PowerSeries R) (A B : ℕ)
    (hAB : 2 * B < A) (hyy : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ y - psMap ι yR)
    (uR : PowerSeries R) (hu : IsUnit (PowerSeries.constantCoeff uR))
    (hB : (derivative HR).eval yR = PowerSeries.X ^ B * uR) :
    ∀ t, ∃ c : R, ι c = PowerSeries.coeff t y := by
  classical
  have hu' : IsUnit (ι (PowerSeries.constantCoeff uR)) := hu.map ι
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < A - B
    · refine ⟨PowerSeries.coeff t yR, ?_⟩
      have := (PowerSeries.X_pow_dvd_iff.mp hyy) t ht
      rw [map_sub, sub_eq_zero] at this
      rw [this, psMap, PowerSeries.coeff_map]
    push Not at ht
    -- the truncation below `t`, lifted to `R`
    choose c hc using ih
    set ytR : PowerSeries R := ((∑ i ∈ Finset.range t,
      Polynomial.monomial i (if h : i < t then c i h else 0) : R[X]) : PowerSeries R) with hytR
    have hyt : psMap ι ytR = (PowerSeries.trunc t y : PowerSeries K) := by
      ext i
      rw [psMap, PowerSeries.coeff_map, hytR, Polynomial.coeff_coe, Polynomial.coeff_coe,
        PowerSeries.coeff_trunc, finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      split_ifs with hi
      · rw [Finset.sum_eq_single i (fun b _ hb ↦ if_neg hb) (by simp [hi]), if_pos rfl,
          dif_pos hi, hc i hi]
      · rw [Finset.sum_eq_zero fun b hb ↦ if_neg fun h ↦ hi (by rw [← h]; exact Finset.mem_range.mp hb),
          map_zero]
    set δ := y - psMap ι ytR with hδ
    have hδt : (PowerSeries.X : PowerSeries K) ^ t ∣ δ := by
      rw [hδ, hyt]; exact coeff_trunc_mul_X_pow_dvd y t
    set HK := HR.map (psMap ι) with hHK
    -- Taylor expansion at `y_{<t}`
    obtain ⟨k, hk⟩ := binomExpansion HK (psMap ι ytR) δ
    rw [hδ, add_sub_cancel, hy] at hk
    -- `H'(y_{<t}) = X^B u + X^{A−B} r`
    have hder : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣
        (derivative HK).eval (psMap ι ytR) - PowerSeries.X ^ B * psMap ι uR := by
      have h1 : (derivative HK).eval (psMap ι yR) = PowerSeries.X ^ B * psMap ι uR := by
        rw [hHK, Polynomial.derivative_map, eval_map, Polynomial.eval₂_hom, hB, map_mul, map_pow,
          PowerSeries.map_X]
      rw [← h1]
      have h2 : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ psMap ι ytR - y := by
        rw [hyt, ← neg_sub]; exact dvd_neg.mpr ((pow_dvd_pow _ ht).trans
          (coeff_trunc_mul_X_pow_dvd y t))
      have h3 := dvd_add h2 hyy
      rw [sub_add_sub_cancel] at h3
      exact h3.trans (sub_dvd_eval_sub _ _ _)
    obtain ⟨r, hr⟩ := hder
    have hkey : PowerSeries.coeff (t + B) (HK.eval (psMap ι ytR)) +
        ι (PowerSeries.constantCoeff uR) * PowerSeries.coeff t y = 0 := by
      have e := congrArg (PowerSeries.coeff (t + B)) hk
      rw [map_zero] at e
      obtain ⟨dq, hdq⟩ := hδt
      have hδ0 : PowerSeries.coeff t δ = PowerSeries.coeff t y := by
        rw [hδ, map_sub, hyt, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg (lt_irrefl t),
          sub_zero]
      have e2 : (derivative HK).eval (psMap ι ytR) * δ = PowerSeries.X ^ B * (psMap ι uR * δ) +
          PowerSeries.X ^ (A - B) * (r * δ) := by
        rw [show (derivative HK).eval (psMap ι ytR) = PowerSeries.X ^ B * psMap ι uR +
          PowerSeries.X ^ (A - B) * r by linear_combination hr]
        ring
      have e3 : PowerSeries.coeff (t + B) (PowerSeries.X ^ (A - B) * (r * δ)) = 0 := by
        rw [hdq, show r * (PowerSeries.X ^ t * dq) = PowerSeries.X ^ t * (r * dq) by ring,
          ← mul_assoc, ← pow_add, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
      have e4 : PowerSeries.coeff (t + B) (k * δ ^ 2) = 0 := by
        rw [hdq, mul_pow, ← pow_mul, show k * (PowerSeries.X ^ (t * 2) * dq ^ 2) =
          PowerSeries.X ^ (t * 2) * (k * dq ^ 2) by ring, PowerSeries.coeff_X_pow_mul',
          if_neg (by omega)]
      have e5 : PowerSeries.coeff (t + B) (PowerSeries.X ^ B * (psMap ι uR * δ)) =
          ι (PowerSeries.constantCoeff uR) * PowerSeries.coeff t y := by
        rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel, hdq,
          show psMap ι uR * (PowerSeries.X ^ t * dq) = PowerSeries.X ^ t * (psMap ι uR * dq) by ring,
          PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, ← hδ0, hdq,
          PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
          map_mul, psMap, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [map_add, map_add, e2, map_add, e3, e4, e5, add_zero, add_zero] at e
      exact e.symm
    -- solve for `c_t`
    set h0 := PowerSeries.coeff (t + B) (HR.eval ytR) with hh0
    have hmap : PowerSeries.coeff (t + B) (HK.eval (psMap ι ytR)) = ι h0 := by
      rw [hh0, hHK, eval_map, Polynomial.eval₂_hom, psMap, PowerSeries.coeff_map]
    refine ⟨-h0 * ↑hu.unit⁻¹, ?_⟩
    rw [map_mul, map_neg, ← hmap]
    have hinv : ι (↑hu.unit⁻¹ : R) * ι (PowerSeries.constantCoeff uR) = 1 := by
      rw [← map_mul, IsUnit.val_inv_mul, map_one]
    linear_combination (-(ι (↑hu.unit⁻¹ : R))) * hkey + PowerSeries.coeff t y * hinv

end Integral

end Curves
