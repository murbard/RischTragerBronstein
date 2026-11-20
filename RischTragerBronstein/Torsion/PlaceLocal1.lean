import RischTragerBronstein.Torsion.PlaceAssemble
import RischTragerBronstein.Torsion.RootCheckComplete

/-!
# Local place data (1): the root checks of the place series

For a split fibre `G(a + Tᴺ, Y) = ∏ₖ (Y − yₖ)` with distinct roots:

* `eval_derivative_ne_zero`: `∂_Y G` does not vanish at a simple root of a split polynomial;
* `placeSer_deriv_ne_zero`: nor at the place series (level `e`), by the substitution `T ↦ T^{N/e}`;
* **`rootCheck_placeSer`**: the truncation of the place series to precision `d + prec`
  (`d = ord ∂_Y G`), with coefficients pulled back to `F`, passes `rootCheck`.
-/

open Polynomial HahnSeries

namespace Curves

open CPoly Sup LaurentSeries Differential

section Deriv

variable {L : Type*} [Field L]

/-- **A simple root of a split polynomial.** -/
lemma eval_derivative_ne_zero {n : ℕ} (r : Fin n → L) (hr : Function.Injective r) (j : Fin n) :
    (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r j) ≠ 0 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Polynomial.derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_prod,
    eval_one]
  exact Finset.prod_ne_zero_iff.mpr fun k hk ↦ by
    simpa [sub_eq_zero] using fun h ↦ (Finset.ne_of_mem_erase hk) (hr h).symm

end Deriv

section Place

variable {K : Type*} [Field K] {n : ℕ} {G : K[X][X]}
variable (Φ : SplitFibre (C := K) (K := K) G n) {ζ : K} (hζ : IsPrimitiveRoot ζ Φ.N)

/-- **`∂_Y G` does not vanish along a place series.** -/
lemma placeSer_deriv_ne_zero (k : Fin n) :
    (derivative (G.map (branchSub (Φ.period hζ k) Φ.a))).eval
      (ofPowerSeries ℤ K (Φ.placeSer hζ k)) ≠ 0 := by
  have hs := Φ.sIdx_pos hζ k
  intro h0
  have h1 := congrArg (lsub (Φ.sIdx hζ k) hs) h0
  rw [map_zero, ← eval₂_at_apply, ← eval_map, ← Polynomial.derivative_map, Polynomial.map_map,
    lsub_comp_branchSub, ← Φ.ofPS_y_eq_lsub hζ k, mul_comm, Φ.sIdx_mul hζ k, Φ.split] at h1
  exact eval_derivative_ne_zero _ (fun a b h ↦ Φ.inj (HahnSeries.ofPowerSeries_injective h)) k h1

end Place

section Check

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K] (ψ : F →+* K)

lemma ofPS_psSubR (e : ℕ) (a : K) (P : K[X]) :
    ofPowerSeries ℤ K (psSubR e a P) = branchSub (C := K) (K := K) e a P := by
  rw [branchSub_eq_psSub]
  congr 1
  simp [psSubR, psSub, Algebra.algebraMap_self]

lemma repEq_map_ofPS (Fc : BPoly F) (a : F) (e : ℕ) :
    (repEq ψ Fc a e).map (ofPowerSeries ℤ K) =
      ((toB Fc).map (mapRingHom ψ)).map (branchSub (C := K) (K := K) e (ψ a)) := by
  rw [repEq, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun P ↦ ofPS_psSubR e (ψ a) P

lemma exists_order (D : PowerSeries K) (hD : D ≠ 0) :
    ∃ d, (∀ i < d, PowerSeries.coeff i D = 0) ∧ PowerSeries.coeff d D ≠ 0 := by
  classical
  have hex : ∃ i, PowerSeries.coeff i D ≠ 0 := by
    by_contra h; push Not at h; exact hD (PowerSeries.ext fun i ↦ by simpa using h i)
  exact ⟨Nat.find hex, fun i hi ↦ by simpa using Nat.find_min hex hi, Nat.find_spec hex⟩

/-- **The truncated place series passes the root check.** -/
theorem rootCheck_trunc (Fc : BPoly F) (a : F) (e : ℕ) (ρ : PowerSeries K)
    (hρ : (((toB Fc).map (mapRingHom ψ)).map (branchSub (C := K) (K := K) e (ψ a))).eval
      (ofPowerSeries ℤ K ρ) = 0)
    (hd : (derivative (((toB Fc).map (mapRingHom ψ)).map (branchSub (C := K) (K := K) e (ψ a)))).eval
      (ofPowerSeries ℤ K ρ) ≠ 0) :
    ∃ d, ∀ prec, d < prec → ∀ pre : K → F,
      (∀ i < d + prec, ψ (pre (PowerSeries.coeff i ρ)) = PowerSeries.coeff i ρ) →
      rootCheck Fc a e prec ((List.range (d + prec)).map fun i ↦ pre (PowerSeries.coeff i ρ)) = true := by
  have hinj : Function.Injective (ofPowerSeries ℤ K) := HahnSeries.ofPowerSeries_injective
  have hev : ∀ Q : (PowerSeries K)[X], ofPowerSeries ℤ K (Q.eval ρ) =
      (Q.map (ofPowerSeries ℤ K)).eval (ofPowerSeries ℤ K ρ) := fun Q ↦ by
    rw [eval_map, eval₂_at_apply]
  have hρ' : (repEq ψ Fc a e).eval ρ = 0 := hinj (by rw [hev, repEq_map_ofPS, hρ, map_zero])
  have hD : (derivative (repEq ψ Fc a e)).eval ρ ≠ 0 := fun h ↦ hd (by
    rw [← repEq_map_ofPS, Polynomial.derivative_map, ← hev, h, map_zero])
  obtain ⟨d, hd0, hd1⟩ := exists_order _ hD
  refine ⟨d, fun prec hdp pre hpre ↦ rootCheck_of_root ψ ρ hρ' d hd0 hd1 hdp ?_⟩
  refine PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ ?_
  rw [map_sub, coeff_thetaT, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range, hpre i hi, sub_self]

end Check

end Curves
