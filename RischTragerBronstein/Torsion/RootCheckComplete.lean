import RischTragerBronstein.Torsion.RamRoots

/-!
# Completeness of the root check

`rootCheck Fc a N prec y` accepts an approximation `y` of a root of `F(a + Tᴺ, Y)`. It is
complete:

* `rootCheck_of_facts`: the converse of `rootCheck_facts` (the truncated evaluations agree with
  the exact ones below the precision);
* **`rootCheck_of_root`**: if `ρ` is a root in `K⟦T⟧` (coefficients through any `ψ : F → K`)
  with `ord F_Y(ρ) = d < prec` and `y ≡ ρ (mod T^{d + prec})`, the check passes.

So exact branch data to precision `d + prec` always pass; this is the first step towards the
completeness of the place search.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Facts

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The converse of `rootCheck_facts`.** -/
theorem rootCheck_of_facts {Fc : BPoly F} {a : F} {N prec : ℕ} {y : CPoly F}
    (h1 : ordC (bivEval (derivYB Fc) (shiftC a N) y) < prec)
    (h2 : ordC (bivEval (derivYB Fc) (shiftC a N) y) < (bivEval (derivYB Fc) (shiftC a N) y).length)
    (h3 : ∀ i < ordC (bivEval (derivYB Fc) (shiftC a N) y) + prec,
      (bivEval Fc (shiftC a N) y).getD i 0 = 0) :
    rootCheck Fc a N prec y = true := by
  set DT := bivEvalT (derivYB Fc) (shiftC a N) y prec with hDT
  set D := bivEval (derivYB Fc) (shiftC a N) y with hD
  have hag : ∀ i < prec, D.getD i 0 = DT.getD i 0 :=
    getD_eq_of_X_pow_dvd (bivEvalT_dvd _ _ _ _)
  have hne : DT.getD (ordC D) 0 ≠ 0 := by rw [← hag _ h1]; exact getD_ordC D h2
  have ho : ordC DT = ordC D := ordC_eq_of
    (fun i hi ↦ by rw [← hag i (by omega)]; exact getD_lt_ordC D i hi) hne
  simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨by rw [← hDT, ho]; exact h1, ?_⟩, fun i hi ↦ ?_⟩
  · rw [← hDT, ho]
    by_contra hl
    exact hne (List.getD_eq_default _ _ (by omega))
  · rw [← hDT, ho] at hi ⊢
    rw [← getD_eq_of_X_pow_dvd (bivEvalT_dvd Fc (shiftC a N) y (ordC D + prec)) i hi]
    exact h3 i hi

end Facts

section Root

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

/-- **Exact roots pass the check**: an approximation of a root `ρ` to precision
`ord F_Y(ρ) + prec` (with `ord F_Y(ρ) < prec`) is accepted. -/
theorem rootCheck_of_root (ψ : F →+* K) {Fc : BPoly F} {a : F} {N prec : ℕ} {y : CPoly F}
    (ρ : PowerSeries K) (hρ : (repEq ψ Fc a N).eval ρ = 0) (d : ℕ)
    (hd0 : ∀ i < d, PowerSeries.coeff i ((derivative (repEq ψ Fc a N)).eval ρ) = 0)
    (hd1 : PowerSeries.coeff d ((derivative (repEq ψ Fc a N)).eval ρ) ≠ 0) (hdp : d < prec)
    (hy : (PowerSeries.X : PowerSeries K) ^ (d + prec) ∣ ρ - thetaT ψ (toPoly y)) :
    rootCheck Fc a N prec y = true := by
  set D := bivEval (derivYB Fc) (shiftC a N) y with hD
  set H := bivEval Fc (shiftC a N) y with hH
  -- the derivative along `y` agrees with the derivative along `ρ` below `d + prec`
  have hDy : thetaT ψ (toPoly D) = (derivative (repEq ψ Fc a N)).eval (thetaT ψ (toPoly y)) :=
    (repEq_deriv ψ Fc a N y).symm
  have hdvdD : (PowerSeries.X : PowerSeries K) ^ (d + prec) ∣
      (derivative (repEq ψ Fc a N)).eval ρ - thetaT ψ (toPoly D) := by
    rw [hDy]
    exact hy.trans (sub_dvd_eval_sub _ _ _)
  have hcD : ∀ i < d + prec, ψ (D.getD i 0) =
      PowerSeries.coeff i ((derivative (repEq ψ Fc a N)).eval ρ) := by
    intro i hi
    rw [← coeff_thetaT]
    obtain ⟨r, hr⟩ := hdvdD
    have := congrArg (PowerSeries.coeff i) hr
    rw [map_sub, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)] at this
    exact (sub_eq_zero.mp this).symm
  have hD0 : ∀ i < d, D.getD i 0 = 0 := fun i hi ↦ ψ.injective (by
    rw [hcD i (by omega), hd0 i hi, map_zero])
  have hD1 : D.getD d 0 ≠ 0 := fun h ↦ hd1 (by rw [← hcD d (by omega), h, map_zero])
  have ho : ordC D = d := ordC_eq_of hD0 hD1
  -- the value along `y` vanishes below `d + prec`
  have hHy : thetaT ψ (toPoly H) = (repEq ψ Fc a N).eval (thetaT ψ (toPoly y)) :=
    thetaT_bivEval' ψ Fc a N y
  have hdvdH : (PowerSeries.X : PowerSeries K) ^ (d + prec) ∣ thetaT ψ (toPoly H) := by
    rw [hHy, ← sub_zero ((repEq ψ Fc a N).eval (thetaT ψ (toPoly y))), ← hρ]
    exact (dvd_sub_comm.mp hy).trans (sub_dvd_eval_sub _ _ _)
  refine rootCheck_of_facts (by rw [ho]; exact hdp) ?_ (fun i hi ↦ ?_)
  · rw [ho]
    by_contra hl
    exact hD1 (List.getD_eq_default _ _ (not_lt.mp hl))
  · rw [ho] at hi
    refine ψ.injective ?_
    rw [map_zero, ← coeff_thetaT]
    obtain ⟨r, hr⟩ := hdvdH
    rw [hr, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

end Root

end Curves
