import RischTragerBronstein.Curves.ProcRF

/-!
# Coefficients along certified branches

`coeff_phi_fin`, `coeff_phi_inf`: the Laurent coefficients of `φ(W/Q)` along a certified branch
are the computed `gi (divTrunc …)` values (below the precision); `coeff_derivation`,
`coeff_single_mul'`: coefficients of derivatives and of products with `dX̂/dT`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Laurent

variable {K : Type*} [Field K]

lemma coeff_single_mul' (c : ℤ) (r : K) (x : LaurentSeries K) (n : ℤ) :
    (single c r * x).coeff n = r * x.coeff (n - c) := by
  rw [show single c r = HahnSeries.C r * single c (1 : K) by
    rw [HahnSeries.C_apply, single_mul_single, zero_add, mul_one]]
  rw [mul_assoc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, LaurentSeries.coeff_single_mul,
    smul_eq_mul]

lemma coeff_derivation (z : LaurentSeries K) (j : ℤ) :
    (LaurentSeries.derivation z).coeff j = ((j + 1 : ℤ) : K) * z.coeff (j + 1) := by
  rw [LaurentSeries.derivation_apply, derivative_coeff]

lemma coeff_ofPS_gi {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ψ : F →+* K) (V : PowerSeries K) (D : CPoly F)
    (prec : ℕ) (hV : (PowerSeries.X : PowerSeries K) ^ prec ∣ V - thetaT ψ (toPoly D)) (m : ℤ)
    (hm : m < prec) : (HahnSeries.ofPowerSeries ℤ K V).coeff m = ψ (gi D m) := by
  rw [LaurentSeries.coeff_ofPS, gi]
  split_ifs with h1 h2 h2
  · omega
  · have := (PowerSeries.X_pow_dvd_iff.mp hV) m.toNat (by omega)
    rw [map_sub, coeff_thetaT, sub_eq_zero] at this
    exact this
  · rw [map_zero]
  · omega

end Laurent

section Phi

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Coefficients along a certified finite branch.** -/
theorem coeff_phi_fin (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (a : F) (N : ℕ) (hN : 0 < N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0)
    (yt : CPoly F) (prec : ℕ)
    (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (z : C⟮S.x⟯⟮S.y⟯) (W : BPoly F) (Q : CPoly F)
    (hz : (z : L) * aeval S.x ((toPoly Q).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀)))
    (hμ : ordC (compC Q (shiftC a N)) < (compC Q (shiftC a N)).length) (j : ℤ)
    (hj : j + ordC (compC Q (shiftC a N)) < prec) :
    (S.embG (branchSub N (algebraMap C K (ψ₀ a))) (branchSub_injective N hN _)
        (HahnSeries.ofPowerSeries ℤ K Y) hY z).coeff j =
      (algebraMap C K).comp ψ₀ (gi (divTrunc (bivEval W (shiftC a N) yt)
        ((compC Q (shiftC a N)).drop (ordC (compC Q (shiftC a N)))) prec)
          (j + ordC (compC Q (shiftC a N)))) := by
  obtain ⟨V, hV, hVa⟩ := S.phi_repr Fc ψ₀ hSF a N hN Y hY yt prec hy z W Q hz hμ
  rw [hV, LaurentSeries.coeff_single_mul, sub_neg_eq_add]
  exact coeff_ofPS_gi _ V _ prec hVa _ hj

/-- **Coefficients along a certified branch above infinity.** -/
theorem coeff_phi_inf (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (k N : ℕ) (hN : 0 < N) (w : PowerSeries K)
    (hY : (S.F.map (infSub N)).eval
      (single (-((k * N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F) (prec : ℕ)
    (hw : (PowerSeries.X : PowerSeries K) ^ prec ∣ w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt))
    (z : C⟮S.x⟯⟮S.y⟯) (W : BPoly F) (Q : CPoly F)
    (hz : (z : L) * aeval S.x ((toPoly Q).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀)))
    (DW : ℕ) (hWok : InvOK k DW 0 W) (hQ : 0 < Q.length) (hQl : Q.getD (Q.length - 1) 0 ≠ 0)
    (j : ℤ) (hj : j + ((N * DW : ℕ) : ℤ) - ((N * (Q.length - 1) : ℕ) : ℤ) < prec) :
    (S.embG (infSub N) (infSub_injective N hN)
        (single (-((k * N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY z).coeff j =
      (algebraMap C K).comp ψ₀ (gi (divTrunc (bivEval (invB W k DW) (shiftC 0 N) wt)
        (compC (reflectC (Q.length - 1) Q) (shiftC 0 N)) prec)
          (j + ((N * DW : ℕ) : ℤ) - ((N * (Q.length - 1) : ℕ) : ℤ))) := by
  obtain ⟨V, hV, hVa⟩ := S.phi_repr_inf Fc ψ₀ hSF k N hN w hY wt prec hw z W Q hz DW hWok hQ hQl
  rw [hV, LaurentSeries.coeff_single_mul]
  rw [show j - (-((N * DW : ℕ) : ℤ) + ((N * (Q.length - 1) : ℕ) : ℤ)) =
    j + ((N * DW : ℕ) : ℤ) - ((N * (Q.length - 1) : ℕ) : ℤ) by ring]
  exact coeff_ofPS_gi _ V _ prec hVa _ hj

end CurveData

end Phi

end Curves
