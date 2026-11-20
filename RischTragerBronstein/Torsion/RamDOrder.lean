import RischTragerBronstein.Torsion.RamCert

/-!
# The order of the basis denominator at a fibre modulo `p`

`lift_D_order`: if the coefficient of `D(α + T)` at its order `μ` reduces to a non-zero value
modulo `p`, then over `ℤ_p` the lift satisfies `D(α + X) = Xᵘ Q` with `Q(0)` a unit — the
hypothesis of `prime_step_places` for fibres where the integral basis has a pole.
-/

open Polynomial

namespace Curves

open CPoly Sup

section DOrder

variable {K : Type*} [Field K] [DecidableEq K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)


include hR in
/-- **The order of the denominator at a fibre is the same modulo `p`**: `D(α + X) = Xᵘ Q` over
`ℤ_p` with `Q(0)` a unit, when the coefficient of `D(α + T)` at its order reduces to non-zero. -/
lemma lift_D_order (Dc : CPoly K) (hok : ∀ c ∈ Dc, R.ok c = true) (a : K) (hoka : R.ok a = true)
    (hne : (compC (Dc.map R.red) (shiftC (R.red a) 1)).getD (muD Dc a 1) 0 ≠ 0) :
    ∃ μ : ℕ, ∃ Q : ℤ_[p][X], (toPoly (liftL R φ hR Dc)).comp (X + Polynomial.C (zL R φ hR a)) =
      X ^ μ * Q ∧ IsUnit (Q.eval 0) := by
  set P := (toPoly (liftL R φ hR Dc)).comp (X + Polynomial.C (zL R φ hR a)) with hP
  have hιi : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  have hPι : P.map (algebraMap ℤ_[p] ℚ_[p]) = (toPoly (compC Dc (shiftC a 1))).map φ := by
    rw [hP, Polynomial.map_comp, toPoly_liftL_map R φ hR _ hok, toPoly_compC, toPoly_shiftC,
      Polynomial.map_comp]
    simp [zL_map R φ hR hoka, add_comm]
  have hPz : P.map PadicInt.toZMod = toPoly (compC (Dc.map R.red) (shiftC (R.red a) 1)) := by
    rw [hP, Polynomial.map_comp, toPoly_liftL_red R φ hR _ hok, toPoly_compC, toPoly_shiftC]
    simp [zL_red R φ hR hoka, add_comm]
  set μ := muD Dc a 1
  have hdvd : (X : ℤ_[p][X]) ^ μ ∣ P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    apply hιi
    rw [map_zero, ← Polynomial.coeff_map, hPι, Polynomial.coeff_map, coeff_toPoly,
      getD_lt_ordC _ d hd, map_zero]
  obtain ⟨Q, hQ⟩ := hdvd
  refine ⟨μ, Q, hQ, Jac.isUnit_of_toZMod ?_⟩
  have h1 : Q.eval 0 = P.coeff μ := by
    rw [hQ, Polynomial.coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h ↦ absurd le_rfl h), Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
  rw [h1, ← Polynomial.coeff_map, hPz, coeff_toPoly]
  exact hne

end DOrder

end Curves
