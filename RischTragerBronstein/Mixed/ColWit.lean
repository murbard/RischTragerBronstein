import RischTragerBronstein.Mixed.KEWit
import RischTragerBronstein.Mixed.PrdeWit

/-!
# The square-root logarithmic columns, explicitly

`logCol_theta_logs`: the column `logCol Â W₀ W₁ z` (the coefficient of `θ̂` in `(W₀ + W₁ θ̂)′/(W₀ + W₁ θ̂)`,
times `z`) times `θ`, in any extension containing `Y` with `Y² = Â` and `z θ = ρ Y`, is
`ρ ((W₀ + W₁ Y)′/(W₀ + W₁ Y) − ½ N′/N)`, `N = W₀² − W₁² Â` (when `N ≠ 0`; the column is `0` when
`N = 0`).
-/

open Polynomial CPoly Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The column vanishes when the norm does. -/
lemma logCol_zero_of_norm (m : ℕ) (h : T.Tr (m + 1)) (Ahat W0 W1 : GPoly (LC m)) (z : LC m)
    (hN : T.evP m W0 ^ 2 - T.evP m W1 ^ 2 * T.evP m Ahat = 0) :
    T.ev (m + 1) (logCol Fc ks m Ahat W0 W1 z) = 0 := by
  rw [T.ev_logCol m h]
  have : T.evP m W0 * T.evP m W0 - T.evP m W1 * T.evP m W1 * T.evP m Ahat = 0 := by
    linear_combination hN
  rw [this, inv_zero, mul_zero, zero_mul]

/-- **The column times `θ` as logarithmic derivatives.** -/
theorem logCol_theta_logs (m : ℕ) (h : T.Tr (m + 1)) (Ahat W0 W1 : GPoly (LC m)) (z : LC m)
    (θ : L) (hN : T.evP m W0 ^ 2 - T.evP m W1 ^ 2 * T.evP m Ahat ≠ 0)
    (E : Type*) [Field E] [CharZero E] [Differential E] [Algebra L E] [DifferentialAlgebra L E]
    (Y ρ : E) (hY2 : Y ^ 2 = algebraMap L E (T.evP m Ahat)) (hY0 : Y ≠ 0)
    (hρ : algebraMap L E (T.ev m z * θ) = ρ * Y) :
    algebraMap L E (T.ev (m + 1) (logCol Fc ks m Ahat W0 W1 z) * θ) =
      ρ * (logDeriv (algebraMap L E (T.evP m W0) + algebraMap L E (T.evP m W1) * Y) -
        (1 / 2 : E) * logDeriv (algebraMap L E (T.evP m W0 ^ 2 - T.evP m W1 ^ 2 *
          T.evP m Ahat))) := by
  set ψ := algebraMap L E with hψ
  have hψd : ∀ w : L, (ψ w)′ = ψ w′ := fun w ↦ deriv_algebraMap w
  set Pv := T.evP m Ahat
  set W0v := T.evP m W0
  set W1v := T.evP m W1
  have hNm : ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv ≠ 0 := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub]
    exact (map_ne_zero ψ).mpr hN
  have hcolY := colY_logDeriv Y (ψ W0v) (ψ W1v) (ψ Pv) hY2 hY0 hNm
  have hψN : ψ (W0v ^ 2 - W1v ^ 2 * Pv) = ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv := by
    simp only [map_sub, map_mul, map_pow]
  rw [hψN, ← hcolY, T.ev_logCol m h]
  have e1 : ψ ((1 / 2 : L)) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have e2 : ψ (Pv′ * Pv⁻¹) = (ψ Pv)′ * (ψ Pv)⁻¹ := by rw [RingHom.map_mul, map_inv₀, hψd]
  have hz : ψ ((W0v * (W1v′ + W1v * ((1 / 2 : L) * (Pv′ * Pv⁻¹))) - W0v′ * W1v) *
      (W0v * W0v - W1v * W1v * Pv)⁻¹ * T.ev m z * θ) =
      ψ ((W0v * (W1v′ + W1v * ((1 / 2 : L) * (Pv′ * Pv⁻¹))) - W0v′ * W1v) *
        (W0v * W0v - W1v * W1v * Pv)⁻¹) * ψ (T.ev m z * θ) := by
    rw [← RingHom.map_mul]; ring_nf
  rw [hz, hρ]
  simp only [RingHom.map_mul, RingHom.map_sub, RingHom.map_add, map_inv₀, e1, e2, hψd]
  rw [show ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv = ψ W0v * ψ W0v - ψ W1v * ψ W1v * ψ Pv by ring]
  field_simp

end MTower

end Curves.MT
