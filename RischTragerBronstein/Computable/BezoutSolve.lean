import RischTragerBronstein.Computable.SquarefreePart
import RischTragerBronstein.Computable.LogCritDecide

/-!
# Correctness of the executable Bézout solver

`solveBezout_spec`: if `a` and `b` are coprime and `b ≠ 0`, then `solveBezout a b c = (s, t)`
satisfies `s * a + t * b = c`.

The solver is the inner step of Mack's Hermite reduction (`B (-D* D⁻′ / D⁻) + C D⁻* = A`). Its
correctness uses the full specification of the executable Euclid: the gcd of coprime inputs is a
nonzero constant `γ`, the cofactor `σ` satisfies `σ a ≡ γ (mod b)`, and the final division by `b` is
exact.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

theorem solveBezout_spec (a b c : CPoly R) (hb : toPoly b ≠ 0)
    (hcop : IsCoprime (toPoly a) (toPoly b)) :
    toPoly (solveBezout a b c).1 * toPoly a + toPoly (solveBezout a b c).2 * toPoly b =
      toPoly c := by
  -- the gcd is a nonzero constant
  have hbez := egcd_spec a b
  obtain ⟨hga, hgb⟩ := egcd_dvd a b
  set g := (egcd a b).1 with hg
  set σ := (egcd a b).2.1 with hσ
  set τ := (egcd a b).2.2 with hτ
  have hunit : IsUnit (toPoly g) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact isUnit_of_dvd_one (huv ▸ dvd_add (Dvd.dvd.mul_left hga u) (Dvd.dvd.mul_left hgb v))
  obtain ⟨γ, hγ, hgγ⟩ := Polynomial.isUnit_iff.mp hunit
  have hγ0 : γ ≠ 0 := hγ.ne_zero
  have hlead : lead (trim g) = γ := by
    rw [← leadingCoeff_toPoly (by rw [← hgγ]; exact C_ne_zero.mpr hγ0), ← hgγ, leadingCoeff_C]
  -- unfold the solver
  have hsol : solveBezout a b c =
      ((divMod (smul (1 / γ) (mul c σ)) b).2,
        div (sub c (mul (divMod (smul (1 / γ) (mul c σ)) b).2 a)) b) := by
    simp only [solveBezout, ← hg, ← hσ, hlead]
  rw [hsol]
  set S0 := smul (1 / γ) (mul c σ) with hS0
  have hdm := divMod_spec S0 b
  set q := (divMod S0 b).1
  set s := (divMod S0 b).2
  have hS0p : toPoly S0 = C (1 / γ) * (toPoly c * toPoly σ) := by simp [hS0]
  have hCγ : C (1 / γ) * C γ = (1 : R[X]) := by
    rw [← C_mul, one_div, inv_mul_cancel₀ hγ0, C_1]
  -- `b ∣ c - s a`
  have hdvd : toPoly b ∣ toPoly (sub c (mul s a)) := by
    refine ⟨C (1 / γ) * toPoly c * toPoly τ + toPoly q * toPoly a, ?_⟩
    have hs : toPoly s = toPoly S0 - toPoly q * toPoly b := by rw [hdm]; ring
    rw [toPoly_sub, toPoly_mul, hs, hS0p]
    linear_combination (-(C (1 / γ) * toPoly c)) * hbez - (toPoly c) * hCγ +
      (C (1 / γ) * toPoly c) * hgγ
  have hexact := div_mul_of_dvd (sub c (mul s a)) b hb hdvd
  rw [toPoly_sub, toPoly_mul] at hexact
  linear_combination -hexact

end CPoly
