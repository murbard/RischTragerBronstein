import RischTragerBronstein.Computable.EuclidDegree
import RischTragerBronstein.Computable.Hermite
import RischTragerBronstein.Rational.SquarefreePart

/-!
# Exact division and the executable squarefree part

* `divMod_exact`: if `d ∣ p` (and `d ≠ 0`) then the remainder of `divMod p d` is zero, so
  `p = div p d * d`.
* `squarefree_sqfreePart`: the executable `D / gcd (D, D′)` denotes a squarefree polynomial and
  divides `D` exactly (`sqfreePart_mul`).

These are two of the facts needed to show that the executable Hermite reduction always succeeds
(its final denominator is `D* = D / gcd (D, D′)`), and the first step of squarefree factorisation.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

theorem divMod_exact (p d : CPoly R) (hd : toPoly d ≠ 0) (hdvd : toPoly d ∣ toPoly p) :
    toPoly (divMod p d).2 = 0 := by
  have hspec := divMod_spec p d
  have hrem : toPoly d ∣ toPoly (divMod p d).2 := by
    have : toPoly (divMod p d).2 = toPoly p - toPoly (divMod p d).1 * toPoly d := by
      rw [hspec]; ring
    rw [this]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  exact eq_zero_of_dvd_of_degree_lt hrem (divMod_degree_lt p d hd)

theorem div_mul_of_dvd (p d : CPoly R) (hd : toPoly d ≠ 0) (hdvd : toPoly d ∣ toPoly p) :
    toPoly p = toPoly (div p d) * toPoly d := by
  have := divMod_spec p d
  rwa [divMod_exact p d hd hdvd, add_zero] at this

/-- The executable squarefree part `D / gcd (D, D′)`. -/
def sqfreePart (D : CPoly R) : CPoly R := div D (gcd D (deriv D))

lemma toPoly_gcd (p q : CPoly R) : toPoly (gcd p q) = toPoly (egcd p q).1 := toPoly_trim _

theorem sqfreePart_mul (D : CPoly R) (hD : toPoly D ≠ 0) :
    toPoly D = toPoly (sqfreePart D) * toPoly (gcd D (deriv D)) := by
  have hdvd : toPoly (gcd D (deriv D)) ∣ toPoly D := by
    rw [toPoly_gcd]; exact (egcd_dvd D (deriv D)).1
  exact div_mul_of_dvd D _ (fun h0 ↦ hD (by simpa [h0] using hdvd)) hdvd

/-- **The executable squarefree part is squarefree.** -/
theorem squarefree_sqfreePart (D : CPoly R) (hD : toPoly D ≠ 0) :
    Squarefree (toPoly (sqfreePart D)) := by
  refine Differential.squarefree_of_gcd_derivative (G := toPoly (gcd D (deriv D))) hD
    (by rw [sqfreePart_mul D hD]; ring) ?_ ?_
  · rw [toPoly_gcd, ← toPoly_deriv]; exact (egcd_dvd D (deriv D)).2
  · intro h h1 h2
    rw [toPoly_gcd]
    exact dvd_egcd D (deriv D) h1 (by rwa [toPoly_deriv])

end CPoly

-- squarefree part of x²(x + 1)³ is ~ x(x + 1)
#eval CPoly.trim (CPoly.sqfreePart ([0, 0, 1, 3, 3, 1] : CPoly ℚ))
