import RischTragerBronstein.Algebraic.HypLogSearch

/-!
# Genus 2: a torsion logarithmic part found automatically

On `y² = x⁵ + 1` (genus 2) the point `(0, 1)` has order `5` in the Jacobian; the search finds
`u = (y − 1 − x⁵/2) / x⁵` (`K = 5`) and the kernel checks the certificate:
`∫ dx / (x √(x⁵ + 1)) = (1/5) log u` is **elementary**. Likewise `∫ dx / (x √(x³ + 1))`
(`(0, 1)` of order `3` on the elliptic curve).
-/

open Polynomial Differential

namespace CPoly.HypLogExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / (x √(x⁵ + 1))` is elementary** (genus 2). -/
theorem ex_genus2_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 5 + 1) : HasElementaryIntegral (1 / (x * y)) := by
  have h := hypLogElem_sound hC x y hx [1, 0, 0, 0, 0, 1]
    (by rw [hy]; simp [toPoly]; ring) [1] [0, 1] 6 (by decide +kernel)
  rwa [show aeval x (toPoly ([1] : CPoly ℚ)) = 1 by simp [toPoly],
    show aeval x (toPoly ([0, 1] : CPoly ℚ)) = x by simp [toPoly]] at h

/-- **`∫ dx / (x √(x³ + 1))` is elementary** (genus 1, found by the same search). -/
theorem ex_genus1_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) : HasElementaryIntegral (1 / (x * y)) := by
  have h := hypLogElem_sound hC x y hx [1, 0, 0, 1]
    (by rw [hy]; simp [toPoly]; ring) [1] [0, 1] 6 (by decide +kernel)
  rwa [show aeval x (toPoly ([1] : CPoly ℚ)) = 1 by simp [toPoly],
    show aeval x (toPoly ([0, 1] : CPoly ℚ)) = x by simp [toPoly]] at h

/-- **Poles over a quintic Galois orbit (genus 2)**: on `y² = x⁵ + x² − 2`, the five poles over
`x⁵ = 2` carry residue `1` and form the divisor of `(y − x)/(y + x)`; the orbit search finds the
certificate: `∫ (3x⁵ + 4) dx / ((x⁵ − 2) √(x⁵ + x² − 2))` is **elementary**. -/
theorem ex_genus2_orbit_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 5 + x ^ 2 - 2) :
    HasElementaryIntegral ((3 * x ^ 5 + 4) / ((x ^ 5 - 2) * y)) := by
  have h := hypLogElemOrb_sound hC x y hx [-2, 0, 1, 0, 0, 1]
    (by rw [hy]; simp [toPoly]; ring) [4, 0, 0, 0, 0, 3] [-2, 0, 0, 0, 0, 1] 3 (by decide +kernel)
  rwa [show aeval x (toPoly ([4, 0, 0, 0, 0, 3] : CPoly ℚ)) = 3 * x ^ 5 + 4 by
      simp [toPoly]; ring,
    show aeval x (toPoly ([-2, 0, 0, 0, 0, 1] : CPoly ℚ)) = x ^ 5 - 2 by simp [toPoly]; ring] at h

end CPoly.HypLogExample
