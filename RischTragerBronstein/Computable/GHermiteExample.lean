import RischTragerBronstein.Computable.GHermite
import RischTragerBronstein.Computable.TowerExample

/-!
# Hermite reduction in `ℚ(x)(log x)`

`∫ dx / (x log² x) = -1 / log x`: Hermite reduction of `(1/x) / t²` in `ℚ(x)(t)`, `t′ = 1/x`, removes
the double pole completely. The certificate is checked by evaluation; by `hermiteCheck_sound` a
passing certificate is a theorem about `RatFunc (RatFunc ℚ)`.
-/

namespace Tower

/-- `t²` as a polynomial in `t` over `ℚ(x)`. -/
def tSq : GPoly (GFrac ℚ) := [ops₁.zero, ops₁.zero, ops₁.one]

/-- numerator `1 / x`. -/
def numInvX : GPoly (GFrac ℚ) := [invX]

/-- numerator `1`. -/
def numOne : GPoly (GFrac ℚ) := [ops₁.one]

end Tower

open Tower in
-- ∫ (1/x) / t²: certificate passes, and the remaining integrand is zero (so the integral is rational in t)
#eval GPoly.hermiteCheck ops₁ [invX] numInvX tSq (GPoly.hermite ops₁ [invX] numInvX tSq)
open Tower in
#eval GPoly.isZero ops₁ (GPoly.hermite ops₁ [invX] numInvX tSq).b
open Tower in
-- ∫ 1 / t²: certificate passes, but a simple-pole remainder is left (∫ dx / log² x = -x / log x + li x)
#eval GPoly.hermiteCheck ops₁ [invX] numOne tSq (GPoly.hermite ops₁ [invX] numOne tSq)
open Tower in
#eval GPoly.isZero ops₁ (GPoly.hermite ops₁ [invX] numOne tSq).b
