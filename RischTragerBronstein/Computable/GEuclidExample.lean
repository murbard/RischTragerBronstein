import RischTragerBronstein.Computable.GEuclid
import RischTragerBronstein.Computable.TowerExample

/-!
# Euclidean division of polynomials in `t` with coefficients in `ℚ(x)`
-/

namespace Tower

/-- `t² - x²` as a polynomial in `t` over `ℚ(x)`. -/
def p₁ : GPoly (GFrac ℚ) := [([0, 0, -1], [1]), ops₁.zero, ops₁.one]

/-- `t - x`. -/
def d₁ : GPoly (GFrac ℚ) := [([0, -1], [1]), ops₁.one]

end Tower

open Tower in
-- the remainder of (t² - x²) / (t - x) is zero
#eval GPoly.isZero ops₁ (GPoly.divMod ops₁ p₁ d₁).2
open Tower in
-- the quotient minus (t + x) is zero
#eval GPoly.isZero ops₁ (GPoly.sub ops₁ (GPoly.divMod ops₁ p₁ d₁).1 [([0, 1], [1]), ops₁.one])
open Tower in
-- gcd (t² - x², t - x) is not zero, and (t - x) modulo it is zero
#eval GPoly.isZero ops₁ (GPoly.divMod ops₁ d₁ (GPoly.trim ops₁ (GPoly.egcd ops₁ p₁ d₁).1)).2
