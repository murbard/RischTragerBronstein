import RischTragerBronstein.Computable.CFrac
import RischTragerBronstein.Computable.NormCoeff

/-!
# A computable tower: `ℚ ⊂ ℚ(x) ⊂ ℚ(x)(log x)`

Two applications of the tower step. `Tower.ops₂` are executable operations on codes for elements of
`ℚ(x)(t)`, `t = log x`; the corresponding model is obtained by two applications of
`CField.monomial`, so every computation below is a theorem about the differential field
`RatFunc (RatFunc ℚ)` with `x′ = 1`, `t′ = 1 / x`.
-/

namespace Tower

/-- level 0: `ℚ`. -/
def ops₀ : COps ℚ := COps.ofDecidableField ℚ

/-- level 1: `ℚ(x)`, `x′ = 1`. -/
def ops₁ : COps (GFrac ℚ) := (ops₀.monomial [1]).normalizeBy CPoly.normCoeff

/-- the element `1 / x` of level 1. -/
def invX : GFrac ℚ := ([1], [0, 1])

/-- level 2: `ℚ(x)(t)`, `t′ = 1 / x` (`t = log x`). -/
def ops₂ : COps (GFrac (GFrac ℚ)) := ops₁.monomial [invX]

/-- the element `t` of level 2. -/
def t : GFrac (GFrac ℚ) := ([ops₁.zero, ops₁.one], [ops₁.one])

/-- the element `x` of level 2. -/
def x : GFrac (GFrac ℚ) := ([([0, 1], [1])], [ops₁.one])

end Tower

open Tower in
-- (t²)′ = 2 t / x : numerator `[0, 2/x]` up to unnormalised fractions
#eval (ops₂.deriv (ops₂.mul t t)).1
open Tower in
-- is (x t)′ - (t + 1) zero?  (x log x)′ = log x + 1
#eval ops₂.isZero (ops₂.add (ops₂.deriv (ops₂.mul x t)) (ops₂.neg (ops₂.add t ops₂.one)))
open Tower in
-- is (t²)′ zero?
#eval ops₂.isZero (ops₂.deriv (ops₂.mul t t))
