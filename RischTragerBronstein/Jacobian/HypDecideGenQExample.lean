import RischTragerBronstein.Jacobian.HypDecideGenQ
import RischTragerBronstein.Jacobian.HypDecideGen

/-!
# Running the genus-`g` decision procedure

`hypDecideGenQ f g A D` decides `∫ A dx / (D √f)`; every answer is correct by
`hypDecideGenQ_spec`. (The procedure searches good primes and orders with `Nat.find`, so it is run
with `#eval`; kernel-checked proofs of individual answers use the certificate checkers, e.g.
`Jac.Genus2Example.genus2_not_elementary` and `Jac.not_elementary_of_check`.)
-/

open Jac

-- `∫ dx / (x √(x⁵ + 1))` is elementary (`(0, 1)` has order `5` in the Jacobian).
#eval hypDecideGenQ [1, 0, 0, 0, 0, 1] 2 [1] [0, 1]  -- some true

-- `∫ dx / (x √(x⁵ − 2x² − 3x + 1))` is not elementary (`[P] − [σP]` is not torsion).
#eval hypDecideGenQ [1, -3, -2, 0, 0, 1] 2 [1] [0, 1]  -- some false

-- The same with `hypDecideGen` (a decision procedure on its class: `hypDecideGen_decides`).
#eval hypDecideGen [1, 0, 0, 0, 0, 1] 2 [1] [0, 1]  -- some true
#eval hypDecideGen [1, -3, -2, 0, 0, 1] 2 [1] [0, 1]  -- some false
-- A pole at the rational point `(9/4, 205/32)` of `y² = x⁵ − 2x² − 2x − 2`:
-- `∫ dx / ((4x − 9) √(x⁵ − 2x² − 2x − 2))` is not elementary.
#eval hypDecideGen [-2, -2, -2, 0, 0, 1] 2 [1] [-9, 4]  -- some false
