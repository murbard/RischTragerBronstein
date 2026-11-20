import RischTragerBronstein.Mixed.FrontRoot

/-!
# Examples: `n`-th roots over a logarithm from expressions

Over the line `y = x`, `frontRootLog n a [e₀, e₁, …] N` decides `∫ ∑ eⱼ θʲ`, `θⁿ = a` (each
answer correct by `frontRootLog_sound`).
-/

namespace Curves.MT.FrontRootEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]

-- `∫ (log x)^{1/3}/x = (3/4) (log x)^{4/3}`.
#guard frontRootLog Fl 3 (log x) [cst 0, inv x] 3 = some true
-- `∫ (log x)^{1/3}` is not elementary.
#guard frontRootLog Fl 3 (log x) [cst 0, cst 1] 3 = some false
-- `∫ (1/x + (log x)^{2/3}/x) = log x + (3/5) (log x)^{5/3}`.
#guard frontRootLog Fl 3 (log x) [inv x, cst 0, inv x] 3 = some true

end Curves.MT.FrontRootEx
