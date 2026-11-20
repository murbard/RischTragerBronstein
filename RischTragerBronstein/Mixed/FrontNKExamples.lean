import RischTragerBronstein.Mixed.FrontNK

/-!
# Examples: a non-Kummer algebraic function over a logarithm, from expressions

Over the line `y = x`, `θ³ + θ − x log x = 0` (single place at infinity). `frontNKLog` decides
(each answer correct by `frontNKLog_sound`): `∫ θ dx` and `∫ θ² dx` are not elementary; `∫ (log x + 1)`
(which is `∫ (θ³ + θ)′`) is.
-/

namespace Curves.MT.FrontNKEx

open Curves Curves.MT Curves.MT.Front EE

def Fl : Sup.BPoly ℚ := [[0, -1], [1]]

-- `∫ θ dx` is not elementary (about 30 s).
#guard frontNKLog Fl [neg (mul x (log x)), cst 1, cst 0] [cst 0, cst 1] 3 = some false
-- `∫ θ² dx` is not elementary.
#guard frontNKLog Fl [neg (mul x (log x)), cst 1, cst 0] [cst 0, cst 0, cst 1] 3 = some false
-- `∫ (log x + 1) dx = x log x`.
#guard frontNKLog Fl [neg (mul x (log x)), cst 1, cst 0] [add (log x) (cst 1)] 3 = some true

end Curves.MT.FrontNKEx
