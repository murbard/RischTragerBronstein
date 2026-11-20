import RischTragerBronstein.Mixed.NKTrace
import RischTragerBronstein.Mixed.NKLogExamples

/-!
# Example: the trace test with non-zero residues and no certificate

Over `θ³ − θ − log x = 0`, `f = θ²/(log x − x)` has poles above `t = x` with non-zero residues.
The trace codes are `(3, 0, 2)` (`traceCodes`, the true power sums), so `Tr(f)/3 = (2/3)/(log x − x)`, and
`elM` answers `false` on it (the residue `x/(1 − x)` of `1/(t − x)` is not constant): by
`nk_trace_decides`, **`∫ θ²/(log x − x) dx` is not elementary** (at every large search bound).
-/

namespace Curves.MT.NKTraceEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogEx

/-- `t − x`. -/
def tmx : GPoly (LC 0) := [(MO Fc ks 0).neg xc, one0]
/-- `f = θ²/(t − x)`. -/
def flT : List (LC 1) := [zer, zer, (([one0] : GPoly (LC 0)), tmx)]

#guard ((traceCodes Fc ks 0 PC).map fun c ↦ ratValC Fc ks 1 c) = [some 3, some 0, some 2]
#guard elM Fc ks lv 1 (nkTau Fc ks 0 3 flT (traceCodes Fc ks 0 PC)) 3 = some false

end Curves.MT.NKTraceEx

/-!
Over an exponential level: `θ³ − θ − eˣ = 0` (single place at infinity), `f = x θ²/(eˣ − 1)`:
`Tr(f)/3 = (2/3) x/(eˣ − 1)`, on which `elM` answers `false`; by `nk_trace_decides` (any level
kind), **`∫ x θ²/(eˣ − 1) dx` is not elementary**.
-/

namespace Curves.MT.NKTraceExE

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEE

def mone0 : GPoly (GFrac ℚ) := [([-1], [1])]
def Pp : List (GPoly (LC 0)) := [[[], mone0], [mone0], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
/-- `eˣ − 1`. -/
def tm1 : GPoly (LC 0) := [mone0, one0]
/-- `f = x θ²/(eˣ − 1)`. -/
def flE : List (LC 1) := [zer, zer, (([xc] : GPoly (LC 0)), tm1)]

#guard nkShape Fc ks 0 Pp
#guard ((traceCodes Fc ks 0 PC).map fun c ↦ ratValC Fc ks 1 c) = [some 3, some 0, some 2]
#guard elM Fc ks lv 1 (nkTau Fc ks 0 3 flE (traceCodes Fc ks 0 PC)) 3 = some false

end Curves.MT.NKTraceExE
