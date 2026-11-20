import RischTragerBronstein.Mixed.NKLogDecide
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Examples: the full decision over a non-Kummer extension of a logarithm

Tower `x`, `t = log x`, `θ³ − θ − t = 0` (single place at infinity: `deg a₀ = 1`, `gcd(3, 1) = 1`).
The trace values are `s = (3, 0, 2)` (power sums of the roots), checked by `traceC`.

By `nk_decides`/`nk_iff`, `∫ θ` is **not elementary**: `exactC` answers `some false` on
`θ − τ(θ)/3 = θ` (`τ(θ) = s₁ = 0`), so the right side `res = true ∧ …` fails whatever `elM` says.
And `∫ 1` is elementary: `f − τ(f)/3 = 0` is exact and `τ(f)/3 = 1` is elementary.
-/

namespace Curves.MT.NKLogEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx

def mone0 : GPoly (GFrac ℚ) := [([-1], [1])]
/-- `a₀ = −t`, `a₁ = −1`, `a₂ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], mone0], [mone0], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, zer, (MOr Fc ks 1).natCast 2]

#guard nkShape Fc ks 0 Pp
#guard traceC Fc ks 0 PC sC

/-- `f = θ`. -/
def flθ : List (LC 1) := nkFl Fc ks 0 [[], [one0], []]
-- `∫ θ` is not elementary (about 20 s).
#guard exactC Fc ks 0 ic lim0 PC (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC)) = some false

/-- `f = 1`. -/
def fl1 : List (LC 1) := nkFl Fc ks 0 [[one0], [], []]
-- the exact part of `∫ 1` (about 20 s)
#guard exactC Fc ks 0 ic lim0 PC (nkRest Fc ks 0 fl1 (nkTau Fc ks 0 3 fl1 sC)) = some true

end Curves.MT.NKLogEx
