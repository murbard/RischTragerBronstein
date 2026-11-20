import RischTragerBronstein.Mixed.NKExpDecide
import RischTragerBronstein.Mixed.NKExactExamples
import RischTragerBronstein.Mixed.NKExactT2

/-!
# Example: the logarithmic part over an exponential level

Tower `x`, `t = eˣ`, and `θ³ = t + t²` (one place above `t = ∞`: `deg a₀ = 2`, `gcd(3, 2) = 1`;
one place above `t = 0`: `ord₀ a₀ = 1`; genus `1`). The trace values are `s = (3, 0, 0)`. By
`nk_iffE`, `∫ θ dx = ∫ (eˣ + e²ˣ)^{1/3} dx` is elementary iff `θ − τ(θ)/3 = θ` is exact and
`τ(θ)/3 = 0` has an elementary integral; `exactG` (exponential solver) answers `some false`:
**`∫ (eˣ + e²ˣ)^{1/3} dx` is not elementary**. The exact part of `θ′` is found (`some true`).

A non-Kummer curve: `θ³ + tθ = t + t²` (`θ ~ t^{2/3}` at infinity, `θ ~ t^{1/3}` at `0`). In the
power basis the system degree bound at infinity fails; in the basis `(1, θ²/t, θ)`, normal at
infinity, the limits are rational and triangular (at `0` after a permutation, `zeroOK`), and
`exactT` decides: by `nk_iffET`, **`∫ θ dx` is not elementary** (`τ(θ) = 0`).
-/

namespace Curves.MT.NKExpEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEE

def mone0 : GPoly (GFrac ℚ) := [([-1], [1])]
/-- `a₀ = −t − t²`, `a₁ = a₂ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], mone0, mone0], [], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, zer, zer]

#guard certC Fc ks lv 1
#guard nkShape Fc ks 0 Pp
#guard nkShape0 Fc ks 0 Pp
#guard traceC Fc ks 0 PC sC

/-- `f = θ`. -/
def flθ : List (LC 1) := nkFl Fc ks 0 [[], [one0], []]
-- `∫ (eˣ + e²ˣ)^{1/3} dx` is not elementary.
#guard exactG Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC
  (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC)) = some false

def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []
-- `∫ θ′ = θ`.
#guard exactG Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC
  ((List.range 3).map fun j ↦ dθ'.getD j O1.zero) = some true

/-- `θ³ + tθ − t − t²`. -/
def Pp2 : List (GPoly (LC 0)) := [[[], mone0, mone0], [[], one0], []]
def PC2 : GPoly (LC 1) := nkPC Fc ks 0 Pp2
def m2t : LC 1 := (([[], [([-2], [1])]] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def sC2 : List (LC 1) := [(MOr Fc ks 1).natCast 3, zer, m2t]
/-- The basis `(1, θ²/t, θ)` and its inverse. -/
def Tc2 : List (List (LC 1)) := [[onec, zer, zer], [zer, zer, O1.inv tC], [zer, onec, zer]]
def Ti2 : List (List (LC 1)) := [[onec, zer, zer], [zer, zer, onec], [zer, tC, zer]]

#guard nkShape Fc ks 0 Pp2
#guard nkShape0 Fc ks 0 Pp2
#guard traceC Fc ks 0 PC2 sC2
-- `∫ θ dx` is not elementary on `θ³ + eˣ θ = eˣ + e²ˣ`.
#guard exactT Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC2 Tc2 Ti2
  (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC2)) = some false

def dθ2 : GPoly (LC 1) := (dThetaC O1 PC2).getD []
-- `∫ θ′ = θ`.
#guard exactT Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC2 Tc2 Ti2
  ((List.range 3).map fun j ↦ dθ2.getD j O1.zero) = some true

-- The basis normal at infinity computed automatically (`nkTc`, `nkTi`) gives the same answers.
#guard exactT Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC2 (nkTc Fc ks 0 Pp2) (nkTi Fc ks 0 Pp2)
  (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC2)) = some false

end Curves.MT.NKExpEx
