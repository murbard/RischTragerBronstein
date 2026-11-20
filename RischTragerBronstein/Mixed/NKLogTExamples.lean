import RischTragerBronstein.Mixed.NKLogDecideT
import RischTragerBronstein.Mixed.NKExpDecide
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: a basis normal at infinity over a logarithm

Tower `x`, `t = log x`, and `θ³ + tθ = t²` (single place at infinity: `deg a₀ = 2`,
`gcd(3, 2) = 1`). In the power basis the system solver answers `none`; in the basis normal at
infinity `nkTc` (`(1, θ²/t, θ)`), `exactT` finds `∫ θ′ = θ` and proves that `θ` is not exact.
Since `τ(θ) = 0`, by `nk_iffT` **`∫ θ dx` is not elementary**.
-/

namespace Curves.MT.NKLogTEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx

def mone0 : GPoly (GFrac ℚ) := [([-1], [1])]
/-- `a₀ = −t²`, `a₁ = t`, `a₂ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], [], mone0], [[], one0], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def m2t : LC 1 := (([[], [([-2], [1])]] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- Power sums: `s₀ = 3`, `s₁ = 0`, `s₂ = −2t`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, zer, m2t]

#guard nkShape Fc ks 0 Pp
#guard traceC Fc ks 0 PC sC

def flθ : List (LC 1) := nkFl Fc ks 0 [[], [one0], []]
-- `∫ θ dx` is not elementary.
#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) PC (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp)
  (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC)) = some false

def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []
-- `∫ θ′ = θ` (the power basis gives `none`).
#guard exactT Fc ks 0 (primSysC Fc ks 0 ic lim0) PC (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp)
  ((List.range 3).map fun j ↦ dθ'.getD j O1.zero) = some true
#guard exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) PC
  ((List.range 3).map fun j ↦ dθ'.getD j O1.zero) = none

end Curves.MT.NKLogTEx
