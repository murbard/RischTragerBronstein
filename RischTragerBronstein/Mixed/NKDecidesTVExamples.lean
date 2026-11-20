import RischTragerBronstein.Mixed.NKLogTExamples
import RischTragerBronstein.Mixed.NKSearchTV

/-!
# Example: a non-constant curve over a logarithm

Tower `x`, `t = log x`, and `θ³ + θ = x t` — a curve whose coefficients involve `x`, i.e. are not
constant over `ℚ(t)` (single place at infinity: `deg a₀ = 1`, `gcd(3, 1) = 1`). The limit of the
derivation matrix at infinity is the non-zero diagonal `(0, 1/(3x), 2/(3x))` (`θ ∼ (x t)^{1/3}`),
outside the reach of `exactTR`. The candidate from the shape (`nkCandV`, diagonal `nkDg`, checked)
gives, by `nk_decidesTVP`: `∫ θ′ = θ`, and the exact part of `∫ θ dx` does not exist — since
`τ(θ) = 0`, **`∫ θ dx` is not elementary** for `θ³ + θ = x log x`.
-/

namespace Curves.MT.NKDecidesTVEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx

def mx : GPoly (GFrac ℚ) := [([0, -1], [1])]
/-- `a₀ = −x t`, `a₁ = 1`, `a₂ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], mx], [one0], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def m2 : LC 1 := (([[([-2], [1])]] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- Power sums: `s₀ = 3`, `s₁ = 0`, `s₂ = −2`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, zer, m2]

#guard nkShape Fc ks 0 Pp
#guard traceC Fc ks 0 PC sC

def flθ : List (LC 1) := nkFl Fc ks 0 [[], [one0], []]
def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []

-- `∫ θ dx` is not elementary (about 40 s).
#guard searchTVP Fc ks 0 ic (prdeC Fc ks lv 0) PC (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC))
  [nkCandV Fc ks 0 Pp] = some false
-- `∫ θ′ = θ` (about 40 s).
#guard searchTVP Fc ks 0 ic (prdeC Fc ks lv 0) PC ((List.range 3).map fun j ↦ dθ'.getD j O1.zero)
  [nkCandV Fc ks 0 Pp] = some true

end Curves.MT.NKDecidesTVEx
