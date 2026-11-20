import RischTragerBronstein.Mixed.NKDecidesTEV
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: a non-constant curve over an exponential

Tower `x`, `t = eˣ`, and `θ² = x t` — coefficients involving `x`, not constant over `ℚ(t)`; a single
place at infinity (`deg a₀ = 1`) and a single place above `t = 0` (`ord₀ a₀ = 1`). The limit of the
rescaled derivation matrix at infinity is the diagonal `(0, −1/2 + 1/(2x))` and its value at `t = 0`
is the diagonal `(0, 1/2 + 1/(2x))` — outside the reach of the constant-curve solvers. A candidate
for `exactTEV` (basis `1, θ`, shifts `0, 1`, trivial gauge at `0`, diagonal data `(p, q, −x)`, the
data that `exactTEV_exists` produces for this curve) answers `some false` for the exact part of
`∫ θ dx` and `some true` for `∫ θ′`. Since `τ(θ) = 0`, `nk_iffTEV` turns the first answer into:
**`∫ √(x eˣ) dx` is not elementary**; `nk_decidesTEV` says the search `searchTEV` always reaches
such an answer.
-/

namespace Curves.MT.NKDecidesTEVEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEE

def mx : GPoly (GFrac ℚ) := [([0, -1], [1])]
def zero0 : GPoly (GFrac ℚ) := []
/-- `a₀ = −x t`, `a₁ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], mx], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
/-- Power sums: `s₀ = 2`, `s₁ = 0`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]

#guard nkShape Fc ks 0 Pp
#guard nkShape0 Fc ks 0 Pp
#guard traceC Fc ks 0 PC sC

def flθ : List (LC 1) := nkFl Fc ks 0 [[], [one0]]
def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []
def Tc : List (List (LC 1)) := [[onec, zer], [zer, onec]]
def Cg : List (List (LC 0)) := [[one0, zero0], [zero0, one0]]
def dg : List (ℚ × ℚ × LC 0) := [(0, 0, mx), (-1/2, 1/2, mx)]
def dg0 : List (ℚ × ℚ × LC 0) := [(0, 0, mx), (1/2, 1/2, mx)]
def r : ℕ → ℤ := fun i ↦ if i = 1 then 1 else 0

-- `τ(θ) = 0`
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 flθ sC)
-- `∫ θ dx` is not elementary
#guard exactTEV Fc ks 0 xc (prdeC Fc ks lv 0) dg r Cg Cg dg0 PC Tc Tc
  (nkRest Fc ks 0 flθ (nkTau Fc ks 0 2 flθ sC)) = some false
-- `∫ θ′ = θ`
#guard exactTEV Fc ks 0 xc (prdeC Fc ks lv 0) dg r Cg Cg dg0 PC Tc Tc
  ((List.range 2).map fun j ↦ dθ'.getD j O1.zero) = some true

end Curves.MT.NKDecidesTEVEx
