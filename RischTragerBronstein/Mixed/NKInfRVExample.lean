import RischTragerBronstein.Mixed.NKInfRV
import RischTragerBronstein.Mixed.NKDecidesInfVG
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: a non-constant curve with two places at infinity

Tower `x`, `t = log x`, and `θ² = t² + x` — coefficients involving `x` (Risch's mixed case), two
places at infinity (`θ ≈ ±t`). Geometric irreducibility: Eisenstein at a root of `q = t² + x`
(`eisCk`, Bézout identities `0·q − 1·(−1) = 1`, `q/x − (t/(2x)) q′ = 1`). The unit
`u₀ = −(θ + t)²/x` (norm `1`, inverse `−(θ − t)²/x`) has `u₀′/u₀ = (2 − t) θ/(x (t² + x))`,
trace `0`, and is independent (`indepC`). By `nk_iffInfV`, `∫ f` is elementary iff
`f − τ(f)/2 − c u₀′/u₀` is exact for a constant `c` (`exactTLV` in the basis `1, θ` rescaled by
`t^{-1}` on `θ`, limit matrix `0`) and `∫ τ(f)/2` is elementary.
-/

namespace Curves.MT.NKInfRVEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx

def px : GPoly (GFrac ℚ) := [([0, 1], [1])]
def mx : GPoly (GFrac ℚ) := [([0, -1], [1])]
def cq (q : ℚ) : GPoly (GFrac ℚ) := [([q], [1])]
def cqx (q : ℚ) : GPoly (GFrac ℚ) := [([q], [0, 1])]
/-- `a₀ = −(t² + x)`, `a₁ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[mx, [], cq (-1)], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
/-- Eisenstein data: `q = t² + x`, `a₀ = q · (−1)`, `a₁ = q · 0`. -/
def qE : GPoly (LC 0) := [px, [], one0]
def csE : List (GPoly (LC 0)) := [[cq (-1)], []]
def sE : GPoly (LC 0) := []
def tE : GPoly (LC 0) := [cq (-1)]
def s2E : GPoly (LC 0) := [cqx 1]
def t2E : GPoly (LC 0) := [[], cqx (-1/2)]

#guard eisCk Fc ks 0 Pp qE csE sE tE s2E t2E
-- split at infinity: `deg aᵢ ≤ 2 − i`, leading polynomial `Z² − 1 = (Z − 1)(Z + 1)`
-- (so `nk_decidesInfVG` applies: the search finds the basis, the gauge and the units)
#guard splitShapeC Fc ks 0 Pp 1 [cq 1, cq (-1)]

/-- `u₀ = −(2t² + x)/x − (2t/x) θ`, `v₀ = −(2t² + x)/x + (2t/x) θ`. -/
def Us : List (List (GPoly (LC 0))) := [[[cq (-1), [], cqx (-2)], [[], cqx (-2)]]]
def Vs : List (List (GPoly (LC 0))) := [[[cq (-1), [], cqx (-2)], [[], cqx 2]]]
def den : GPoly (LC 0) := [[([0, 0, 1], [1])], [], [([0, 1], [1])]]
/-- `g₀ = (2 − t) θ / (x (t² + x))`. -/
def gls : List (GPoly (LC 1)) := [[zer, ([cq 2, cq (-1)], den)]]
/-- `θ′ = (x + 2t) θ / (2x (t² + x))`, `1/(2θ) = θ/(2 (t² + x))`. -/
def dθW : GPoly (LC 1) := [zer, ([px, cq 2], [[([0, 0, 2], [1])], [], [([0, 2], [1])]])]
def wθW : GPoly (LC 1) := [zer, ([one0], [[([0, 2], [1])], [], [cq 2].head!])]
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]
def J : List ℕ := [1]
def H : List (List (LC 1)) := [[(den, [cq 2, cq (-1)])]]

#guard unitsC Fc ks 0 Pp Us Vs gls dθW wθW sC
#guard indepC Fc ks 0 gls J H
#guard traceW Fc ks 0 Pp dθW wθW sC

def Tc : List (List (LC 1)) := [[onec, zer], [zer, onec]]
def dg : List (FRep (LC 0)) := [⟨[], []⟩, ⟨[], []⟩]
def r : ℕ → ℤ := fun i ↦ if i = 1 then 1 else 0
def fθ : List (GPoly (LC 0)) := [[], [one0]]
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)

-- `τ(θ) = 0` and the exact part of `θ` does not exist: **`∫ √(log² x + x) dx` is not elementary**
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)
#guard exactTLV Fc ks 0 ic (prdeC Fc ks lv 0) dg r PC Tc Tc restθ gls = some false
def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []
-- `∫ θ′`, `∫ u₀′/u₀` and `∫ (θ′ + 3 u₀′/u₀)`: exact parts exist
#guard exactTLV Fc ks 0 ic (prdeC Fc ks lv 0) dg r PC Tc Tc
  ((List.range 2).map fun j ↦ dθ'.getD j O1.zero) gls = some true
#guard exactTLV Fc ks 0 ic (prdeC Fc ks lv 0) dg r PC Tc Tc
  ((List.range 2).map fun j ↦ (gls.getD 0 []).getD j O1.zero) gls = some true
#guard exactTLV Fc ks 0 ic (prdeC Fc ks lv 0) dg r PC Tc Tc
  ((List.range 2).map fun j ↦ O1.add (dθ'.getD j O1.zero)
    (O1.mul (O1.natCast 3) ((gls.getD 0 []).getD j O1.zero))) gls = some true

end Curves.MT.NKInfRVEx
