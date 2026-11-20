import RischTragerBronstein.Mixed.NKInfRVExp
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: a non-constant curve over `eˣ` with two places at infinity

Tower `x`, `t = eˣ`, and `θ² = t² + x t` (coefficients involving `x`): two places at infinity
(`θ ≈ ±t`), a single ramified place above `t = 0`. Eisenstein at a root of `q = t² + x t`
(Bézout `−(4/x²) q + (2t/x² + 1/x) q′ = 1`). The unit `u₀ = −4 (θ + t + x/2)²/x²` (norm `1`) has
`u₀′/u₀ = 2 (x − 1) θ / (x (t + x))`. By `nk_iffETInfV`: `∫ θ dx` is elementary iff `θ − c u₀′/u₀`
is exact for a constant `c` (`exactTLEV`: basis `1, θ`, shifts `0, 1`, trivial gauge at `0`
with diagonal `0, (1 + x)/(2x)`), since `τ(θ) = 0`.
-/

namespace Curves.MT.NKInfRVExpEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEE

def px : GPoly (GFrac ℚ) := [([0, 1], [1])]
def mx : GPoly (GFrac ℚ) := [([0, -1], [1])]
def cq (q : ℚ) : GPoly (GFrac ℚ) := [([q], [1])]
def cqx (q : ℚ) : GPoly (GFrac ℚ) := [([q], [0, 1])]
def cqx2 (q : ℚ) : GPoly (GFrac ℚ) := [([q], [0, 0, 1])]
/-- `a₀ = −(t² + x t)`, `a₁ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], mx, cq (-1)], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def qE : GPoly (LC 0) := [[], px, one0]
def csE : List (GPoly (LC 0)) := [[cq (-1)], []]
def sE : GPoly (LC 0) := []
def tE : GPoly (LC 0) := [cq (-1)]
def s2E : GPoly (LC 0) := [cqx2 (-4)]
def t2E : GPoly (LC 0) := [cqx 1, cqx2 2]

#guard eisCk Fc ks 0 Pp qE csE sE tE s2E t2E
#guard nkShape0 Fc ks 0 Pp

def Us : List (List (GPoly (LC 0))) := [[[cq (-1), cqx (-8), cqx2 (-8)], [cqx (-4), cqx2 (-8)]]]
def Vs : List (List (GPoly (LC 0))) := [[[cq (-1), cqx (-8), cqx2 (-8)], [cqx 4, cqx2 8]]]
def den : GPoly (LC 0) := [[([0, 0, 1], [1])], [([0, 1], [1])]]
/-- `g₀ = 2 (x − 1) θ / (x (t + x))`. -/
def gls : List (GPoly (LC 1)) := [[zer, ([[([-2, 2], [1])]], den)]]
/-- `θ′ = (2t + 1 + x) θ / (2 (t + x))`, `1/(2θ) = θ/(2 (t² + x t))`. -/
def dθW : GPoly (LC 1) :=
  [zer, ([[([1, 1], [1])], cq 2], [[([0, 2], [1])], cq 2])]
def wθW : GPoly (LC 1) := [zer, ([one0], [[], [([0, 2], [1])], cq 2])]
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]
def J : List ℕ := [1]
def H : List (List (LC 1)) := [[(den, [[([-2, 2], [1])]])]]

#guard unitsC Fc ks 0 Pp Us Vs gls dθW wθW sC
#guard indepC Fc ks 0 gls J H
#guard traceW Fc ks 0 Pp dθW wθW sC

def Tc : List (List (LC 1)) := [[onec, zer], [zer, onec]]
def Cg : List (List (LC 0)) := [[one0, []], [[], one0]]
def dg : List (ℚ × ℚ × LC 0) := [(0, 0, one0), (0, 0, one0)]
def dg0 : List (ℚ × ℚ × LC 0) := [(0, 0, mx), (1/2, 1/2, mx)]
def r : ℕ → ℤ := fun i ↦ if i = 1 then 1 else 0
def fθ : List (GPoly (LC 0)) := [[], [one0]]
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)
def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []

-- `τ(θ) = 0` and no exact part: **`∫ √(e²ˣ + x eˣ) dx` is not elementary**
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)
#guard exactTLEV Fc ks 0 xc (prdeC Fc ks lv 0) dg r Cg Cg dg0 PC Tc Tc restθ gls = some false
-- `∫ θ′` and `∫ u₀′/u₀`
#guard exactTLEV Fc ks 0 xc (prdeC Fc ks lv 0) dg r Cg Cg dg0 PC Tc Tc
  ((List.range 2).map fun j ↦ dθ'.getD j O1.zero) gls = some true
#guard exactTLEV Fc ks 0 xc (prdeC Fc ks lv 0) dg r Cg Cg dg0 PC Tc Tc
  ((List.range 2).map fun j ↦ (gls.getD 0 []).getD j O1.zero) gls = some true

end Curves.MT.NKInfRVExpEx
