import RischTragerBronstein.Mixed.NKSplit0Cand
import RischTragerBronstein.Mixed.NKInfRVExpExample

/-!
# Several places above `t = 0`: an example

`θ² = e²ˣ + x eˣ + x²` (`t = eˣ`): two places at infinity (`θ ≈ ±t`, `splitShapeC`) and two
places above `t = 0` (`θ = ±x`, `split0C`) — not covered by the single-place deciders
(`nkShape0` fails). Eisenstein at `q = t² + x t + x²` (Bézout `(4/(3x²)) q − (2t/(3x²) + 1/(3x)) q′ = 1`).
The S-units (`S` = the four places), normalized to norm `1`:

* `u₁ = (θ + t + x/2)²/N`, `N = −3x²/4` (a unit outside infinity), and
* `u₂ = (θ − x − t/2)²/(−3t²/4)` (zeros and poles above `0` and at infinity),

with `x` they span the S-units (genus `0`). `split0Cands` computes the logarithmic derivatives,
the Wronskian certificate and the gauges at infinity and at `0`, and `split0CandsA` also finds the
units (`split0Units`, kernels of order conditions at infinity and along the Hensel branches above
`0`); `searchET0P … 0 = some false`:
**`∫ √(e²ˣ + x eˣ + x²) dx` is not elementary** (`nk_decidesETInf0P`, `τ(θ) = 0`), while `∫ θ′`
is found elementary.
-/

namespace Curves.MT.NKSplit0Ex

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEE
open Curves.MT.NKInfRVExpEx

/-- `c xᵏ` and `c / xᵏ`. -/
def qx (c : ℚ) (k : ℕ) : GPoly (GFrac ℚ) := [(List.replicate k 0 ++ [c], [1])]
def qxi (c : ℚ) (k : ℕ) : GPoly (GFrac ℚ) := [([c], List.replicate k 0 ++ [1])]

/-- `θ² = t² + x t + x²`. -/
def Pq : List (GPoly (LC 0)) := [[qx (-1) 2, mx, cq (-1)], []]
def qQ : GPoly (LC 0) := [qx 1 2, px, one0]
def csQ : List (GPoly (LC 0)) := [[cq (-1)], []]
def s2Q : GPoly (LC 0) := [qxi (4/3) 2]
def t2Q : GPoly (LC 0) := [qxi (-1/3) 1, qxi (-2/3) 2]

#guard eisCk Fc ks 0 Pq qQ csQ [] [cq (-1)] s2Q t2Q
#guard splitShapeC Fc ks 0 Pq 1 [cq 1, cq (-1)]
#guard split0C Fc ks 0 Pq [px, mx]

/-- `U₁ = −(4/(3x²)) (θ + t + x/2)²`, `V₁` its conjugate: `U₁ V₁ = 1`. -/
def U1 : List (GPoly (LC 0)) := [[cq (-5/3), qxi (-8/3) 1, qxi (-8/3) 2], [qxi (-4/3) 1, qxi (-8/3) 2]]
def V1 : List (GPoly (LC 0)) := [[cq (-5/3), qxi (-8/3) 1, qxi (-8/3) 2], [qxi (4/3) 1, qxi (8/3) 2]]
/-- `U₂ = −(4/3) (θ − x − t/2)²`, `V₂` its conjugate: `U₂ V₂ = t⁴`; the unit is `U₂/t²`. -/
def U2 : List (GPoly (LC 0)) := [[qx (-8/3) 2, qx (-8/3) 1, cq (-5/3)], [qx (8/3) 1, cq (4/3)]]
def V2 : List (GPoly (LC 0)) := [[qx (-8/3) 2, qx (-8/3) 1, cq (-5/3)], [qx (-8/3) 1, cq (-4/3)]]

#guard unitDC Fc ks 0 Pq U1 V1 0
#guard unitDC Fc ks 0 Pq U2 V2 4

def PC0 : GPoly (LC 1) := nkPC Fc ks 0 Pq
def dθ0 : GPoly (LC 1) := (dThetaC O1 PC0).getD []
def wθ0 : GPoly (LC 1) := (invModC O1 PC0 (GPoly.derivX O1 PC0)).getD []
def s0 : List (LC 1) := traceCodes Fc ks 0 PC0

#guard traceW Fc ks 0 Pq dθ0 wθ0 s0

def cands : List (CandET0 0) :=
  split0Cands Fc ks 0 1 Pq [cq 1, cq (-1)] [px, mx] ((MO Fc ks 0).deriv xc) [U1, U2] [V1, V2] [0, 4]
    [0, 2]
def gls0 : List (GPoly (LC 1)) := ((cands.headD default).2.2.2).2.2.1

#guard unitsC0 Fc ks 0 Pq [U1, U2] [V1, V2] [0, 4] [0, 2] ((MO Fc ks 0).deriv xc) gls0 dθ0 wθ0 s0
#guard indepWC Fc ks 0 gls0 (cands.headD default).2.2.2.2.2.2.1 (cands.headD default).2.2.1
  (cands.headD default).2.2.2.2.2.2.2.1

def fθ2 : List (GPoly (LC 0)) := [[], [one0]]
def rest2 : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ2) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ2) s0)

-- `τ(θ) = 0` and no exact part: **`∫ √(e²ˣ + x eˣ + x²) dx` is not elementary**
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ2) s0)
#guard searchET0P Fc ks 0 xc (prdeC Fc ks lv 0) Pq dθ0 wθ0 s0 rest2 cands 0 = some false

/-- `θ′` in the basis `1, θ` (control: `∫ θ′` is elementary). -/
def dθ2 : List (LC 1) := (List.range 2).map fun j ↦ dθ0.getD j (MOr Fc ks 1).zero

#guard searchET0P Fc ks 0 xc (prdeC Fc ks lv 0) Pq dθ0 wθ0 s0 dθ2 cands 0 = some true

-- the same with the S-units found automatically (`split0Units`: divisors `P∞₀ − P∞₁`, `P0₀ − P∞₁`)
#guard searchET0P Fc ks 0 xc (prdeC Fc ks lv 0) Pq dθ0 wθ0 s0 rest2
  (split0CandsA Fc ks 0 1 6 3 2 Pq [cq 1, cq (-1)] [px, mx] ((MO Fc ks 0).deriv xc)) 0 = some false

end Curves.MT.NKSplit0Ex
