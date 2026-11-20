import RischTragerBronstein.Mixed.NKRam0Cand
import RischTragerBronstein.Mixed.NKSplit0Examples

/-!
# A ramified place at infinity and two places above `t = 0`: `√(x eˣ + 1)`

`θ² = x eˣ + 1` (`t = eˣ`): a single ramified place at infinity (slope `1/2`, residual polynomial
`Z² − x`, `ramShapeC`) and two places above `t = 0` (`θ = ±1`, `split0C`) — not covered by
`nk_decidesETInfVR` (which needs a single place above `0`). Eisenstein at `q = t + 1/x`
(`a₀ = −x q`). `ram0Cands` finds the S-unit (`(θ − 1)²/(−x t)`, divisor `2 P0₊ − 2 P∞`), its
logarithmic derivative, the Wronskian certificate and the gauges; `searchET0RP … 0 = some false`:
**`∫ √(x eˣ + 1) dx` is not elementary** (`nk_decidesETInf0RP`, `τ(θ) = 0`), while `∫ θ′` is found.
-/

namespace Curves.MT.NKSplit0Ex

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEE
open Curves.MT.NKInfRVExpEx

/-- `θ² = x t + 1`. -/
def PR : List (GPoly (LC 0)) := [[cq (-1), mx], []]
def qR : GPoly (LC 0) := [qxi 1 1, one0]
def csR : List (GPoly (LC 0)) := [[mx], []]

#guard eisCk Fc ks 0 PR qR csR [] [qxi (-1) 1] [] [one0]
#guard ramShapeC Fc ks 0 PR 2 1 [px]
#guard split0C Fc ks 0 PR [cq 1, cq (-1)]

def PCR : GPoly (LC 1) := nkPC Fc ks 0 PR
def dθR : GPoly (LC 1) := (dThetaC O1 PCR).getD []
def wθR : GPoly (LC 1) := (invModC O1 PCR (GPoly.derivX O1 PCR)).getD []
def sR0 : List (LC 1) := traceCodes Fc ks 0 PCR

#guard traceW Fc ks 0 PR dθR wθR sR0

def candsR : List (CandET0R 0) :=
  ram0Cands Fc ks 0 2 1 6 3 2 PR [px] [cq 1, cq (-1)] ((MO Fc ks 0).deriv xc)
def restR : List (LC 1) :=
  nkRest Fc ks 0 (nkFl Fc ks 0 fθ2) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ2) sR0)

-- `τ(θ) = 0` and no exact part: **`∫ √(x eˣ + 1) dx` is not elementary**
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ2) sR0)
#guard searchET0RP Fc ks 0 xc (prdeC Fc ks lv 0) PR 2 dθR wθR sR0 restR candsR 0 = some false

/-- `θ′` in the basis `1, θ` (control). -/
def dθR2 : List (LC 1) := (List.range 2).map fun j ↦ dθR.getD j (MOr Fc ks 1).zero

#guard searchET0RP Fc ks 0 xc (prdeC Fc ks lv 0) PR 2 dθR wθR sR0 dθR2 candsR 0 = some true

end Curves.MT.NKSplit0Ex
