import RischTragerBronstein.Mixed.NKBC0R
import RischTragerBronstein.Mixed.NKBCExamples

/-!
# A ramified place at infinity and a non-rational fibre above `0`: `√(x eˣ + x)`

`θ² = x eˣ + x`: a single ramified place at infinity (residual polynomial `Z² − x`) and a single
place above `t = 0` with residue field `ℚ(x)(√x)`. Over the base `w² = x` (`Mixed/KBExamples`) the
fibre splits (`θ = ±w`) and `nk_decidesETInf0RP_bc` applies; Eisenstein at `q = t + 1`
(`a₀ = −x q`). `ram0Cands` finds the S-unit over the new base; `searchET0RP … 0 = some false`:
**`∫ √(x eˣ + x) dx` is not elementary**, while `∫ θ′` is found.

A curve of genus `1`: `θ² = e³ˣ + x` (slope `3/2` at infinity, fibre `θ² = x` above `0`). Over
`w² = x` the points `(0, ±w)` of `θ² = t³ + w²` are `3`-torsion (flexes), so `(θ − w)` is an S-unit
with divisor `3 P0₊ − 3 P∞`, found by `ram0Cands` (`μ ≤ 3`); the search answers in seconds:
**`∫ √(e³ˣ + x) dx` is not elementary**.
-/

namespace Curves.MT.KBEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX

/-- `θ² = x t + x` over the original base and its translation. -/
def PX : List (GPoly (LC 0)) := [[cx [0, -1] [1], cx [0, -1] [1]], []]
def PX' : List (GPoly (LC 0)) := PX.map (·.map (tauC Fc' Yc 0))

#guard eisCk Fc' ks' 0 PX' [cx [1] [1], cx [1] [1]] [[cx [0, -1] [1]], []] [] [cx [-1] [0, 1]] []
  [cx [1] [1]]
#guard ramShapeC Fc' ks' 0 PX' 2 1 [cx [0, 1] [1]]
#guard split0C Fc' ks' 0 PX' [wC, mwC]

def PCX : GPoly (LC 1) := nkPC Fc' ks' 0 PX'
def dθX : GPoly (LC 1) := (dThetaC (MOr Fc' ks' 1) PCX).getD []
def wθX : GPoly (LC 1) := (invModC (MOr Fc' ks' 1) PCX (GPoly.derivX (MOr Fc' ks' 1) PCX)).getD []
def sX : List (LC 1) := traceCodes Fc' ks' 0 PCX

#guard traceW Fc' ks' 0 PX' dθX wθX sX

def candsX : List (CandET0R 0) := ram0Cands Fc' ks' 0 2 1 6 3 2 PX' [cx [0, 1] [1]] [wC, mwC] ηc'
def restX : List (LC 1) :=
  nkRest Fc' ks' 0 (nkFl Fc' ks' 0 fθ') (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') sX)

-- `τ(θ) = 0` and no exact part: **`∫ √(x eˣ + x) dx` is not elementary**
#guard (MOr Fc' ks' 1).isZero (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') sX)
#guard searchET0RP Fc' ks' 0 (tauC Fc' Yc 0 xc) (prdeC Fc' ks' lv' 0) PX' 2 dθX wθX sX restX candsX 0 =
  some false

/-- `θ′` in the basis `1, θ` (control). -/
def dθX2 : List (LC 1) := (List.range 2).map fun j ↦ dθX.getD j (MOr Fc' ks' 1).zero

#guard searchET0RP Fc' ks' 0 (tauC Fc' Yc 0 xc) (prdeC Fc' ks' lv' 0) PX' 2 dθX wθX sX dθX2 candsX 0 =
  some true

/-- `θ² = t³ + x`, Eisenstein at `q = t³ + x` (Bézout `(1/x) q − (t/(3x)) q′ = 1`). -/
def PE : List (GPoly (LC 0)) := [[cx [0, -1] [1], [], [], cx [-1] [1]], []]
def PE' : List (GPoly (LC 0)) := PE.map (·.map (tauC Fc' Yc 0))

#guard eisCk Fc' ks' 0 PE' [cx [0, 1] [1], [], [], cx [1] [1]] [[cx [-1] [1]], []] [] [cx [-1] [1]]
  [cx [1] [0, 1]] [[], cx [-1] [0, 3]]
#guard ramShapeC Fc' ks' 0 PE' 2 3 [cx [1] [1]]
#guard split0C Fc' ks' 0 PE' [wC, mwC]

def PCE : GPoly (LC 1) := nkPC Fc' ks' 0 PE'
def dθE : GPoly (LC 1) := (dThetaC (MOr Fc' ks' 1) PCE).getD []
def wθE : GPoly (LC 1) := (invModC (MOr Fc' ks' 1) PCE (GPoly.derivX (MOr Fc' ks' 1) PCE)).getD []
def sEl : List (LC 1) := traceCodes Fc' ks' 0 PCE

#guard traceW Fc' ks' 0 PE' dθE wθE sEl

def candsE : List (CandET0R 0) := ram0Cands Fc' ks' 0 2 3 8 4 4 PE' [cx [1] [1]] [wC, mwC] ηc'
def restE : List (LC 1) :=
  nkRest Fc' ks' 0 (nkFl Fc' ks' 0 fθ') (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') sEl)

-- **`∫ √(e³ˣ + x) dx` is not elementary** (genus `1`)
#guard (MOr Fc' ks' 1).isZero (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') sEl)
#guard searchET0RP Fc' ks' 0 (tauC Fc' Yc 0 xc) (prdeC Fc' ks' lv' 0) PE' 2 dθE wθE sEl restE candsE 0 =
  some false

/-- `θ′` in the basis `1, θ` (control). -/
def dθE2 : List (LC 1) := (List.range 2).map fun j ↦ dθE.getD j (MOr Fc' ks' 1).zero

#guard searchET0RP Fc' ks' 0 (tauC Fc' Yc 0 xc) (prdeC Fc' ks' lv' 0) PE' 2 dθE wθE sEl dθE2 candsE 0 =
  some true

end Curves.MT.KBEx
