import RischTragerBronstein.Mixed.NKRamCand
import RischTragerBronstein.Mixed.NKInfRVExample
import RischTragerBronstein.Mixed.NKInfRVExpExample

/-!
# Ramified places at infinity: examples with computed candidates

* `θ⁴ = log² x + x` (`t = log x`): slope `1/2` at infinity, residual polynomial `W² − 1`, two
  places of ramification `2` (`θ² ≈ ±t`). The unit `(θ² − t)²/(−x)` comes from the split subcurve
  `φ² = t² + x`, `φ = θ²` (`ramUnits`). `searchIVRP … 0 = some false`:
  **`∫ (log² x + x)^{1/4} dx` is not elementary** (`nk_decidesInfVRP`; `τ(θ) = 0`).
* `θ⁴ = e²ˣ + x eˣ` (`t = eˣ`, a single place above `t = 0`): `searchETVRP … 0 = some false`:
  **`∫ (e²ˣ + x eˣ)^{1/4} dx` is not elementary** (`nk_decidesETInfVRP`).

Controls: with `f = θ′` both searches return `some true`. Each search runs in about 1.5 minutes.
-/

namespace Curves.MT.NKRamCandEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX

namespace Log

open Curves.MT.NKInfRVEx Curves.MT.NKExEx

/-- `θ⁴ = t² + x`. -/
def Pp4 : List (GPoly (LC 0)) := [[mx, [], cq (-1)], [], [], []]
def csE4 : List (GPoly (LC 0)) := [[cq (-1)], [], [], []]

#guard eisCk Fc ks 0 Pp4 qE csE4 sE tE s2E t2E
#guard ramShapeC Fc ks 0 Pp4 2 1 [cq 1, cq (-1)]

def RU := (ramUnits Fc ks 0 2 1 6 3 2 Pp4 [cq 1, cq (-1)]).getD ([], [], [], [], [], [], [], [])
def dθA : GPoly (LC 1) := RU.2.2.2.2.2.1
def wθA : GPoly (LC 1) := RU.2.2.2.2.2.2.1
def sA : List (LC 1) := RU.2.2.2.2.2.2.2

#guard traceW Fc ks 0 Pp4 dθA wθA sA
#guard unitsC Fc ks 0 Pp4 RU.1 RU.2.1 RU.2.2.1 dθA wθA sA
#guard indepC Fc ks 0 RU.2.2.1 RU.2.2.2.1 RU.2.2.2.2.1

def fθ4 : List (GPoly (LC 0)) := [[], [one0], [], []]
def restA : List (LC 1) :=
  nkRest Fc ks 0 (nkFl Fc ks 0 fθ4) (nkTau Fc ks 0 4 (nkFl Fc ks 0 fθ4) sA)

#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 4 (nkFl Fc ks 0 fθ4) sA)
#guard searchIVRP Fc ks 0 ic (prdeC Fc ks lv 0) Pp4 2 dθA wθA sA restA
  (ramCandsL Fc ks 0 2 1 6 3 2 Pp4 [cq 1, cq (-1)]) 0 = some false

/-- `θ′` in the basis `1, θ, θ², θ³` (control: `∫ θ′` is elementary). -/
def dθ4 : List (LC 1) :=
  let d := (dThetaC (MOr Fc ks 1) (nkPC Fc ks 0 Pp4)).getD []
  (List.range 4).map fun j ↦ d.getD j (MOr Fc ks 1).zero

#guard searchIVRP Fc ks 0 ic (prdeC Fc ks lv 0) Pp4 2 dθA wθA sA dθ4
  (ramCandsL Fc ks 0 2 1 6 3 2 Pp4 [cq 1, cq (-1)]) 0 = some true

end Log

namespace Exp

open Curves.MT.NKInfRVExpEx Curves.MT.NKExEE

/-- `θ⁴ = t² + x t`. -/
def Pp4 : List (GPoly (LC 0)) := [[[], mx, cq (-1)], [], [], []]
def csE4 : List (GPoly (LC 0)) := [[cq (-1)], [], [], []]

#guard eisCk Fc ks 0 Pp4 qE csE4 sE tE s2E t2E
#guard ramShapeC Fc ks 0 Pp4 2 1 [cq 1, cq (-1)]

def RU := (ramUnits Fc ks 0 2 1 6 3 2 Pp4 [cq 1, cq (-1)]).getD ([], [], [], [], [], [], [], [])
def dθA : GPoly (LC 1) := RU.2.2.2.2.2.1
def wθA : GPoly (LC 1) := RU.2.2.2.2.2.2.1
def sA : List (LC 1) := RU.2.2.2.2.2.2.2

#guard traceW Fc ks 0 Pp4 dθA wθA sA
#guard unitsC Fc ks 0 Pp4 RU.1 RU.2.1 RU.2.2.1 dθA wθA sA
#guard indepC Fc ks 0 RU.2.2.1 RU.2.2.2.1 RU.2.2.2.2.1

def fθ4 : List (GPoly (LC 0)) := [[], [one0], [], []]
def restA : List (LC 1) :=
  nkRest Fc ks 0 (nkFl Fc ks 0 fθ4) (nkTau Fc ks 0 4 (nkFl Fc ks 0 fθ4) sA)

#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 4 (nkFl Fc ks 0 fθ4) sA)
#guard searchETVRP Fc ks 0 xc (prdeC Fc ks lv 0) Pp4 2 dθA wθA sA restA
  (ramCandsE Fc ks 0 2 1 6 3 2 Pp4 [cq 1, cq (-1)]) 0 = some false

/-- `θ′` in the basis `1, θ, θ², θ³` (control). -/
def dθ4 : List (LC 1) :=
  let d := (dThetaC (MOr Fc ks 1) (nkPC Fc ks 0 Pp4)).getD []
  (List.range 4).map fun j ↦ d.getD j (MOr Fc ks 1).zero

#guard searchETVRP Fc ks 0 xc (prdeC Fc ks lv 0) Pp4 2 dθA wθA sA dθ4
  (ramCandsE Fc ks 0 2 1 6 3 2 Pp4 [cq 1, cq (-1)]) 0 = some true

end Exp

end Curves.MT.NKRamCandEx
