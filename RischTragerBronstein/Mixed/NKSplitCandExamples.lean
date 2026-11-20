import RischTragerBronstein.Mixed.NKSplitCand
import RischTragerBronstein.Mixed.NKInfRVExample
import RischTragerBronstein.Mixed.NKInfRVExpExample

/-!
# The split-at-infinity decisions with computed candidates

The candidates of `splitCandsL`/`splitCandsE` (units by linear algebra along the places at
infinity, normalized to norm `1`; basis, shifts and gauges from the leading values `γₖ = ±1`)
make the searches answer at bound `0`, with no data supplied by hand:

* `θ² = log² x + x` (`NKInfRVExample`): the computed unit is `(θ − t)²/(−x)` reduced modulo the
  curve; `searchIVGP … 0 = some false`: **`∫ √(log² x + x) dx` is not elementary**
  (`nk_decidesInfVGP`; `τ(θ) = 0`, so `elM` is not needed);
* `θ² = e²ˣ + x eˣ` (`NKInfRVExpExample`): `searchETVGP … 0 = some false`:
  **`∫ √(e²ˣ + x eˣ) dx` is not elementary** (`nk_decidesETInfVGP`).
-/

namespace Curves.MT.NKSplitCandEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX

namespace Log

open Curves.MT.NKInfRVEx Curves.MT.NKExEx

def SU := (splitUnits Fc ks 0 1 6 3 2 Pp [cq 1, cq (-1)]).getD ([], [], [], [], [], [], [], [])
def dθA : GPoly (LC 1) := SU.2.2.2.2.2.1
def wθA : GPoly (LC 1) := SU.2.2.2.2.2.2.1
def sA : List (LC 1) := SU.2.2.2.2.2.2.2

#guard traceW Fc ks 0 Pp dθA wθA sA
#guard unitsC Fc ks 0 Pp SU.1 SU.2.1 SU.2.2.1 dθA wθA sA
#guard indepC Fc ks 0 SU.2.2.1 SU.2.2.2.1 SU.2.2.2.2.1

def restA : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sA)

#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sA)
#guard searchIVGP Fc ks 0 ic (prdeC Fc ks lv 0) Pp dθA wθA sA restA
  (splitCandsL Fc ks 0 1 6 3 2 Pp [cq 1, cq (-1)]) 0 = some false

end Log

namespace Exp

open Curves.MT.NKInfRVExpEx Curves.MT.NKExEE

def SU := (splitUnits Fc ks 0 1 6 3 2 Pp [cq 1, cq (-1)]).getD ([], [], [], [], [], [], [], [])
def dθA : GPoly (LC 1) := SU.2.2.2.2.2.1
def wθA : GPoly (LC 1) := SU.2.2.2.2.2.2.1
def sA : List (LC 1) := SU.2.2.2.2.2.2.2

#guard traceW Fc ks 0 Pp dθA wθA sA
#guard unitsC Fc ks 0 Pp SU.1 SU.2.1 SU.2.2.1 dθA wθA sA
#guard indepC Fc ks 0 SU.2.2.1 SU.2.2.2.1 SU.2.2.2.2.1

def restA : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sA)

#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sA)
#guard searchETVGP Fc ks 0 xc (prdeC Fc ks lv 0) Pp dθA wθA sA restA
  (splitCandsE Fc ks 0 1 6 3 2 Pp [cq 1, cq (-1)]) 0 = some false

end Exp

end Curves.MT.NKSplitCandEx
