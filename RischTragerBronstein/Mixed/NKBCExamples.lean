import RischTragerBronstein.Mixed.NKBC
import RischTragerBronstein.Mixed.KBExamples

/-!
# A non-rational place above `t = 0`: `√(e²ˣ + x eˣ + x)`

Over `x`, `t = eˣ`, the curve `θ² = t² + x t + x` has two places at infinity (`θ ≈ ±t`) and a single
place above `t = 0` with residue field `ℚ(x)(√x)` (`θ² = x`): not rational, so `split0C` fails over
the base `ℚ(x)`. After the change of base curve to `w² = x` (`Mixed/KBExamples`: `Fc'`, `Yc`,
`bcOK`) the fibre splits (`θ = ±w`) and `nk_decidesETInf0P_bc` applies: the data below are the
translated curve, its Eisenstein certificate at `q = t² + x t + x` (Bézout `(4/(4x − x²)) q −
((2t + x)/(4x − x²)) q′ = 1`), the shapes at infinity and at `0`, and the trace certificate, all
checked; the candidates (`split0CandsA`) find the S-units over the new base.

The search itself takes about 10 minutes and is run by `#eval` outside the build:

    searchET0P Fc' ks' 0 (tauC Fc' Yc 0 xc) (prdeC Fc' ks' lv' 0) Pp' dθ' wθ' s' rest'
      (split0CandsA Fc' ks' 0 1 6 3 2 Pp' [cx [1] [1], cx [-1] [1]] [wC, mwC] ηc') 0 = some false

so **`∫ √(e²ˣ + x eˣ + x) dx` is not elementary** (the first candidate answers).

A non-rational pair of places at infinity: `θ² = x e²ˣ + eˣ` has leading values `±√x` and a single
ramified place above `t = 0`; over `w² = x` the places at infinity are split (`γ = ±w`) and
`nk_decidesETInfVGP_bc` applies; `searchETVGP` with `splitCandsE` answers in seconds:
**`∫ √(x e²ˣ + eˣ) dx` is not elementary**, while `∫ θ′` is found.
-/

namespace Curves.MT.KBEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX

/-- Codes over the base curve `w² = x`: `n(x)/d(x)` (degree `0` in `w`), `w` and `−w`. -/
def cx (n d : CPoly ℚ) : GPoly (GFrac ℚ) := [(n, d)]
def wC : GPoly (GFrac ℚ) := [([], [1]), ([1], [1])]
def mwC : GPoly (GFrac ℚ) := [([], [1]), ([-1], [1])]

/-- `θ² = t² + x t + x` over the original base (`y = x`), and its translation. -/
def PpO : List (GPoly (LC 0)) := [[cx [0, -1] [1], cx [0, -1] [1], cx [-1] [1]], []]
def Pp' : List (GPoly (LC 0)) := PpO.map (·.map (tauC Fc' Yc 0))
def qE' : GPoly (LC 0) := [cx [0, 1] [1], cx [0, 1] [1], cx [1] [1]]
def csE' : List (GPoly (LC 0)) := [[cx [-1] [1]], []]
def s2E' : GPoly (LC 0) := [cx [4] [0, 4, -1]]
def t2E' : GPoly (LC 0) := [cx [-1] [4, -1], cx [-2] [0, 4, -1]]

#guard eisCk Fc' ks' 0 Pp' qE' csE' [] [cx [-1] [1]] s2E' t2E'
#guard splitShapeC Fc' ks' 0 Pp' 1 [cx [1] [1], cx [-1] [1]]
#guard split0C Fc' ks' 0 Pp' [wC, mwC]

def PC' : GPoly (LC 1) := nkPC Fc' ks' 0 Pp'
def dθ' : GPoly (LC 1) := (dThetaC (MOr Fc' ks' 1) PC').getD []
def wθ' : GPoly (LC 1) := (invModC (MOr Fc' ks' 1) PC' (GPoly.derivX (MOr Fc' ks' 1) PC')).getD []
def s' : List (LC 1) := traceCodes Fc' ks' 0 PC'

#guard traceW Fc' ks' 0 Pp' dθ' wθ' s'

def fθ' : List (GPoly (LC 0)) := [[], [[([1], [1])]]].map (·.map (tauC Fc' Yc 0))
def rest' : List (LC 1) :=
  nkRest Fc' ks' 0 (nkFl Fc' ks' 0 fθ') (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') s')
def ηc' : LC 0 := (MO Fc' ks' 0).deriv (tauC Fc' Yc 0 xc)

-- `τ(θ) = 0`
#guard (MOr Fc' ks' 1).isZero (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') s')
-- the S-units over the new base (divisors `P∞₀ − P∞₁` and `P0₀ − P∞₁`) are found
#guard (split0Units Fc' ks' 0 1 6 3 2 Pp' [cx [1] [1], cx [-1] [1]] [wC, mwC]).map
  (fun u ↦ (u.1.length, u.2.2.1, u.2.2.2)) = some (2, [0, 2], [0, 1])

/-- `θ² = x t² + t` over the original base, its translation, Eisenstein at `q = t² + t/x`
(`a₀ = −x q`, Bézout `−4x² q + (2x² t + x) q′ = 1`). -/
def PpI : List (GPoly (LC 0)) := [[[], cx [-1] [1], cx [0, -1] [1]], []]
def PpI' : List (GPoly (LC 0)) := PpI.map (·.map (tauC Fc' Yc 0))
def qI : GPoly (LC 0) := [[], cx [1] [0, 1], cx [1] [1]]
def csI : List (GPoly (LC 0)) := [[cx [0, -1] [1]], []]
def s2I : GPoly (LC 0) := [cx [0, 0, -4] [1]]
def t2I : GPoly (LC 0) := [cx [0, 1] [1], cx [0, 0, 2] [1]]

#guard eisCk Fc' ks' 0 PpI' qI csI [] [cx [-1] [0, 1]] s2I t2I
#guard splitShapeC Fc' ks' 0 PpI' 1 [wC, mwC]
#guard nkShape0 Fc' ks' 0 PpI'

def PCI : GPoly (LC 1) := nkPC Fc' ks' 0 PpI'
def dθI : GPoly (LC 1) := (dThetaC (MOr Fc' ks' 1) PCI).getD []
def wθI : GPoly (LC 1) := (invModC (MOr Fc' ks' 1) PCI (GPoly.derivX (MOr Fc' ks' 1) PCI)).getD []
def sI : List (LC 1) := traceCodes Fc' ks' 0 PCI

#guard traceW Fc' ks' 0 PpI' dθI wθI sI

def restI : List (LC 1) :=
  nkRest Fc' ks' 0 (nkFl Fc' ks' 0 fθ') (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') sI)

-- `τ(θ) = 0` and no exact part: **`∫ √(x e²ˣ + eˣ) dx` is not elementary**
#guard (MOr Fc' ks' 1).isZero (nkTau Fc' ks' 0 2 (nkFl Fc' ks' 0 fθ') sI)
#guard searchETVGP Fc' ks' 0 (tauC Fc' Yc 0 xc) (prdeC Fc' ks' lv' 0) PpI' dθI wθI sI restI
  (splitCandsE Fc' ks' 0 1 6 3 2 PpI' [wC, mwC]) 0 = some false

/-- `θ′` in the basis `1, θ` (control). -/
def dθI2 : List (LC 1) := (List.range 2).map fun j ↦ dθI.getD j (MOr Fc' ks' 1).zero

#guard searchETVGP Fc' ks' 0 (tauC Fc' Yc 0 xc) (prdeC Fc' ks' lv' 0) PpI' dθI wθI sI dθI2
  (splitCandsE Fc' ks' 0 1 6 3 2 PpI' [wC, mwC]) 0 = some true

end Curves.MT.KBEx
