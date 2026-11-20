import RischTragerBronstein.Mixed.NKRamZeroCand
import RischTragerBronstein.Mixed.NKInfRVExample

/-!
# Example: zero residues at ramified places at infinity, no units

Tower `x`, `t = log x`, `θ⁴ − 5t θ² + 4t² + x t = 0` (Eisenstein at `t`). One slope `1/2` at
infinity with residual `(Z² − 1)(Z² − 4)`: two places, each of ramification `2` (`θ² ≈ t`,
`θ² ≈ 4t`). The expanded inverted curve is `Z⁴ − 5Z² + 4 + x T²`; one residual root per place
(`γ = 1, 2`), Newton lifts (`henselC`) and the residue coefficient `[T³] Θ = 0` of `f = θ`:
`splitResRamCk` passes. `τ(θ) = 0` and the units-free search (`ramZCands`, `searchIVR0P`) answers
`some false`: by `nk_decidesInfVR0P`, **`∫ θ dx` is not elementary** — no unit was needed.
Control: `θ′` gives `some true`. (About 6 minutes.)
-/

namespace Curves.MT.NKZeroResRamEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKInfRVEx

/-- `θ⁴ − 5t θ² + 4t² + x t = 0`. -/
def Pp4 : List (GPoly (LC 0)) := [[[], px, cq 4], [], [[], cq (-5)], []]
def qE4 : GPoly (LC 0) := [[], one0]
def csE4 : List (GPoly (LC 0)) := [[px, cq 4], [], [cq (-5)], []]
def sE4 : GPoly (LC 0) := [cqx (-4)]
def tE4 : GPoly (LC 0) := [cqx 1]
def s2E4 : GPoly (LC 0) := []
def t2E4 : GPoly (LC 0) := [one0]

#guard eisCk Fc ks 0 Pp4 qE4 csE4 sE4 tE4 s2E4 t2E4
#guard ramShapeC Fc ks 0 Pp4 2 1 [cq 1, cq 4]

def γR : List (LC 0) := [cq 1, cq 2]
def Ppe : List (GPoly (LC 0)) := Pp4.map (expandGC Fc ks 0 2)
def Θs : List (GPoly (LC 0)) := γR.map (henselC Fc ks 0 1 6 Ppe)
def fθ4 : List (GPoly (LC 0)) := [[], [one0], [], []]

#guard splitResRamCk Fc ks lv 0 2 1 6 Pp4 γR Θs fθ4

def P4 : GPoly (LC 1) := nkPC Fc ks 0 Pp4
def dθA : GPoly (LC 1) := (dThetaC (MOr Fc ks 1) P4).getD []
def wθA : GPoly (LC 1) := (invModC (MOr Fc ks 1) P4 (GPoly.derivX (MOr Fc ks 1) P4)).getD []
def sA : List (LC 1) := traceCodes Fc ks 0 P4

#guard traceW Fc ks 0 Pp4 dθA wθA sA
def restA : List (LC 1) :=
  nkRest Fc ks 0 (nkFl Fc ks 0 fθ4) (nkTau Fc ks 0 4 (nkFl Fc ks 0 fθ4) sA)
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 4 (nkFl Fc ks 0 fθ4) sA)
#guard searchIVR0P Fc ks 0 ic (prdeC Fc ks lv 0) Pp4 restA (ramZCands Fc ks 0 2 1 4 [cq 1, cq 4]) 0 =
  some false
def dθ4 : List (LC 1) := (List.range 4).map fun j ↦ dθA.getD j (MOr Fc ks 1).zero
#guard searchIVR0P Fc ks 0 ic (prdeC Fc ks lv 0) Pp4 dθ4 (ramZCands Fc ks 0 2 1 4 [cq 1, cq 4]) 0 =
  some true

end Curves.MT.NKZeroResRamEx
