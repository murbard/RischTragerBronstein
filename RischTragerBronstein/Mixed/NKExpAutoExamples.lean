import RischTragerBronstein.Mixed.NKExpAuto
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: an automatic constant change of basis at infinity

On `θ³ + eˣθ = eˣ + e²ˣ`, in the basis normal at infinity with two vectors swapped, the limit at
infinity is not upper triangular and `exactT` answers `none`; `exactTA` computes it, triangularizes
it over `ℚ` (`triCQ`) and decides in the new basis.
-/

namespace Curves.MT.NKExpAutoEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEE

def mone0 : GPoly (GFrac ℚ) := [([-1], [1])]
def Pp : List (GPoly (LC 0)) := [[[], mone0, mone0], [[], one0], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def S : QMat := fun i j ↦ ([[0, 1, 0], [1, 0, 0], [0, 0, 1]] : List (List ℚ)).getD i [] |>.getD j 0
def Si : QMat := fun i j ↦ ([[0, 1, 0], [1, 0, 0], [0, 0, 1]] : List (List ℚ)).getD i [] |>.getD j 0
def TcS := rowMix Fc ks 0 3 S (nkTc Fc ks 0 Pp)
def TiS := colMix Fc ks 0 3 (nkTi Fc ks 0 Pp) Si
def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []
def fθ' := (List.range 3).map fun j ↦ dθ'.getD j O1.zero
-- In the swapped basis the limit at infinity is not upper triangular: `exactT` answers `none`.
#guard exactT Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC TcS TiS fθ' = none
-- `exactTA` triangularizes it: `∫ θ′ = θ`.
#guard exactTA Fc ks 0 xc (rdeE Fc ks lv 0) PC TcS TiS fθ' = some true
-- and `θ` is not exact (`∫ θ dx` not elementary, `nk_iffETA`).
#guard exactTA Fc ks 0 xc (rdeE Fc ks lv 0) PC TcS TiS [zer, onec, zer] = some false

end Curves.MT.NKExpAutoEx
