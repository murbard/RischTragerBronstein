import RischTragerBronstein.Mixed.NKDecidesInfVG0
import RischTragerBronstein.Mixed.NKInfRVExample

/-!
# Examples: zero residues at infinity, no units

Tower `x`, `t = log x`, `θ² = t² + x` (as in `NKInfRVExample`, but **without the unit**).
Inverted at infinity: `Q(T, Z) = Z² − 1 − x T²`, roots `Θ = ±(1 + (x/2) T² + O(T⁴))`, found by
Newton lifting (`henselC`). The residue coefficient of `∑ bⱼ θʲ` at the place `Θ` is
`∑ b_{j i} [T^{1+i+j}] Θʲ`:
* `f = θ`: `±x/2 = (±x²/4)′`, a derivative ⇒ residue `0`;
* `f = t θ`: `[T³] Θ = 0` ⇒ residue `0`.
So `splitRes0C` passes and `nk_decidesInfVG0` decides both integrals with no units:
**`∫ √(log² x + x) dx` and `∫ log x · √(log² x + x) dx` are not elementary**
(`τ(f) = 0`, and the exact parts do not exist). For `f = θ/x²` the residue coefficient `1/(2x)` is
not a derivative (residue `∓1/2`): the certificate correctly fails. Control: `θ′` has an exact part.
-/

namespace Curves.MT.NKZeroResEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKInfRVEx

def γs : List (LC 0) := [cq 1, cq (-1)]
def ΘL : List (GPoly (LC 0)) := γs.map (henselC Fc ks 0 1 5 Pp)

-- the lifts: `Θ = ±(1 + (x/2) T² + 0 T³ + ⋯)`
#guard (MO Fc ks 0).isZero ((MO Fc ks 0).add ((ΘL.getD 0 []).getD 2 []) [([0, -1/2], [1])])
#guard (MO Fc ks 0).isZero ((ΘL.getD 0 []).getD 3 [])

def fθ : List (GPoly (LC 0)) := [[], [one0]]
def ftθ : List (GPoly (LC 0)) := [[], [[], one0]]
def fθx : List (GPoly (LC 0)) := [[], [[([1], [0, 0, 1])]]]

#guard splitRes0C Fc ks lv 0 1 5 Pp γs fθ
#guard splitRes0C Fc ks lv 0 1 5 Pp γs ftθ
#guard !splitRes0C Fc ks lv 0 1 5 Pp γs fθx

def mone0 : LC 0 := [([-1], [1])]
def half0 : LC 0 := [([1/2], [1])]
def mhalf0 : LC 0 := [([-1/2], [1])]
def Cg : List (List (LC 0)) := [[one0, one0], [one0, mone0]]
def Cgi : List (List (LC 0)) := [[half0, half0], [half0, mhalf0]]

def rest (fp : List (GPoly (LC 0))) : List (LC 1) :=
  nkRest Fc ks 0 (nkFl Fc ks 0 fp) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC)

#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sC)
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 ftθ) sC)
-- control: `θ′` has an exact part
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi r PC Tc Tc
  ((List.range 2).map fun j ↦ dθ'.getD j O1.zero) [] = some true
-- no exact parts: by `nk_iffInfVG0` neither integral is elementary
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi r PC Tc Tc (rest fθ) [] = some false
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi r PC Tc Tc (rest ftθ) [] = some false

end Curves.MT.NKZeroResEx
