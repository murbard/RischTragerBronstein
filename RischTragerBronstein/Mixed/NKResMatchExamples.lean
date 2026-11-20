import RischTragerBronstein.Mixed.NKDecidesInfVMR1
import RischTragerBronstein.Mixed.NKUnitsDExamples

/-!
# Example: residues at infinity matched by a unit

The curve of `NKUnitsDExamples`: `θ² = t² (t² + x)` (`t = log x`), one segment of slope `2` with
residual `Z² − 1` (two places, `θ ≈ ±t²`), the unit `w = U/t²` (`U = −(θ + t²)²/x`). For
`f = (t/x³) θ` the residues at infinity are non-zero (`multiResCk` fails: `[τ⁴] Θ = ∓x²/8`, so the
residue coefficients are `∓1/(8x) = ∓η/8`). The `τ`-orders of `U` along the places are `−4` and `0`
(`ordCk`), and `κ = −1/16` matches the residues (`multiMatchCk`). With `τ(f) = 0`, the search with
`g = w′/w` answers `some false`: by `nk_decidesInfVMR1`, **`∫ (log x/x³) √(log² x (log² x + x)) dx`
is not elementary**. Control: `θ′ − g/16` has an exact part. (About 30 seconds.)
-/

namespace Curves.MT.NKResMatchEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKMultiEx
  Curves.MT.NKUnitsDEx

def βs : List (List (LC 0)) := [[one0, cq (-1)]]
def Θs : List (List (GPoly (LC 0))) := multiHensel Fc ks 0 NKUnitsDEx.Pp NKUnitsDEx.segs βs 10
/-- `f = (t/x³) θ`. -/
def f3 : List (GPoly (LC 0)) := [[], [[], [([1], [0, 0, 0, 1])]]]
def os : List (List (List ℤ)) := [[[-4], [0]]]

-- non-zero residues: the zero-residue certificate fails
#guard !multiResCk Fc ks lv 0 NKUnitsDEx.Pp NKUnitsDEx.segs βs Θs 10 f3
-- the orders of `U` along the places
#guard ordCk Fc ks 0 1 2 10 NKUnitsDEx.U ((Θs.getD 0 []).getD 0 []) (-4)
#guard ordCk Fc ks 0 1 2 10 NKUnitsDEx.U ((Θs.getD 0 []).getD 1 []) 0
-- the residues are matched by `κ = −1/16`
#guard multiMatchCk Fc ks lv 0 ic NKUnitsDEx.Pp NKUnitsDEx.segs βs Θs 10 f3 [NKUnitsDEx.U]
  [NKUnitsDEx.d] os [-1/16]

def pre0 : List (CandIVR0 0) := [((I2, I2, rr2, Vg.1, Vg.2), []), ((I2, I2, rr2, Vg.2, Vg.1), [])]
def tau3 : LC 1 := nkTau Fc ks 0 2 (nkFl Fc ks 0 f3) NKUnitsDEx.sM
def rest3 : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 f3) tau3
#guard (MOr Fc ks 1).isZero tau3
-- **not elementary**
#guard searchIVR1P Fc ks 0 ic (prdeC Fc ks lv 0) NKUnitsDEx.Pp rest3 NKUnitsDEx.gls pre0 0 =
  some false
-- control: `θ′ − g/16`
def ctrl : List (LC 1) := (List.range 2).map fun j ↦
  (MOr Fc ks 1).add (NKUnitsDEx.dθM.getD j (MOr Fc ks 1).zero)
    ((MOr Fc ks 1).mul (mcst Fc ks 1 (-1/16)) (NKUnitsDEx.gl.getD j (MOr Fc ks 1).zero))
#guard searchIVR1P Fc ks 0 ic (prdeC Fc ks lv 0) NKUnitsDEx.Pp ctrl NKUnitsDEx.gls pre0 0 =
  some true

end Curves.MT.NKResMatchEx
