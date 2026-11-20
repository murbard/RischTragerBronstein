import RischTragerBronstein.Mixed.NKDecidesInfVMR0
import RischTragerBronstein.Mixed.NKMultiRExamples

/-!
# Example: several Newton segments at infinity, zero residues, no units

The curve of `NKMultiRExamples`: `θ³ − t θ + x t = 0` (`t = log x`), segments `(e, s) = (2, 1)`
(`θ ≈ ±√t`, one ramified place) and `(1, 0)` (`θ ≈ x`). Segment polynomials
`Z³ − Z + x τ` and `τ Z³ − Z + x` (not monic); the Newton lifts of `β = 1` and `β = x`
(`multiHensel`) are `1 − (x/2) τ − (3x²/8) τ² − (x³/2) τ³ + ⋯` and `x + x³ τ + ⋯`. For `f = θ` the
residue values `[τ³] Θ̃₁ = −x³/2` and `[τ] Θ̃₂ = x³` are derivatives: `multiResCk` passes. The
units-free search answers `some false`: by `nk_decidesInfVMR0`, **`∫ θ dx` is not elementary**,
without the unit `θ/x − 1`. Control: `θ′` gives `some true`. (About 1.5 minutes.)
-/

namespace Curves.MT.NKZeroResMultiEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKMultiEx
  Curves.MT.NKMultiREx

def βs : List (List (LC 0)) := [[one0], [px]]
def Θs : List (List (GPoly (LC 0))) := multiHensel Fc ks 0 NKMultiREx.Pp NKMultiREx.segs βs 6
#guard multiResCk Fc ks lv 0 NKMultiREx.Pp NKMultiREx.segs βs Θs 6 NKMultiREx.fθ
def pre0 : List (CandIVR0 0) := [((I3, I3, rr3, Ug, Ugi), []), ((I3, I3, rr3, Ugi, Ug), [])]
#guard searchIVR0P Fc ks 0 ic (prdeC Fc ks lv 0) NKMultiREx.Pp NKMultiREx.restθ pre0 0 =
  some false
#guard searchIVR0P Fc ks 0 ic (prdeC Fc ks lv 0) NKMultiREx.Pp
  ((List.range 3).map fun j ↦ NKMultiREx.dθM.getD j O1.zero) pre0 0 = some true

end Curves.MT.NKZeroResMultiEx
