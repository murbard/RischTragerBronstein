import RischTragerBronstein.Mixed.NKResNone
import RischTragerBronstein.Mixed.NKResMatchExamples

/-!
# Example: a place at infinity without a rational residue

On `θ² = log² x (log² x + x)` (as in `NKResMatchExamples`), `f = 8 t θ/(x² (x + 1))` has residue
coefficients `∓1/(x + 1)` at the two places at infinity. No rational `ρ` makes `1/(x + 1) + ρ/x` a
derivative in `ℚ(x)`: the parametric Risch equation only has solutions with zero first coordinate
(`noResCk`). By `nk_not_elem_noRes`, **`∫ 8 log x √(log² x (log² x + x)) / (x² (x + 1)) dx` is
not elementary**, without any unit or exact-part computation. For `f = (t/x³) θ` the residues are
rational and the certificate (correctly) does not apply.
-/

namespace Curves.MT.NKResNoneEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKMultiEx
  Curves.MT.NKUnitsDEx Curves.MT.NKResMatchEx

/-- `f = 8 t θ / (x² (x + 1))`. -/
def f4 : List (GPoly (LC 0)) := [[], [[], [([8], [0, 0, 1, 1])]]]
#guard placesCk Fc ks 0 NKUnitsDEx.Pp NKUnitsDEx.segs βs Θs 10 f4
#guard noResCk Fc ks lv 0 ic NKUnitsDEx.Pp NKUnitsDEx.segs βs Θs 10 f4 0 0
#guard !noResCk Fc ks lv 0 ic NKUnitsDEx.Pp NKUnitsDEx.segs βs Θs 10 f3 0 0

end Curves.MT.NKResNoneEx
