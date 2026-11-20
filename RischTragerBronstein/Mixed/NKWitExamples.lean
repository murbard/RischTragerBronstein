import RischTragerBronstein.Mixed.NKDecidesTRExamples
import RischTragerBronstein.Mixed.NKWitP
import RischTragerBronstein.Mixed.FrontIntegrate

/-!
# Example: the exact part returned by the non-Kummer pipeline

Tower `x`, `t = log x`, `θ³ + tθ = t²` (as in `NKDecidesTRExamples`). The witness mirror of the
exact-part test (`exactTLSW`, with the precomputed basis normal at infinity) applied to `θ′`
(coordinates of `θ′` in the power basis) returns the exact part `Y = (0, 1, 0)`: `∫ θ′ = θ`
(valid by `exactTLSW_valid`; `nk_integrateTRP` for the whole decision).
-/

namespace Curves.MT.NKDecidesTREx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogTEx

/-- The exact part of `θ′`. -/
def witθ' : Option (Option (List ℚ × List (LC 1))) :=
  prefW (fun c ↦ exactTLSW Fc ks 0 ic (fun n A0 q hh G0 ↦ primSysB Fc ks 0 ic lim0 n A0 q hh G0 0)
    c.2.2 PC c.1 c.2.1 ((List.range 3).map fun j ↦ dθ'.getD j O1.zero) []) pre none

#guard (witθ'.map (Option.map fun w ↦ (w.1, w.2.map (Front.showLC Fc ks 1)))) =
  some (some ([], ["0", "((1))", "0"]))

end Curves.MT.NKDecidesTREx
