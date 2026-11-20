import RischTragerBronstein.Mixed.NKExactG
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Examples: integrands with multiple poles where the derivation matrix is regular

Over `θ³ − θ − log x = 0` (`t = log x`), `exactG` with `primSysC` (`exactG_correct`, `primSpec`):
`1/log² x` has no antiderivative in `ℚ(x, log x, θ)`, while `(1/log x)′` has one. The common
denominator of `exactC` made the indicial norm vanish at `t = 0` (answer `none`).
-/

namespace Curves.MT.NKExG

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx

/-- `1/t²`. -/
def invt2 : LC 1 := (([one0] : GPoly (LC 0)), ([[], [], one0] : GPoly (LC 0)))

#guard exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) P [invt2, zer, zer] = some false
#guard exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) P [O1.deriv (O1.inv tC), zer, zer] = some true

end Curves.MT.NKExG
