import RischTragerBronstein.Mixed.NKInf2ExpExample

/-! Kernel check of the exact-part answer of `NKInf2ExpExample` (alone in its module: ~29G peak). -/

namespace Curves.MT.NKInf2ExpEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEE Polynomial Differential

set_option maxHeartbeats 0 in
set_option maxRecDepth 400000 in
/-- `θ` has no exact part (kernel-checked). -/
lemma hresK : exactT Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
    (nkTi Fc ks 0 Pp) rest = some false := by
  decide +kernel

end Curves.MT.NKInf2ExpEx
