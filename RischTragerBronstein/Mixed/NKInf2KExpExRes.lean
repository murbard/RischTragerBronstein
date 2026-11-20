import RischTragerBronstein.Mixed.NKInf2KExpExample

/-! Kernel check of the exact-part answer of `NKInf2KExpExample` (alone in its module: about 6 min,
65G peak — beyond a 32G machine). -/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial

set_option maxHeartbeats 0 in
set_option maxRecDepth 400000 in
/-- `θ` has no exact part in the basis `1, θ/t²` (kernel-checked). -/
lemma hresK : exactTLEVG Fc ks 0 xc (prdeC Fc ks lv 0) [] Cg Cgi r C Ci dg0 PC Tc Ti restθ [] =
    some false := by
  decide +kernel

end Curves.MT.NKInf2KExpEx
