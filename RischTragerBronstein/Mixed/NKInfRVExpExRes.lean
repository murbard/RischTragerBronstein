import RischTragerBronstein.Mixed.NKInfRVExpExample

/-! Kernel check of the exact-part answer of `NKInfRVExpExample` (alone in its module: it peaks
near 30G). With the structural `linSolve` the whole exact-part test reduces in the kernel. -/

namespace Curves.MT.NKInfRVExpEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEE

set_option maxHeartbeats 0 in
set_option maxRecDepth 400000 in
/-- `θ − c u₀′/u₀` is exact for no constant `c` (kernel-checked). -/
lemma hresK : exactTLEV Fc ks 0 xc (prdeC Fc ks lv 0) dg r Cg Cg dg0 PC Tc Tc restθ gls =
    some false := by
  decide +kernel

end Curves.MT.NKInfRVExpEx
