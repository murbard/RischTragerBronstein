import RischTragerBronstein.Mixed.NKInf2NExpExample

namespace Curves.MT.NKInf2NEEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEE Polynomial Differential GTors

set_option maxHeartbeats 0 in
set_option maxRecDepth 400000 in
lemma hresK : exactTL Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp) rest gs = some true := by
  decide +kernel

end Curves.MT.NKInf2NEEx
