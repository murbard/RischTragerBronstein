import RischTragerBronstein.Mixed.NKInf2KExChk1

/-! Kernel checks for `NKInf2KExample` (place certificate: the branch at the first place); split for memory. -/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial

set_option maxRecDepth 200000 in
lemma okRoot0 : rootCheck TT.Fc (Pc2.fα (Pc2.pj 0)) (Pc2.pe 0) (Pc2.pp 0) (Pc2.py 0) = true := by
  decide +kernel

end Curves.MT.NKInf2KEx
