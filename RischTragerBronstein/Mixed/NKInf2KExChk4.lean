import RischTragerBronstein.Mixed.NKInf2KExChk3

/-! Kernel checks for `NKInf2KExample` (place data at 7); split for memory. -/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial

set_option maxRecDepth 200000 in
lemma okQ7 : Pc2.primeCheck R7 TT.Fc TT.n TT.I.δL TT.I.Bc TT.I.Dc P7.xs Q7 = true := by
  decide +kernel

end Curves.MT.NKInf2KEx
