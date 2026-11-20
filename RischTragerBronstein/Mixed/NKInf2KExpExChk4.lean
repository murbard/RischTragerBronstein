import RischTragerBronstein.Mixed.NKInf2KExpExChk3

/-! Kernel checks for `NKInf2KExpExample` (place data at 13); split for memory. -/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial

set_option maxRecDepth 200000 in
lemma okQ13 : Pc2.primeCheck R13 TT.Fc TT.n TT.I.δL TT.I.Bc TT.I.Dc P13.xs Q13 = true := by
  decide +kernel

end Curves.MT.NKInf2KExpEx
