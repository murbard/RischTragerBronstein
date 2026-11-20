import RischTragerBronstein.Mixed.NKInf2KExChk5

/-! Kernel checks for `NKInf2KExample` (place data at 37); split for memory. -/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial

set_option maxRecDepth 200000 in
lemma okQ37 : Pc2.primeCheck R37 TT.Fc TT.n TT.I.δL TT.I.Bc TT.I.Dc P37.xs Q37 = true := by
  decide +kernel

end Curves.MT.NKInf2KEx
