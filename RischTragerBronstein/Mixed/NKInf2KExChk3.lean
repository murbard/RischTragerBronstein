import RischTragerBronstein.Mixed.NKInf2KExChk2c

/-! Kernel checks for `NKInf2KExample` (prime certificate at 7); split for memory. -/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial

set_option maxRecDepth 200000 in
lemma okP7 : primeCheck R7 TT P7 = true := by decide +kernel

end Curves.MT.NKInf2KEx
