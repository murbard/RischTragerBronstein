import RischTragerBronstein.Mixed.NKInf2KExChk4

/-! Kernel checks for `NKInf2KExample` (prime certificate at 37); split for memory. -/

namespace Curves.MT.NKInf2KEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEx Polynomial

set_option maxRecDepth 200000 in
lemma okP37 : primeCheck R37 TT P37 = true := by decide +kernel

end Curves.MT.NKInf2KEx
