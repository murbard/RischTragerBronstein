import RischTragerBronstein.Mixed.NKInf2KExpExChk2c

/-! Kernel checks for `NKInf2KExpExample` (prime certificate at 13); split for memory. -/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial

set_option maxRecDepth 200000 in
lemma okP13 : primeCheck R13 TT P13 = true := by decide +kernel

end Curves.MT.NKInf2KExpEx
