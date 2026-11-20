import RischTragerBronstein.Mixed.NKInf2KExpExChk4

/-! Kernel checks for `NKInf2KExpExample` (prime certificate at 41); split for memory. -/

namespace Curves.MT.NKInf2KExpEx

open Curves Curves.LT Curves.MT CPoly Sup GTors Tower.Sys Tower.NestX Curves.MT.NKExEE Polynomial

set_option maxRecDepth 200000 in
lemma okP41 : primeCheck R41 TT P41 = true := by decide +kernel

end Curves.MT.NKInf2KExpEx
