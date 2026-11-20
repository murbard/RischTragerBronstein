import RischTragerBronstein.Mixed.NKUnitFind
import RischTragerBronstein.Mixed.NKInfRNExample
import RischTragerBronstein.Mixed.NKInfRExample

/-!
# Example: the certificates of the several-places decision, found automatically

For `θ³ − t θ² − t = 0` over `t = log x` (`NKInfRNEx`: places at infinity `s = 0, ±i`),
`autoInfUnits` finds over `ℚ(i)` two units with divisors `P₀ − P₂`, `P₁ − P₂`, their inverses and
logarithmic derivatives, the independence certificate, the trace codes and the place
certificate; all the checks of `nk_iffRN` pass on them (`#guard`, about 40 s).
-/

namespace Curves.MT.NKUnitFindEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx GTors

abbrev MM := NKInfRNEx.MM
abbrev KK := NKInfRNEx.KK

def C? : Option (InfUnitsCert 0 KK) :=
  autoInfUnits Fc ks (NFC.rfNFZ MM) 0 NKInfRNEx.Pp NKInfRNEx.Fq 1 3 10 3 3 NKInf2NEx.μ

#guard C?.isSome
#guard (C?.map fun C ↦
  unitsRNC Fc ks 0 NKInfRNEx.Pp NKInf2NEx.μ C.Ass C.Bss C.gss C.dθ C.wθ C.s &&
  indepCN Fc ks 0 NKInf2NEx.μ C.gss C.J C.H &&
  traceW Fc ks 0 NKInfRNEx.Pp C.dθ C.wθ C.s &&
  C.Pc.check NKInfRNEx.FcK 3) = some true

/-! The rational case `θ³ + t θ² − t = 0` (`NKInfREx`, units over `ℚ`: `μ = X`). -/

def CQ? : Option (InfUnitsCert 0 NKInfREx.KK) :=
  autoInfUnits Fc ks (NFC.rfNFZ NKInfREx.MM) 0 NKInfREx.Pp NKInfREx.Fq 1 3 10 3 3 [0]

#guard (CQ?.map fun C ↦
  unitsRNC Fc ks 0 NKInfREx.Pp [0] C.Ass C.Bss C.gss C.dθ C.wθ C.s &&
  indepCN Fc ks 0 [0] C.gss C.J C.H &&
  traceW Fc ks 0 NKInfREx.Pp C.dθ C.wθ C.s &&
  C.Pc.check NKInfREx.FcK 3) = some true

end Curves.MT.NKUnitFindEx
