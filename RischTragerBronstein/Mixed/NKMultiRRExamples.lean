import RischTragerBronstein.Mixed.NKDecidesInfVMRR
import RischTragerBronstein.Mixed.NKMultiRC
import RischTragerBronstein.Mixed.NKMultiRExamples

/-!
# Example: several slopes at infinity and a residue-free pole

On `θ³ − t θ + x t = 0` over `t = log x` (`Mixed/NKMultiRExamples`), the integrand `θ/t` has a pole
above `t = 0`, which is a single totally ramified place (Eisenstein): `θ³ = t (θ − x)`, so
`resCert` holds with `k = 3`, `U = θ − x`, and `θ dx/t` has no pole there. By `nk_decidesInfVMRR`:
**`∫ θ/log x dx` is not elementary** (`τ = 0`, no exact part); control: `∫ (θ/t)′` is found
elementary.

With a non-zero residue (`nk_decidesInfVMRC`): `f = θ′/θ + θ/log x` (residue `1` above `t = 0`,
where `θ` vanishes); the certificate `(θ, 1)` (`logCert`) reduces it to `θ/log x`: **`∫ (θ′/θ +
θ/log x) dx` is not elementary**.
-/

namespace Curves.MT.NKMultiREx
open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKMultiEx

/-- `θ/t`: `b = θ`, `D = t`. -/
def fpR : List (GPoly (LC 0)) := [[], [one0], []]
def DR : GPoly (LC 0) := [[], one0]
#guard GPoly.squarefreeCheck (MO Fc ks 0) DR
#guard resCert Fc ks 0 Pp fpR DR 3 [[mx], [one0]]
def tauR : LC 1 := nkTau Fc ks 0 3 (nkFlR 0 fpR DR) sM
def restR : List (LC 1) := nkRest Fc ks 0 (nkFlR 0 fpR DR) tauR
#guard elM Fc ks lv 1 tauR 3 = some true
-- **`∫ θ/log x dx` is not elementary**
#guard searchIVMP Fc ks 0 ic (prdeC Fc ks lv 0) Pp (nPlacesR segs) dθM wθM sM restR pre 0 =
  some false
/-- `(θ/t)′ = θ′/t − θ/(x t²)` in the basis `1, θ, θ²` (control). -/
def dR : List (LC 1) :=
  let tinv := O1.inv tC
  (List.range 3).map fun j ↦ O1.add (O1.mul (dθM.getD j O1.zero) tinv)
    (O1.neg (if j = 1 then O1.mul (([ic], [one0]) : LC 1) (O1.mul tinv tinv) else O1.zero))
#guard searchIVMP Fc ks 0 ic (prdeC Fc ks lv 0) Pp (nPlacesR segs) dθM wθM sM dR pre 0 =
  some true

/-- `θ′/θ + θ/t` in the basis `1, θ, θ²` and the certificate `(θ, 1)`. -/
def ldθ : GPoly (LC 1) := (logDerC O1 PC dθM [zer, onec]).getD []
def flC : List (LC 1) := (List.range 3).map fun j ↦
  O1.add (ldθ.getD j O1.zero) ((nkFlR 0 fpR DR).getD j O1.zero)
#guard logCert Fc ks 0 PC flC (nkFlR 0 fpR DR) [[zer, onec]] [1]

end Curves.MT.NKMultiREx
