import RischTragerBronstein.Mixed.NKLogCert
import RischTragerBronstein.Mixed.NKLogExamples

/-!
# Example: non-zero residues with a logarithm certificate

Over `θ³ − θ − log x = 0`, `f = θ + θ′/θ` has non-zero residues (at the zeros of `θ`, above
`t = 0`). With the certificate `u = θ`, `c = 1` (`logCert`: `f − θ − θ′/θ ≡ 0`), `g = θ` is
residue-free (`resCert` with `D = 1`, `k = 1`), `τ(g) = 0`, and `exactG` answers `some false`: by
`nk_iffC`, **`∫ (θ + θ′/θ)` is not elementary**.
-/

namespace Curves.MT.NKLogCertEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogEx

def D1 : GPoly (LC 0) := [one0]
def dθP : GPoly (LC 1) := (dThetaC O1 PC).getD []
def uθ : GPoly (LC 1) := [zer, onec]
def ld : GPoly (LC 1) := (logDerC O1 PC dθP uθ).getD []
def pad3 (l : GPoly (LC 1)) : List (LC 1) := (List.range 3).map fun j ↦ l.getD j O1.zero
/-- `g = θ`. -/
def gp : List (GPoly (LC 0)) := [[], [one0], []]
/-- `f = θ + θ′/θ`. -/
def flC : List (LC 1) := pad3 (GPoly.add O1 (nkFlR 0 gp D1) ld)

#guard GPoly.squarefreeCheck (MO Fc ks 0) D1
#guard resCert Fc ks 0 Pp gp D1 1 gp
#guard logCert Fc ks 0 PC flC (nkFlR 0 gp D1) [uθ] [1]
-- (about 20 s)
#guard exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) PC
  (nkRest Fc ks 0 (nkFlR 0 gp D1) (nkTau Fc ks 0 3 (nkFlR 0 gp D1) sC)) = some false

end Curves.MT.NKLogCertEx
