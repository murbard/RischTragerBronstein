import RischTragerBronstein.Mixed.NKSearch
import RischTragerBronstein.Mixed.NKLogCertExamples

/-!
# Example: an automatically found logarithm certificate

Over `θ³ − θ − log x = 0`, `f = θ + 2 θ′/θ − ½ (θ − 1)′/(θ − 1)` has residues `2`, `−½`, `0` at the
points `(0, 0)`, `(0, 1)`, `(0, −1)` above `t = 0`. Given only `f` and the fibre above `t = 0`,
`Search.findCert` finds `c = ½` and `u` with `div u = 4 (0,0) − (0,1) − 3 ∞` (the minimal-weight
element of the Riemann–Roch space), so that `g = f − ½ u′/u = θ`. The certificate is checked
(`logCert`, `resCert`), `τ(g) = 0`, and `exactG` answers `some false`: by `nk_iffC`, **`∫ f` is not
elementary** — with no certificate supplied by hand.
-/

namespace Curves.MT.NKSearchEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogEx
  Curves.MT.NKLogCertEx

def O0 := MO Fc ks 0
/-- `ω(a) − a′` at a primitive level with `t′ = 1/x`. -/
def sDen (a : LC 0) : LC 0 := O0.add ic (O0.neg (O0.deriv a))
def u1 : GPoly (LC 1) := [O1.neg onec, onec]
def ld1 : GPoly (LC 1) := (logDerC O1 PC dθP u1).getD []
/-- `f = θ + 2 θ′/θ − ½ (θ − 1)′/(θ − 1)`. -/
def fl2 : List (LC 1) := pad3 (GPoly.add O1 (GPoly.add O1 (nkFlR 0 gp D1)
  (GPoly.smul O1 (mcst Fc ks 1 2) ld)) (GPoly.smul O1 (mcst Fc ks 1 (-1/2)) ld1))

/-- The certificate, found by search. -/
def cert := (Search.findCert Fc ks 0 sDen Pp fl2 [(O0.zero, [O0.zero, O0.one, O0.neg O0.one])]
  8 2 12).getD ([], 0, [], [], 0, [])

#guard cert.2.1 = 1/2
#guard GPoly.squarefreeCheck (MO Fc ks 0) cert.2.2.2.1
#guard resCert Fc ks 0 Pp cert.2.2.1 cert.2.2.2.1 cert.2.2.2.2.1 cert.2.2.2.2.2
#guard logCert Fc ks 0 PC fl2 (nkFlR 0 cert.2.2.1 cert.2.2.2.1) [cert.1] [cert.2.1]
#guard exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) PC
  (nkRest Fc ks 0 (nkFlR 0 cert.2.2.1 cert.2.2.2.1)
    (nkTau Fc ks 0 3 (nkFlR 0 cert.2.2.1 cert.2.2.2.1) sC)) = some false

end Curves.MT.NKSearchEx
