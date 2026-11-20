import RischTragerBronstein.Mixed.NKExpRes
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: a residue-free pole over an exponential level

Tower `x`, `t = eˣ`, `θ³ = t + t²`, `f = θ/(t + 1)`. The pole `t = −1` is residue-free:
`θ³ ≡ t (t + 1) mod P` (`resCert`, `k = 3`, `U = t`). By `nk_iffRE`,
**`∫ (eˣ + e²ˣ)^{1/3}/(eˣ + 1) dx` is not elementary** (`exactG` answers `some false`).

Non-zero residues with a logarithm certificate (`nk_iffCE`): `f = θ + θ′/θ`, certificate `u = θ`,
`c = 1`, `g = θ`; **`∫ (θ + θ′/θ) dx` is not elementary**.
-/

namespace Curves.MT.NKExpResEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEE

def mone0 : GPoly (GFrac ℚ) := [([-1], [1])]
def Pp : List (GPoly (LC 0)) := [[[], mone0, mone0], [], []]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, zer, zer]
def Dc : GPoly (LC 0) := [one0, one0]
def fpc : List (GPoly (LC 0)) := [[], [one0], []]
def Uc : List (GPoly (LC 0)) := [[[], one0]]
#guard GPoly.squarefreeCheck (MO Fc ks 0) Dc
#guard resCert Fc ks 0 Pp fpc Dc 3 Uc
#guard nkShape Fc ks 0 Pp
#guard nkShape0 Fc ks 0 Pp
#guard traceC Fc ks 0 PC sC
def flR : List (LC 1) := nkFlR 0 fpc Dc
-- `∫ (eˣ + e²ˣ)^{1/3}/(eˣ + 1) dx` is not elementary.
#guard exactG Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC
  (nkRest Fc ks 0 flR (nkTau Fc ks 0 3 flR sC)) = some false

-- `f = θ + θ′/θ`
def gp : List (GPoly (LC 0)) := [[], [one0], []]
def D1 : GPoly (LC 0) := [one0]
def dθ' : GPoly (LC 1) := (dThetaC O1 PC).getD []
def invθ : GPoly (LC 1) := (invModC O1 PC [zer, onec]).getD []
def flf : List (LC 1) := (List.range 3).map fun j ↦ O1.add (if j = 1 then onec else zer)
  ((remP O1 PC (GPoly.mul O1 dθ' invθ)).getD j O1.zero)
#guard logCert Fc ks 0 PC flf (nkFlR 0 gp D1) [[zer, onec]] [1]
#guard resCert Fc ks 0 Pp gp D1 1 gp
-- `∫ (θ + θ′/θ) dx` is not elementary.
#guard exactG Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC
  (nkRest Fc ks 0 (nkFlR 0 gp D1) (nkTau Fc ks 0 3 (nkFlR 0 gp D1) sC)) = some false

end Curves.MT.NKExpResEx
