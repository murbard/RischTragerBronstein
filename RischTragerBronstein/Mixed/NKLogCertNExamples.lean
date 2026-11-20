import RischTragerBronstein.Mixed.NKLogCertN
import RischTragerBronstein.Mixed.NKLogCertExamples

/-!
# Example: irrational residues with an algebraic logarithm certificate

Over `θ³ − θ − log x = 0`, `f = θ + 4θ′/(θ² − 2)` has the residues `±√2` (at the points `θ = ±√2`).
With `α = √2` (`μ = X² − 2`) the certificate is `c₁ = α`, `u₁ = θ − α` and `c₂ = −α`, `u₂ = θ + α`
(`logCertN`; the inverses of `uᵢ` modulo `P` have coefficients in `ℚ(α)(t)`). Then `g = θ` is
residue-free, and `exactG` answers `some false`: by `nk_iffCN` (with `√2` among the constants),
**`∫ (θ + 4θ′/(θ² − 2))` is not elementary**.
-/

namespace Curves.MT.NKLogCertNEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogEx
  Curves.MT.NKLogCertEx

def μ2 : List ℤ := [-2, 0]
def cst0 (c : ℚ) : LC 0 := [([c], [1])]
/-- `t² − 2`. -/
def den : GPoly (LC 0) := [cst0 (-2), [], one0]
def tP : GPoly (LC 0) := [[], one0]
def rf (n : GPoly (LC 0)) : LC 1 := (n, den)
/-- The `α`-coordinates of `(θ − α)⁻¹ = (θ² + αθ + 1)(t + α)/(t² − 2)`. -/
def B0 : GPoly (LC 1) := [rf tP, rf [cst0 2], rf tP]
def B1 : GPoly (LC 1) := [rf [one0], rf tP, rf [one0]]
def A0 : List (GPoly (LC 0)) := [[], [one0]]
def wθ : GPoly (LC 1) := (invModC O1 PC (GPoly.derivX O1 PC)).getD []
def gOf (B : GPoly (LC 1)) : GPoly (LC 1) := remP O1 PC (GPoly.mul O1 dθP B)
def log1 : LogN 0 := ([A0, [[cst0 (-1)]]], [B0, B1], [gOf B0, gOf B1], [0, 1])
def log2 : LogN 0 := ([A0, [[one0]]], [B0, GPoly.neg O1 B1], [gOf B0, gOf (GPoly.neg O1 B1)], [0, -1])
def logs : List (LogN 0) := [log1, log2]
def tot : List (GPoly (LC 1)) := NCodes.nRed (θOps Fc ks 0) μ2 (logTotN Fc ks 0 logs)
/-- `f = θ + 4θ′/(θ² − 2)` (the rational part of the logarithms, plus `g = θ`). -/
def flN : List (LC 1) := pad3 (GPoly.add O1 (nkFlR 0 gp D1) (remP O1 PC (tot.getD 0 [])))

/-- `4θ′/(θ² − 2)` computed directly. -/
def hdir : GPoly (LC 1) :=
  remP O1 PC (GPoly.mul O1 (GPoly.smul O1 (O1.natCast 4) dθP)
    ((invModC O1 PC [O1.neg (O1.natCast 2), zer, onec]).getD []))

#guard (remP O1 PC (GPoly.sub O1 (GPoly.sub O1 flN (nkFlR 0 gp D1)) hdir)).all O1.isZero
#guard logCertN Fc ks 0 Pp μ2 flN (nkFlR 0 gp D1) logs dθP wθ
#guard GPoly.squarefreeCheck (MO Fc ks 0) D1
#guard resCert Fc ks 0 Pp gp D1 1 gp
-- (about 20 s)
#guard exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) PC
  (nkRest Fc ks 0 (nkFlR 0 gp D1) (nkTau Fc ks 0 3 (nkFlR 0 gp D1) sC)) = some false

end Curves.MT.NKLogCertNEx
