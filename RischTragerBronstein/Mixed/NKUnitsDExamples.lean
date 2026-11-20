import RischTragerBronstein.Mixed.NKDecidesInfVMRD
import RischTragerBronstein.Mixed.NKMultiRExamples

/-!
# Example: a unit outside the order `Fₘ[t][θ]`

Tower `x`, `t = log x`, and `θ² = t² (t² + x)`. The function `u = (θ + t²)/t = θ/t + t` is a unit
of the integral closure (`u · (θ − t²)/(x t) = 1`, and `u² − 2t u − x = 0`), but no power of `u`
lies in `Fₘ[t][θ]` (the odd part of `uᵏ` has a nonzero coefficient `k x^{(k−2)/2}` at `θ/t`), so
the certificates `unitC` cannot see it. With denominators (`unitsCD`: `U = θ + t²`,
`V = (θ − t²)/x`, `d = t`) the split decision at infinity applies: Eisenstein at `t² + x`, one
segment of slope `2` with residual `Z² − 1`.
-/

namespace Curves.MT.NKUnitsDEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKMultiEx

/-- `θ² − t⁴ − x t² = 0`: `a₀ = −x t² − t⁴`, `a₁ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], [], mx, [], cq (-1)], []]

#guard eisCk Fc ks 0 Pp [px, [], one0] [[[], [], cq (-1)], []] [cqx 1] [cqx 1] [cqx 1]
  [[], cqx (-1/2)]

def segs : List (SegRC 0) := [(1, 2, 4, one0, [one0, cq (-1)])]

#guard multiShapeRC Fc ks 0 Pp segs
#guard nPlacesR segs = 2

/-- The unit `ũ = −u²/x` of norm `1` (so `τ(ũ′/ũ) = 0`): `U = −(θ + t²)²/x ≡ −(2t⁴ + x t² + 2t²θ)/x`,
`V = −x ((θ − t²)/x)² ≡ −(2t⁴ + x t² − 2t²θ)/x`, `d = t²`, with `U V ≡ d²` modulo `P`. -/
def U : List (GPoly (LC 0)) := [[[], [], cq (-1), [], cqx (-2)], [[], [], cqx (-2)]]
def V : List (GPoly (LC 0)) := [[[], [], cq (-1), [], cqx (-2)], [[], [], cqx 2]]
def d : GPoly (LC 0) := [[], [], one0]
/-- `w = U/d` and `w' = V/d` are roots of `Z² + (2 + 4t²/x) Z + 1`. -/
def cU : List (GPoly (LC 0)) := [[cq 2, [], cqx 4], [one0]]
def cV : List (GPoly (LC 0)) := cU
/-- `E = 1/t²`. -/
def E : GPoly (LC 1) := [(([one0] : GPoly (LC 0)), d)]

def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def dθM : GPoly (LC 1) := (dThetaC O1 PC).getD []
def wθM : GPoly (LC 1) := (invModC O1 PC (GPoly.derivX O1 PC)).getD []
/-- `g = U′/U − d′/d` (`d′/d = 2t′/t = 2/(x t)`). -/
def gl : GPoly (LC 1) := GPoly.sub O1 ((logDerC O1 PC dθM (nkFl Fc ks 0 U)).getD [])
  [(([cqx 2] : GPoly (LC 0)), ([[], one0] : GPoly (LC 0)))]
def gls : List (GPoly (LC 1)) := [gl]
def sM : List (LC 1) := traceCodes Fc ks 0 PC

#guard unitCD Fc ks 0 Pp U V d
#guard unitIC Fc ks 0 Pp U d cU
#guard unitIC Fc ks 0 Pp V d cV
#guard zeroModC Fc ks 0 Pp (GPoly.sub (MO Fc ks 1) (GPoly.mul (MO Fc ks 1) (nkFl Fc ks 0 [d]) E)
  [(MO Fc ks 1).one])
#guard logDerChkD Fc ks 0 Pp U V d gl dθM wθM
#guard gl.length ≤ Pp.length
#guard (MOr Fc ks 1).isZero (nkTau Fc ks 0 Pp.length gl sM)
#guard unitsCD Fc ks 0 Pp [U] [V] [d] [cU] [cV] [E] gls dθM wθM sM
#guard traceW Fc ks 0 Pp dθM wθM sM

def J : List ℕ := [1]
def H : List (List (LC 1)) := (gjInvO O1 1 [[(gls.getD 0 []).getD 1 O1.zero]]).getD []
#guard indepC Fc ks 0 gls J H

/-- The split gauge (Vandermonde of the residual roots `±1`) with shifts `0, 2`. -/
def Vg : List (List (LC 0)) × List (List (LC 0)) :=
  (splitGaugeS Fc ks 0 [one0, cq (-1)]).getD ([], [])
def I2 := idMatC O1 2
def rr2 : List ℤ := [0, 2]
def cand (C Ci : List (List (LC 0))) : CandIVRD 0 :=
  (((([U], [V], gls, J, H, I2, I2, rr2, C, Ci) : CandIVG 0), ([] : List (LC 0 × List (LC 0 × LC 0)))),
    [d], [cU], [cV], [E])
def pre : List (CandIVRD 0) :=
  [cand Vg.1 Vg.2, cand Vg.2 Vg.1, cand (idMatC (MO Fc ks 0) 2) (idMatC (MO Fc ks 0) 2)]

def fθ : List (GPoly (LC 0)) := [[], [one0]]
def tauθ : LC 1 := nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sM
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) tauθ
#guard elM Fc ks lv 1 tauθ 3 = some true
def rrf : ℕ → ℤ := fun i ↦ rr2.getD i 0
-- controls: `ũ′/ũ` and `θ′` have exact parts
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Vg.1 Vg.2 rrf PC I2 I2
  ((List.range 2).map fun j ↦ gl.getD j O1.zero) gls = some true
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Vg.1 Vg.2 rrf PC I2 I2
  ((List.range 2).map fun j ↦ dθM.getD j O1.zero) gls = some true
-- **`∫ θ dx` is not elementary** (`nk_decidesInfVMRD`: `res = false`)
#guard searchIVMPD Fc ks 0 ic (prdeC Fc ks lv 0) Pp (nPlacesR segs) dθM wθM sM restθ pre 0 =
  some false

end Curves.MT.NKUnitsDEx
