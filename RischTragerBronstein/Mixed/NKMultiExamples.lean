import RischTragerBronstein.Mixed.NKDecidesInfVM
import RischTragerBronstein.Mixed.NKExactExamples

/-!
# Example: several slopes at infinity

Tower `x`, `t = log x`, and `θ² − t θ + x t = 0` (coefficients involving `x`): the places at
infinity have different slopes, `θ ≈ t` and `θ ≈ x` (`multiShapeC`: segments of slopes `1` and
`0` with residual polynomials `Z (Z − 1)` and `−(Z − x)`), Eisenstein at `t`. The curve has genus
`0`; `u = θ − x` is a unit (`u (t − θ − x) = x²`), normalized to norm `1`. The basis `1, θ/t` is
normal at infinity, with values `[[1, 1], [1, 0]]` along the two roots (the gauge of
`multi_gauge`). By `nk_decidesInfVMP`: **`∫ θ dx` is not elementary** (`τ(θ)/2 = (log x)/2` is
integrable, the exact part is not); controls: the exact parts of `θ′` and `u′/u` exist.
-/

namespace Curves.MT.NKMultiEx
open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx

def px : GPoly (GFrac ℚ) := [([0, 1], [1])]
def mx : GPoly (GFrac ℚ) := [([0, -1], [1])]
def cq (q : ℚ) : GPoly (GFrac ℚ) := [([q], [1])]
def cqx (q : ℚ) : GPoly (GFrac ℚ) := [([q], [0, 1])]
def cqx2 (q : ℚ) : GPoly (GFrac ℚ) := [([q], [0, 0, 1])]
/-- `θ² − t θ + x t = 0`: `a₀ = x t`, `a₁ = −t`. -/
def Pp : List (GPoly (LC 0)) := [[[], px], [[], cq (-1)]]
-- Eisenstein at `q = t`: `a₀ = t · x`, `a₁ = t · (−1)`, `0 · t + (1/x) · x = 1`, `0 · t + 1 · 1 = 1`
#guard eisCk Fc ks 0 Pp [[], one0] [[px], [cq (-1)]] [] [cqx 1] [] [one0]
def segs : List (SegC 0) := [(1, 2, one0, [one0]), (0, 1, cq (-1), [px])]
#guard multiShapeC Fc ks 0 Pp segs

def O0 := MO Fc ks 0
def x2 : LC 0 := [([0, 0, 1], [1])]
/-- `u = θ − x`, `v = (t − θ − x)/x²` (`u v = 1`), norm `x²`. -/
def u : List (GPoly (LC 0)) := [[mx], [one0]]
def v : List (GPoly (LC 0)) := [[cqx (-1), cqx2 1], [cqx2 (-1)]]
def Us : List (List (GPoly (LC 0))) := [(thPowS Fc ks 0 Pp u 2).map (GPoly.smul O0 (O0.inv x2))]
def Vs : List (List (GPoly (LC 0))) := [(thPowS Fc ks 0 Pp v 2).map (GPoly.smul O0 x2)]
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def dθM : GPoly (LC 1) := (dThetaC O1 PC).getD []
def wθM : GPoly (LC 1) := (invModC O1 PC (GPoly.derivX O1 PC)).getD []
def gls : List (GPoly (LC 1)) := [(logDerC O1 PC dθM (nkFl Fc ks 0 (Us.getD 0 []))).getD []]
def J : List ℕ := [1]
def H : List (List (LC 1)) := (gjInvO O1 1 [[(gls.getD 0 []).getD 1 O1.zero]]).getD []
def sM : List (LC 1) := traceCodes Fc ks 0 PC
#guard unitsC Fc ks 0 Pp Us Vs gls dθM wθM sM
#guard indepC Fc ks 0 gls J H
#guard traceW Fc ks 0 Pp dθM wθM sM
def mone0 : LC 0 := [([-1], [1])]
def I1 := idMatC O1 2
def Cg : List (List (LC 0)) := [[one0, one0], [one0, []]]
def Cgi : List (List (LC 0)) := [[[], one0], [one0, mone0]]
def pre : List (CandIVG 0) :=
  [(Us, Vs, gls, J, H, I1, I1, [0, 1], Cg, Cgi),
   (Us, Vs, gls, J, H, I1, I1, [0, 1], Cgi, Cg),
   (Us, Vs, gls, J, H, I1, I1, [0, 1], idMatC O0 2, idMatC O0 2)]
def fθ : List (GPoly (LC 0)) := [[], [one0]]
def tauθ : LC 1 := nkTau Fc ks 0 2 (nkFl Fc ks 0 fθ) sM
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) tauθ
#guard elM Fc ks lv 1 tauθ 3 = some true
-- **`∫ θ dx` is not elementary** (`nk_decidesInfVMP`: `res = false`)
#guard searchIVGP Fc ks 0 ic (prdeC Fc ks lv 0) Pp dθM wθM sM restθ pre 0 = some false
def rr : ℕ → ℤ := fun i ↦ if i = 1 then 1 else 0
-- controls: `θ′` and `u′/u` have exact parts
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi rr PC I1 I1
  ((List.range 2).map fun j ↦ dθM.getD j O1.zero) gls = some true
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Cg Cgi rr PC I1 I1
  ((List.range 2).map fun j ↦ (gls.getD 0 []).getD j O1.zero) gls = some true

end Curves.MT.NKMultiEx
