import RischTragerBronstein.Mixed.NKDecidesInfVMR
import RischTragerBronstein.Mixed.NKMultiExamples

/-!
# Example: several slopes at infinity, one of them ramified

Tower `x`, `t = log x`, and `θ³ − t θ + x t = 0`: the places at infinity are `θ ≈ ±√t` (slope
`1/2`, ramification `2`) and `θ ≈ x` (slope `0`) (`multiShapeRC`: segments `(e, s) = (2, 1)` and
`(1, 0)` with residual polynomials `Z (Z² − 1)` and `−(Z − x)`), Eisenstein at `t`. The unit
`u = θ/x − 1` has norm `−1` (`(θ − x)(θ² + x θ + x² − t) = −x³`). The basis `1, θ, θ²` with shifts
`0, 1, 1` is normal at infinity; its window jets along `ρ₊ = T⁻¹ − x/2 + ⋯` (`t = T⁻²`) and
`ρ₃ = x + ⋯` are `[[1, 0, 1], [0, 1, 0], [1, −x, 0]]`, the gauge of `multi_gauge_ram` (diagonal
data `0`: `γ = 1`). By `nk_decidesInfVMR`: **`∫ θ dx` is not elementary** (`τ(θ) = 0`, the exact
part does not exist); controls: the exact parts of `θ′` and `u′/u` exist (~3 min).
-/

namespace Curves.MT.NKMultiREx
open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEx Curves.MT.NKMultiEx

/-- `θ³ − t θ + x t = 0`: `a₀ = x t`, `a₁ = −t`, `a₂ = 0`. -/
def Pp : List (GPoly (LC 0)) := [[[], px], [[], cq (-1)], []]
#guard eisCk Fc ks 0 Pp [[], one0] [[px], [cq (-1)], []] [] [cqx 1] [] [one0]
def segs : List (SegRC 0) := [(2, 1, 3, one0, [one0]), (1, 0, 1, cq (-1), [px])]
#guard multiShapeRC Fc ks 0 Pp segs
#guard nPlacesR segs = 2

/-- `u = θ/x − 1`, `v = −(θ² + x θ + x² − t)/x²` (`u v = 1`). -/
def u : List (GPoly (LC 0)) := [[cq (-1)], [cqx 1]]
def v : List (GPoly (LC 0)) := [[cq (-1), cqx2 1], [cqx (-1)], [cqx2 (-1)]]
def Us : List (List (GPoly (LC 0))) := [u]
def Vs : List (List (GPoly (LC 0))) := [v]
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

def I3 := idMatC O1 3
def Ug : List (List (LC 0)) := [[one0, [], one0], [[], one0, mx], [one0, [], []]]
def Ugi : List (List (LC 0)) := [[[], [], one0], [px, one0, mx], [one0, [], cq (-1)]]
def rr3 : List ℤ := [0, 1, 1]
def pre : List (CandIVR 0) :=
  [((Us, Vs, gls, J, H, I3, I3, rr3, Ug, Ugi), []),
   ((Us, Vs, gls, J, H, I3, I3, rr3, Ugi, Ug), [])]
def fθ : List (GPoly (LC 0)) := [[], [one0]]
def tauθ : LC 1 := nkTau Fc ks 0 3 (nkFl Fc ks 0 fθ) sM
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) tauθ
#guard elM Fc ks lv 1 tauθ 3 = some true
-- **`∫ θ dx` is not elementary** (`nk_decidesInfVMR`: `res = false`)
#guard searchIVMP Fc ks 0 ic (prdeC Fc ks lv 0) Pp (nPlacesR segs) dθM wθM sM restθ pre 0 =
  some false
def rrf : ℕ → ℤ := fun i ↦ rr3.getD i 0
-- controls: `θ′` and `u′/u` have exact parts
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Ug Ugi rrf PC I3 I3
  ((List.range 3).map fun j ↦ dθM.getD j O1.zero) gls = some true
#guard exactTLVG Fc ks 0 ic (prdeC Fc ks lv 0) [] Ug Ugi rrf PC I3 I3
  ((List.range 3).map fun j ↦ (gls.getD 0 []).getD j O1.zero) gls = some true

end Curves.MT.NKMultiREx
