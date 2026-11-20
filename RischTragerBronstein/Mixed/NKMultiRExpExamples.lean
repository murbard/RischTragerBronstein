import RischTragerBronstein.Mixed.NKDecidesETInfVMR
import RischTragerBronstein.Mixed.NKRamCandExamples

/-!
# Example: several slopes at infinity, one ramified, over an exponential level

Tower `x`, `t = eˣ`, and `θ³ − t θ + x t = 0`: at infinity the segments `(e, s) = (2, 1)`
(`θ ≈ ±√t`) and `(1, 0)` (`θ ≈ x`) (`multiShapeRC`), above `t = 0` a single place (`nkShape0`:
`θ³ ≈ −x t`), Eisenstein at `t`. The unit `u = θ/x − 1` has norm `−1`. The basis `1, θ, θ²` with
shifts `0, 1, 1` has the window jets `[[1, 0, 1], [0, 1, 0], [1, −x, 0]]` at infinity (the gauge
of `multi_gauge_ramE`, diagonal data `(0, 0, 1), (−1/2, 1/2, 1), (0, 0, 1)`: `−(1/2) a′` on the
window `T¹` of the ramified place); at `t = 0` the permutation gauges of `ramCandsE`. By
`nk_decidesETInfVMR`: **`∫ θ dx` is not elementary**; control: `∫ θ′` is found elementary (~1 min).
-/

namespace Curves.MT.NKMultiREE
open Curves Curves.LT Curves.MT CPoly Tower.Sys Tower.NestX Curves.MT.NKExEE
  Curves.MT.NKInfRVExpEx

/-- `θ³ − t θ + x t = 0`: `a₀ = x t`, `a₁ = −t`, `a₂ = 0`. -/
def Pp3 : List (GPoly (LC 0)) := [[[], px], [[], cq (-1)], []]
#guard eisCk Fc ks 0 Pp3 [[], one0] [[px], [cq (-1)], []] [] [cqx 1] [] [one0]
#guard nkShape0 Fc ks 0 Pp3
def segs : List (SegRC 0) := [(2, 1, 3, one0, [one0]), (1, 0, 1, cq (-1), [px])]
#guard multiShapeRC Fc ks 0 Pp3 segs

def O0 := MO Fc ks 0
/-- `u = θ/x − 1`, `v = −(θ² + x θ + x² − t)/x²` (`u v = 1`). -/
def u : List (GPoly (LC 0)) := [[cq (-1)], [cqx 1]]
def v : List (GPoly (LC 0)) := [[cq (-1), cqx2 1], [cqx (-1)], [cqx2 (-1)]]
def Us3 : List (List (GPoly (LC 0))) := [u]
def Vs3 : List (List (GPoly (LC 0))) := [v]
def PC3 : GPoly (LC 1) := nkPC Fc ks 0 Pp3
def dθM : GPoly (LC 1) := (dThetaC O1 PC3).getD []
def wθM : GPoly (LC 1) := (invModC O1 PC3 (GPoly.derivX O1 PC3)).getD []
def gls3 : List (GPoly (LC 1)) := [(logDerC O1 PC3 dθM (nkFl Fc ks 0 (Us3.getD 0 []))).getD []]
def J3 : List ℕ := [1]
def H3 : List (List (LC 1)) := (gjInvO O1 1 [[(gls3.getD 0 []).getD 1 O1.zero]]).getD []
def sM : List (LC 1) := traceCodes Fc ks 0 PC3
#guard unitsC Fc ks 0 Pp3 Us3 Vs3 gls3 dθM wθM sM
#guard indepC Fc ks 0 gls3 J3 H3
#guard traceW Fc ks 0 Pp3 dθM wθM sM

def I3 := idMatC O1 3
def Ug : List (List (LC 0)) := [[one0, [], one0], [[], one0, mx], [one0, [], []]]
def Ugi : List (List (LC 0)) := [[[], [], one0], [px, one0, mx], [one0, [], cq (-1)]]
def rl : List ℤ := [0, 1, 1]
def dgI : List (ℚ × ℚ × LC 0) := [(0, 0, one0), (-1/2, 1/2, one0), (0, 0, one0)]
/-- The gauges at `t = 0` (`d₀ = 1`, `c₀ = x`), as in `ramCandsE`. -/
def τ : List ℕ := (List.range 3).insertionSort fun i j ↦ j % 3 ≤ i % 3
def zs : List (List ℕ) :=
  [τ, (List.range 3).map fun a ↦ τ.idxOf a, List.range 3, (List.range 3).reverse]
def pre : List (CandETVR 0) :=
  (zs.flatMap fun σ ↦
    let σi := (List.range 3).map fun a ↦ σ.idxOf a
    [(permMatC O0 3 σ, permMatC O0 3 σi, σ), (permMatC O0 3 σi, permMatC O0 3 σ, σ)]).map fun c ↦
    ((Us3, Vs3, gls3, J3, H3, I3, I3, rl, Ug, Ugi, c.1, c.2.1,
      (List.range 3).map fun a ↦
        let j := c.2.2.getD a 0
        (((j % 3 : ℕ) : ℚ) / 3, ((j : ℕ) : ℚ) / 3, px)), dgI)
def fθ : List (GPoly (LC 0)) := [[], [one0]]
def tauθ : LC 1 := nkTau Fc ks 0 3 (nkFl Fc ks 0 fθ) sM
def restθ : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fθ) tauθ
#guard elM Fc ks lv 1 tauθ 3 = some true
-- **`∫ θ dx` is not elementary** (`nk_decidesETInfVMR`: `res = false`)
#guard searchETVMP Fc ks 0 xc (prdeC Fc ks lv 0) Pp3 (nPlacesR segs) dθM wθM sM restθ pre 0 =
  some false
/-- `θ′` in the basis `1, θ, θ²` (control: `∫ θ′` is elementary). -/
def dθ3 : List (LC 1) := (List.range 3).map fun j ↦ dθM.getD j O1.zero
#guard searchETVMP Fc ks 0 xc (prdeC Fc ks lv 0) Pp3 (nPlacesR segs) dθM wθM sM dθ3 pre 0 =
  some true

end Curves.MT.NKMultiREE
