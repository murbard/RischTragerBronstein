import RischTragerBronstein.Mixed.NKExact
import RischTragerBronstein.Mixed.MTAlg

/-!
# Examples: the exact part over a non-Kummer extension of a logarithm

Tower `x`, `t = log x`, and `θ` with `θ³ − θ − t = 0` (not a radical extension). By
`exactC_correct` (the powers `1, θ, θ²` are independent over `ℚ(x, t)` since `Y³ − Y − t` is
irreducible): `θ′` has an antiderivative in `ℚ(x, t, θ)` (namely `θ`), and `θ` has none there.
-/

namespace Curves.MT.NKExEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def ic : GPoly (GFrac ℚ) := [([1], [0, 1])]
def one0 : GPoly (GFrac ℚ) := [([1], [1])]
def ks : (m : ℕ) → KindC m
  | 0 => .prim ic
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lim0 : List (LC 0) → List (List ℚ × LC 0) := fun ws ↦ paramLimC Fc ks lv 0 ws
def O1 := MOr Fc ks 1
def tC : LC 1 := (([[], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def mone : LC 1 := (([[([-1], [1])]] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def zer : LC 1 := (([] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def onec : LC 1 := (([one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- `Y³ − Y − t`. -/
def P : GPoly (LC 1) := [O1.neg tC, mone, zer, onec]
def dθ : GPoly (LC 1) := (dThetaC O1 P).getD []

-- `∫ θ′ = θ` (about 20 s).
#guard exactC Fc ks 0 ic lim0 P ((List.range 3).map fun j ↦ dθ.getD j O1.zero) = some true
-- `∫ θ` is not in `ℚ(x, log x, θ)` (about 20 s).
#guard exactC Fc ks 0 ic lim0 P [zer, onec, zer] = some false

end Curves.MT.NKExEx

/-!
Over an exponential: `t = eˣ`, `θ³ − θ − t = 0`. The derivation matrix tends to `Λ = ` a rational
upper triangular matrix at infinity (Puiseux exponents `0, 1/3, 2/3`) and vanishes at `t = 0`:
`exactCT` (`exactCT_correct`) finds `∫ θ′ = θ` and proves `∫ θ ∉ ℚ(x, eˣ, θ)`.
-/

namespace Curves.MT.NKExEE

open Curves Curves.LT Curves.MT CPoly Tower.Sys

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def one0 : GPoly (GFrac ℚ) := [([1], [1])]
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def rde0 : LC 0 → List (LC 0) → List (List ℚ × LC 0) := fun c ws ↦ prdeC Fc ks lv 0 ⟨c, []⟩ ws
def O1 := MOr Fc ks 1
def tC : LC 1 := (([[], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def mone : LC 1 := (([[([-1], [1])]] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def zer : LC 1 := (([] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def onec : LC 1 := (([one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def P : GPoly (LC 1) := [O1.neg tC, mone, zer, onec]
def dθ : GPoly (LC 1) := (dThetaC O1 P).getD []

#guard exactCT Fc ks 0 xc rde0 P ((List.range 3).map fun j ↦ dθ.getD j O1.zero) = some true
#guard exactCT Fc ks 0 xc rde0 P [zer, onec, zer] = some false

/-! `θ³ − θ² − eˣ = 0`: the matrix does not vanish at `t = 0` (a ramified place, `θ ~ √(−t)`);
its limit there is the rational triangular `Λ₀` with diagonal `0, 1/2, 0` (`zeroOK`,
`sys_den_zero_tri`). -/
def P2 : GPoly (LC 1) := [O1.neg tC, zer, mone, onec]
def dθ2 : GPoly (LC 1) := (dThetaC O1 P2).getD []

#guard exactCT Fc ks 0 xc rde0 P2 ((List.range 3).map fun j ↦ dθ2.getD j O1.zero) = some true
#guard exactCT Fc ks 0 xc rde0 P2 [zer, onec, zer] = some false

end Curves.MT.NKExEE
