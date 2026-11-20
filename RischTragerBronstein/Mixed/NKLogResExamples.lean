import RischTragerBronstein.Mixed.NKLogRes
import RischTragerBronstein.Mixed.NKLogExamples

/-!
# Example: a non-Kummer integrand with residue-free poles

Over `θ³ − θ − log x = 0` (`t = log x`), `f = (θ² − (3t/2) θ − 2/3)/(27 t² − 4)` has poles above the
ramified places `27 t² = 4`, but `B = θ² − (3t/2)θ − 2/3` vanishes at every point above them:
`B² ≡ (27t² − 4)(θ²/12 − 1/9) mod θ³ − θ − t` (`resCert`, `k = 2`), so all residues vanish.
`τ(f) = 0`, and `exactG` answers `some false`: by `nk_iffR` / `nk_decidesR`, **`∫ f` is not
elementary**.
-/

namespace Curves.MT.NKLogResEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogEx

def c0 (r : ℚ) : LC 0 := mcst Fc ks 0 r
/-- `D = 27 t² − 4`. -/
def Dc : GPoly (LC 0) := [c0 (-4), [], c0 27]
/-- `B = −2/3 − (3/2) t θ + θ²`. -/
def fpc : List (GPoly (LC 0)) := [[c0 (-2/3)], [[], c0 (-3/2)], [one0]]
/-- `U = −1/9 + θ²/12`. -/
def Uc : List (GPoly (LC 0)) := [[c0 (-1/9)], [], [c0 (1/12)]]
def flR : List (LC 1) := nkFlR 0 fpc Dc

#guard GPoly.squarefreeCheck (MO Fc ks 0) Dc
#guard resCert Fc ks 0 Pp fpc Dc 2 Uc
-- `f − τ(f)/3` is not exact (about 30 s)
#guard exactG Fc ks 0 (primSysC Fc ks 0 ic lim0) PC (nkRest Fc ks 0 flR (nkTau Fc ks 0 3 flR sC)) =
  some false

end Curves.MT.NKLogResEx
