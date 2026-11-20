import RischTragerBronstein.Mixed.NKLogTExamples
import RischTragerBronstein.Mixed.NKDecidesTR

/-!
# Example: the complete exact-part search over a logarithm

Tower `x`, `t = log x`, `θ³ + tθ = t²` (constant coefficients, single place at infinity). The
search `searchTRP` of `nk_decidesTRP`, with the basis normal at infinity of the shape as
precomputed candidate (shifts `0`), answers at once (bound `0`, no enumeration): the exact part of
`∫ θ dx` does not exist (so, as `τ(θ) = 0`, `∫ θ dx` is not elementary), and `∫ θ′ = θ` is found.
-/

namespace Curves.MT.NKDecidesTREx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEx Curves.MT.NKLogTEx

/-- The precomputed candidate: the basis normal at infinity, shifts `0`. -/
def pre : List (List (List (LC 1)) × List (List (LC 1)) × (ℕ → ℤ)) :=
  [(nkTc Fc ks 0 Pp, nkTi Fc ks 0 Pp, fun _ ↦ 0)]

#guard searchTRP Fc ks 0 ic lim0 PC (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC)) pre 0 = some false
#guard searchTRP Fc ks 0 ic lim0 PC ((List.range 3).map fun j ↦ dθ'.getD j O1.zero) pre 0 = some true

end Curves.MT.NKDecidesTREx
