import RischTragerBronstein.Mixed.NKExpExamples
import RischTragerBronstein.Mixed.NKExpDecideTRE

/-!
# Example: the complete exact-part search over an exponential

Tower `x`, `t = eˣ`, `θ³ + tθ = t + t²` (constant coefficients; single places above `t = 0` and
`t = ∞`). The power basis `(1, θ, θ²)` is an integral basis (the constant term `t + t²` is
Eisenstein at `t = 0`), and with the shifts `(0, 1, 2)` it is reduced at infinity
(`θ ~ t^{2/3}`); its residue matrices are `Λ₀` with eigenvalues `0, 1/3, 2/3` (`N₀ = 3`) and a
triangular `Λ∞` with eigenvalues `0, −1/3, −2/3`, made triangular in the solver's orientation by
the order-reversing permutation `C = C⁻¹`. With this precomputed candidate `searchTREP` (of
`nk_decidesTREP`) answers at bound `0`: the exact part of `∫ θ dx` does not exist (so, as
`τ(θ) = 0`, **`∫ θ dx` is not elementary**), and `∫ θ′ = θ` is found.
-/

namespace Curves.MT.NKDecidesTREEx

open Curves Curves.LT Curves.MT CPoly Tower.Sys Curves.MT.NKExEE Curves.MT.NKExpEx

/-- The order-reversing permutation. -/
def J3 : List (List ℚ) := [[0, 0, 1], [0, 1, 0], [1, 0, 0]]
/-- The power basis. -/
def Id3 : List (List (LC 1)) := [[onec, zer, zer], [zer, onec, zer], [zer, zer, onec]]

/-- The precomputed candidate. -/
def pre : List (PreTRE 0) := [(Id3, Id3, fun i ↦ (i : ℤ), 3, J3, J3)]

-- `∫ θ dx` is not elementary on `θ³ + eˣ θ = eˣ + e²ˣ`.
#guard searchTREP Fc ks 0 xc (rdeE Fc ks lv 0) PC2 (nkRest Fc ks 0 flθ (nkTau Fc ks 0 3 flθ sC2)) pre 0 =
  some false
-- `∫ θ′ = θ`.
#guard searchTREP Fc ks 0 xc (rdeE Fc ks lv 0) PC2 ((List.range 3).map fun j ↦ NKExpEx.dθ2.getD j O1.zero)
  pre 0 = some true

end Curves.MT.NKDecidesTREEx
