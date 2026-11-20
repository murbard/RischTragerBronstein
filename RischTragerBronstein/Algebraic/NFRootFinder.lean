import RischTragerBronstein.Algebraic.NFRoots
import RischTragerBronstein.Computable.SquarefreePart
import RischTragerBronstein.Curves.AutoPuiseux

/-!
# A complete root finder in a number field

`rfNF f P`: all roots of `P` in `K = ℚ[θ]/(f)` (Trager's norm method on the squarefree part,
`rootsIn`), or `none` if some root of `P` (counted with multiplicity) is not in `K`. This is the
`RootFinder` used by `puiseuxAt`.
-/

open Polynomial CPoly

namespace NFC

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

/-- **All roots in `K`**, or `none` when `P` does not split over `K`. -/
def rfNF : Curves.RootFinder (NF f) := fun P ↦
  let P := trim P
  if isZero P then none else
  match rootsIn f (sqfreePart P) with
  | none => none
  | some rs =>
    let rs := rs.dedup
    if (rs.map fun r ↦ Curves.multAt P r (P.length + 1) P).sum + 1 = P.length then some rs
    else none

end NFC
