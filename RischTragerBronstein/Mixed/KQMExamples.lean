import RischTragerBronstein.Mixed.KQMMain
import RischTragerBronstein.Mixed.KQMDecides

/-!
# Examples: square roots over a logarithm, residues in several classes

`kqmDecide` over the tower `x`, `t = log x`; each answer is correct by `kqmDecide_correct`.

* `∫ √(log x)/(x (log x − 1)(log x − 2))`: residues in the classes `ℚ` and `ℚ√2`, both torsion
  (genus `0`), elementary;
* `∫ √(log³x + 1)/(x log x (log x − 1))`: the class `ℚ` at `(0, 1)` is `3`-torsion, the class
  `ℚ√2` at `(1, √2)` is not torsion on `θ² = t³ + 1` (its twist `2y² = t³ + 1` has the point
  `(1, 1)` of infinite order): not elementary.
-/

namespace Curves.MT.KQMEx

open Curves Curves.LT Curves.MT CPoly

def Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def xi : GPoly (GFrac ℚ) := [([1], [0, 1])]
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def c2 : GPoly (GFrac ℚ) := [([2], [1])]
def c0 : GPoly (GFrac ℚ) := []

/-- The tower `t₀ = log x`. -/
def ks : (m : ℕ) → KindC m
  | 0 => .prim xi
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

#guard certC Fc ks lv 1 = true
-- `∫ √(log x)/(x (log x − 1)(log x − 2))` is elementary (two classes).
#guard kqmDecide Fc ks lv 0 xi [c0, c1] [xi] 0 [c1, c2] ps 30 (fun _ ↦ 2) = some true
-- `∫ √(log³x + 1)/(x log x (log x − 1))` is not (the class `√2` is not torsion).
#guard kqmDecide Fc ks lv 0 xi [c1, c0, c0, c1] [xi] 0 [c0, c1] ps 30 (fun _ ↦ 2) = some false

-- The decision with local torsion certificates (`kqmDecideL`, always answering by `kqm_decided`).
#guard kqmDecideL Fc ks lv 0 xi [c0, c1] [xi] 0 [c1, c2] (Sup.primesBelow 40) 40 (fun _ ↦ 2) =
  some true
#guard kqmDecideL Fc ks lv 0 xi [c1, c0, c0, c1] [xi] 0 [c0, c1] (Sup.primesBelow 40) 40
  (fun _ ↦ 2) = some false

end Curves.MT.KQMEx
