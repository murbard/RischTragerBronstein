import RischTragerBronstein.Mixed.KQMain
import RischTragerBronstein.Mixed.KQDecides

/-!
# Examples: square roots over a logarithm, with poles at ordinary places

`kqDecide` over the tower `x`, `t = log x` (base curve `y = x`), `θ² = A(t)`, integrand
`B(t) θ / (∏ (t − c_q) A(t)ˡ)`; each answer is correct by `kqDecide_correct`.

* `∫ √(log x)/(log x − 1)`: the residue at `log x = 1` is `x`, not a constant: not elementary;
* `∫ (1 − 2 log x)/(√(log x) (log x − x²)) = log((√(log x) − x)/(√(log x) + x))` (genus `0`,
  the pole `(x², x)` is rational over `ℚ(x)`);
* `∫ (1 − 2x²)/x² · √(log x)/(log x − x²)`: the same logarithmic part, and the remainder
  `∫ dx/(x² √(log x))` is not elementary;
* `∫ √(log³x + 1)/(x log x)`: `(0, 1)` has order `3` on `θ² = t³ + 1` (genus `1`), elementary;
* `∫ √(log³x + log x + 1)/(x log x)`: `(0, 1)` has infinite order on `θ² = t³ + t + 1`, not
  elementary.
-/

namespace Curves.MT.KQEx

open Curves Curves.LT Curves.MT CPoly

def Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def xi : GPoly (GFrac ℚ) := [([1], [0, 1])]
def x2 : GPoly (GFrac ℚ) := [([0, 0, 1], [1])]
def b4 : GPoly (GFrac ℚ) := [([1, 0, -2], [0, 0, 1])]
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def cm2 : GPoly (GFrac ℚ) := [([-2], [1])]
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
-- `∫ √(log x)/(log x − 1)` is not elementary.
#guard kqDecide Fc ks lv 0 xi [c0, c1] [c1] 0 [c1] ps 30 (fun _ ↦ 2) = some false
-- `∫ (1 − 2 log x)/(√(log x) (log x − x²))` is elementary.
#guard kqDecide Fc ks lv 0 xi [c0, c1] [c1, cm2] 1 [x2] ps 30 (fun _ ↦ 2) = some true
-- `∫ (1 − 2x²)/x² · √(log x)/(log x − x²)` is not.
#guard kqDecide Fc ks lv 0 xi [c0, c1] [b4] 0 [x2] ps 30 (fun _ ↦ 2) = some false
-- `∫ √(log³x + 1)/(x log x)` is elementary (3-torsion).
#guard kqDecide Fc ks lv 0 xi [c1, c0, c0, c1] [xi] 0 [c0] ps 30 (fun _ ↦ 2) = some true
-- `∫ √(log³x + log x + 1)/(x log x)` is not (no torsion).
#guard kqDecide Fc ks lv 0 xi [c1, c1, c0, c1] [xi] 0 [c0] ps 30 (fun _ ↦ 2) = some false

-- The decision with local torsion certificates (`kqDecideL`, always answering by `kq_decided`).
#guard kqDecideL Fc ks lv 0 xi [c0, c1] [c1, cm2] 1 [x2] (Sup.primesBelow 40) 40 (fun _ ↦ 2) = some true
#guard kqDecideL Fc ks lv 0 xi [c1, c0, c0, c1] [xi] 0 [c0] (Sup.primesBelow 40) 40 (fun _ ↦ 2) =
  some true
#guard kqDecideL Fc ks lv 0 xi [c1, c1, c0, c1] [xi] 0 [c0] (Sup.primesBelow 40) 40 (fun _ ↦ 2) =
  some false

end Curves.MT.KQEx
