import RischTragerBronstein.Mixed.KXMain
import RischTragerBronstein.Mixed.KXDecides

/-!
# Examples: square roots over an exponential, with poles at ordinary places

`kxDecide` over the tower `x`, `t = eˣ`; each answer is correct by `kxDecide_correct`.
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly

def Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def c0 : GPoly (GFrac ℚ) := []
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def c2 : GPoly (GFrac ℚ) := [([2], [1])]
def c3 : GPoly (GFrac ℚ) := [([3], [1])]

/-- The tower `t₀ = eˣ`. -/
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

-- `∫ √(1 + eˣ)/(eˣ − 1)` is elementary (genus 0; `P₊ − ∞` principal).
#guard kxDecide Fc ks lv 0 xc [c1, c1] [c1] 0 0 [c1] ps 30 (fun _ ↦ 2) = some true
-- `∫ √(1 + eˣ)/(eˣ (eˣ − 1))` is elementary.
#guard kxDecide Fc ks lv 0 xc [c1, c1] [c1] 1 0 [c1] ps 30 (fun _ ↦ 2) = some true
-- `∫ 1/((eˣ − 1) √(1 + eˣ))` is elementary.
#guard kxDecide Fc ks lv 0 xc [c1, c1] [c1] 0 1 [c1] ps 30 (fun _ ↦ 2) = some true
-- `∫ √(1 + eˣ)/((eˣ − 1)(eˣ − 3))` is elementary (residues in the classes `ℚ√2` and `ℚ`).
#guard kxDecide Fc ks lv 0 xc [c1, c1] [c1] 0 0 [c1, c3] ps 30 (fun _ ↦ 2) = some true
-- `∫ √(2 + eˣ)/(eˣ − 1)` is elementary (`A(0) = 2`: the point `P₊` needs `√2`).
#guard kxDecide Fc ks lv 0 xc [c2, c1] [c1] 0 0 [c1] ps 30 (fun _ ↦ 2) = some true
-- `∫ (eˣ(x − 2) − x)/((eˣ + x − x²) √(x + eˣ))` is elementary
-- (`= log((√(x + eˣ) − x)/(√(x + eˣ) + x))`; `A(0) = x` is not a constant times a square).
#guard kxDecide Fc ks lv 0 xc [xc, c1] [[([0, -1], [1])], [([-2, 1], [1])]] 0 1
  [[([0, -1, 1], [1])]] ps 30 (fun _ ↦ 2) = some true
-- `∫ √(x + eˣ)/(eˣ − 1)` is not (the residue `√(x + 1)` is not constant).
#guard kxDecide Fc ks lv 0 xc [xc, c1] [c1] 0 0 [c1] ps 30 (fun _ ↦ 2) = some false
-- `∫ √(1 + e³ˣ)/(eˣ − 1)` is not (the point `(1, √2)` is not torsion on `θ² = t³ + 1`,
-- while `P₊ = (0, 1)` is `3`-torsion).
#guard kxDecide Fc ks lv 0 xc [c1, c0, c0, c1] [c1] 0 0 [c1] ps 30 (fun _ ↦ 2) = some false
-- `∫ √(1 + e³ˣ)/(eˣ − 2)` is not (all points torsion, the Risch equation has no solution).
#guard kxDecide Fc ks lv 0 xc [c1, c0, c0, c1] [c1] 0 0 [c2] ps 30 (fun _ ↦ 2) = some false
-- `∫ √(1 + eˣ + e³ˣ)/(eˣ − 1)`: neither `P₊ − ∞` nor the class of the pole is torsion; whether
-- a combination is (a Mordell–Weil relation) is not decided.
#guard kxDecide Fc ks lv 0 xc [c1, c1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none

-- The decision with local torsion certificates (`kxDecideL`, answering outside the
-- Mordell–Weil case by `kx_decided`).
#guard kxDecideL Fc ks lv 0 xc [c1, c1] [c1] 0 0 [c1, c3] (Sup.primesBelow 40) 40 (fun _ ↦ 2) =
  some true
#guard kxDecideL Fc ks lv 0 xc [c1, c0, c0, c1] [c1] 0 0 [c2] (Sup.primesBelow 40) 40 (fun _ ↦ 2) =
  some false

end Curves.MT.KXEx
