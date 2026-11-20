import RischTragerBronstein.Mixed.KEMain
import RischTragerBronstein.Mixed.KEDecides

/-!
# Examples: square roots over an exponential

`keDecide` over the tower `x`, `t = eˣ` (base curve `y = x`), `θ² = A(t)`, integrand
`B(t) θ/(tᵏ A(t)ˡ)`; each answer is correct by
`keDecide_correct`. `√(1 + eˣ)` needs the logarithmic part `log((θ − 1)/(θ + 1))` (the divisor
`P₊ − ∞` is principal); `√(1 + e³ˣ)` needs the 3-torsion of `P₊ − ∞` on the elliptic curve
`θ² = 1 + t³`; for `√(1 + eˣ + e³ˣ)` the point is not torsion and there is no antiderivative.
-/

namespace Curves.MT.KEEx

open Curves Curves.LT Curves.MT CPoly

def Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def c1 : GPoly (GFrac ℚ) := [([1], [1])]
def c0 : GPoly (GFrac ℚ) := []

/-- The tower `t₀ = eˣ`. -/
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | m + 1 => .prim (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def ps : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

#guard certC Fc ks lv 1 = true
-- `∫ √(1 + eˣ)` is elementary.
#guard keDecide Fc ks lv 0 [c1, c1] [c1] 0 0 ps 30 (fun _ ↦ 2) = some true
-- `∫ √(x + eˣ)` is not.
#guard keDecide Fc ks lv 0 [xc, c1] [c1] 0 0 ps 30 (fun _ ↦ 2) = some false
-- `∫ eˣ √(1 + eˣ)` is elementary.
#guard keDecide Fc ks lv 0 [c1, c1] [c0, c1] 0 0 ps 30 (fun _ ↦ 2) = some true
-- `∫ √(1 + eˣ) / eˣ` is elementary.
#guard keDecide Fc ks lv 0 [c1, c1] [c1] 1 0 ps 30 (fun _ ↦ 2) = some true
-- `∫ x √(1 + eˣ)` is not.
#guard keDecide Fc ks lv 0 [c1, c1] [xc] 0 0 ps 30 (fun _ ↦ 2) = some false
-- `∫ √(1 + e³ˣ)` is elementary (3-torsion).
#guard keDecide Fc ks lv 0 [c1, c0, c0, c1] [c1] 0 0 ps 30 (fun _ ↦ 2) = some true
-- `∫ √(1 + eˣ + e³ˣ)` is not (no torsion).
#guard keDecide Fc ks lv 0 [c1, c1, c0, c1] [c1] 0 0 ps 30 (fun _ ↦ 2) = some false
-- `∫ 1/√(1 + eˣ) = ∫ θ/(1 + t)` is elementary (a logarithmic part)
#guard keDecide Fc ks lv 0 [c1, c1] [c1] 0 1 ps 30 (fun _ ↦ 2) = some true
-- `∫ eˣ/√(1 + eˣ)` is elementary
#guard keDecide Fc ks lv 0 [c1, c1] [c0, c1] 0 1 ps 30 (fun _ ↦ 2) = some true
-- `∫ 1/√(x + eˣ)` is not
#guard keDecide Fc ks lv 0 [xc, c1] [c1] 0 1 ps 30 (fun _ ↦ 2) = some false

-- The decision with local torsion certificates (`keDecideL`, always answering by `ke_decided`).
#guard keDecideL Fc ks lv 0 [c1, c1] [c1] 0 0 (Sup.primesBelow 40) 40 (fun _ ↦ 2) = some true
#guard keDecideL Fc ks lv 0 [c1, c0, c0, c1] [c1] 0 0 (Sup.primesBelow 40) 40 (fun _ ↦ 2) = some true
#guard keDecideL Fc ks lv 0 [c1, c1, c0, c1] [c1] 0 0 (Sup.primesBelow 40) 40 (fun _ ↦ 2) = some false

end Curves.MT.KEEx
