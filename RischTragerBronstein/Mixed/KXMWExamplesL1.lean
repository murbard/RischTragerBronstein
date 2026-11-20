import RischTragerBronstein.Mixed.KXExamples
import RischTragerBronstein.Mixed.KXMWDecideS

/-!
# Example: the Mordell–Weil exception at level `1`

Tower `x`, `t₀ = eˣ`, `t₁ = e^{t₀}`; `θ² = t₁³ − t₁ + t₀²` (a curve over `F₁ = Cc(x, t₀)`) and the
integrand `θ / (t₁ − 1)`, i.e. `∫ √(e^{3eˣ} − e^{eˣ} + e^{2x}) / (e^{eˣ} − 1) dx`. `kxDecide` at level
`1` answers `none` (the points `(1, t₀)` and `(0, t₀)` are both non-torsion); `kxDecideMWS` finds a
height certificate over `K₀` (`ℚ(x)`) on `F₁ = F₀(t₀)` and answers **not elementary**
(correct by `kxDecideMWS_correct`).
-/

namespace Curves.MT.KXL1

open Curves Curves.LT Curves.MT CPoly

abbrev Fc : Sup.BPoly ℚ := [[0, -1], [1]]
instance : Fact (Irreducible (toPoly (fKc Fc))) := ⟨fKc_irr_linear [0, -1]⟩
def xc : GPoly (GFrac ℚ) := [([0, 1], [1])]
def one0 : GPoly (GFrac ℚ) := [([1], [1])]
/-- `t₀` as a level-`1` code. -/
def g1 : LC 1 := ([[], one0], [one0])
/-- The tower `t₀ = eˣ`, `t₁ = e^{t₀}`. -/
def ks : (m : ℕ) → KindC m
  | 0 => .exp xc
  | 1 => .exp g1
  | m + 2 => .prim (([] : GPoly (LC (m + 1))), ([] : GPoly (LC (m + 1))))
def lv : (m : ℕ) → LC m
  | 0 => xc
  | m + 1 => (([] : GPoly (LC m)), ([] : GPoly (LC m)))
def one1 : LC 1 := ([one0], [one0])
def zero1 : LC 1 := ([], [one0])
def t0sq : LC 1 := ([[], [], one0], [one0])
def m1 : LC 1 := ([[([-1], [1])]], [one0])
/-- `A(t₁) = t₁³ − t₁ + t₀²`. -/
def A1 : GPoly (LC 1) := [t0sq, m1, zero1, one1]

#guard certC Fc ks lv 2 = true
#guard kxDecide Fc ks lv 1 g1 A1 [one1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) = none
#guard kxDecideMWS Fc ks lv 0 g1 A1 [one1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) 3 = some false

/-- `2t₀²`. -/
def t0sq2 : LC 1 := ([[], [], [([2], [1])]], [one0])
/-- `−(t₀² + 1)`. -/
def cm2 : LC 1 := ([[([-1], [1])], [], [([-1], [1])]], [one0])
/-- `A(t₁) = t₁³ − (t₀² + 1) t₁ + 2t₀²`: the pole gives `(1, t₀)` (class `1`), `κ = 2`. -/
def A3 : GPoly (LC 1) := [t0sq2, cm2, zero1, one1]

-- Different classes at level `1`: conjugation over `K₀(√2)` and a one-point certificate
-- (`grp_of_chkCS`): `∫ √(e^{3eˣ} − (e^{2x} + 1) e^{eˣ} + 2e^{2x}) / (e^{eˣ} − 1) dx` is not elementary.
#guard kxDecide Fc ks lv 1 g1 A3 [one1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) = none
#guard kxDecideMWS Fc ks lv 0 g1 A3 [one1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) 3 = some false

end Curves.MT.KXL1
