import RischTragerBronstein.Mixed.KXMWExample
import RischTragerBronstein.Mixed.KXMWDecideQ
import RischTragerBronstein.Mixed.KXMWDecideT
import RischTragerBronstein.Mixed.KXMWDecideK

/-!
# Examples: `kxDecideMWQ0` (certificate search over `ℚ(√d)`)

Each answer is correct by `kxDecideMWQ0_correct`.
-/

namespace Curves.MT.KXEx

open Curves Curves.LT Curves.MT CPoly

/-- `2x²`. -/
def x22q : GPoly (GFrac ℚ) := [([0, 0, 2], [1])]

-- `∫ √(e³ˣ − eˣ + 2x²)/(x (eˣ − 1))`: residue class `ℚ√2`, `κ = 2`; not elementary
-- (certificate over `ℚ(√2)`; also a theorem with every check kernel-verified: `not_elementary_mw2`).
#guard kxDecide Fc ks lv 0 xc [x22q, cm1, c0, c1] Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) = none
#guard kxDecideMWQ0 Fc ks lv xc [x22q, cm1, c0, c1] Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 =
  some false
-- The same example through the twist (certificate over `ℚ`, `kxDecideMWT0`).
#guard kxDecideMWT0 Fc ks lv xc [x22q, cm1, c0, c1] Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 =
  some false
-- `∫ √(e³ˣ − (x²+1)eˣ + 2x²)/(x (eˣ − 1))`: `P = (1, x)` rational, `P₊ = (0, √2 x)`; different
-- classes, decided by conjugation and a one-point certificate (`kxDecideMWC0`; theorem
-- `not_elementary_mw3`).
#guard kxDecideMWC0 Fc ks lv xc [x22q, [([-1, 0, -1], [1])], c0, c1] Bmw 0 0 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 3 = some false
#guard kxDecideMWC0 Fc ks lv xc [x22q, cm1, c0, c1] Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 =
  some false
#guard kxDecideMWC0 Fc ks lv xc [c1, c1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 = none
-- Constant curve `√(1 + eˣ + e³ˣ)/(eˣ − 1)`: decided with heights over `ℚ` (`kxDecideMWK0`;
-- theorem `not_elementary_mw4`).
#guard kxDecideMWK0 Fc ks lv xc [c1, c1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 4 =
  some false
-- Constant curve, same class: `√(e³ˣ − eˣ + 4)/(eˣ − 1)` (theorem `not_elementary_mw5`), and more.
#guard kxDecideMWK0 Fc ks lv xc [[([4], [1])], cm1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 4 = some false
#guard kxDecideMWK0 Fc ks lv xc [[([9], [1])], [([-2], [1])], c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 4 = some false
-- `√(e³ˣ − eˣ + 1)/(eˣ − 1)`: `(1, 1)` and `(0, 1)` are dependent on `y² = x³ − x + 1` (a genuine
-- Mordell–Weil relation): no independence certificate, the decision stays open (`none`).
#guard kxDecideMWK0 Fc ks lv xc [[([1], [1])], cm1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30
  (fun _ ↦ 2) 3 = none
-- The rational cases are still answered (`kxDecideMW0` first).
#guard kxDecideMWQ0 Fc ks lv xc Amw Bmw 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 = some false
-- Constant curve: no certificate over `ℚ(x)`.
#guard kxDecideMWQ0 Fc ks lv xc [c1, c1, c0, c1] [c1] 0 0 [c1] [17, 19, 23] 30 (fun _ ↦ 2) 3 = none

end Curves.MT.KXEx
