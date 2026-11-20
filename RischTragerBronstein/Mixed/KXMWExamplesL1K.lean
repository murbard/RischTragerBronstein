import RischTragerBronstein.Mixed.KXMWExamplesL1
import RischTragerBronstein.Mixed.KXMWDecideSK

/-!
# Example: a constant curve at level `1`

Tower `x`, `t₀ = eˣ`, `t₁ = e^{t₀}`; `θ² = t₁³ + t₁ + 1` (rational coefficients) and the integrand
`t₀ θ / (t₁ − 1)`, i.e. `∫ eˣ √(1 + e^{eˣ} + e^{3eˣ}) / (e^{eˣ} − 1) dx` (the factor `t₀` makes
the residues constant). Function-field heights over `K₀`
vanish, so `kxDecideMWS` answers `none`; `kxDecideMWSK` certifies with heights over `ℚ` and answers
**not elementary** (correct by `kxDecideMWSK_correct`).
-/

namespace Curves.MT.KXL1

open Curves Curves.LT Curves.MT CPoly

/-- `A(t₁) = t₁³ + t₁ + 1`. -/
def AK : GPoly (LC 1) := [one1, one1, zero1, one1]

def c4 : LC 1 := ([[([4], [1])]], [one0])
def c9 : LC 1 := ([[([9], [1])]], [one0])
def cm2' : LC 1 := ([[([-2], [1])]], [one0])
-- Different classes (`κ = 1`, `s = 3`): heights over `ℚ` on the twist.
#guard kxDecide Fc ks lv 1 g1 AK [g1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) = none
#guard kxDecideMWS Fc ks lv 0 g1 AK [g1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) 4 = none
#guard kxDecideMWSK Fc ks lv 0 g1 AK [g1] 0 0 [one1] [17, 19, 23] 30 (fun _ ↦ 2) 4 = some false
-- Same class: `θ² = t₁³ − t₁ + 4`, `∫ e^x √(e^{3eˣ} − e^{eˣ} + 4) / (e^{eˣ} − 1) dx`.
#guard kxDecideMWSK Fc ks lv 0 g1 [c4, m1, zero1, one1] [g1] 0 0 [one1] [17, 19, 23] 30
  (fun _ ↦ 2) 4 = some false

end Curves.MT.KXL1
