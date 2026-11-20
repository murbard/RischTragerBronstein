import RischTragerBronstein.Mixed.FrontRootPole
import RischTragerBronstein.Mixed.KYExamples

/-!
# Examples: `n`-th roots with poles over a logarithm, from expressions

Over the line `y = x`, `frontRootP M n j zN gs a e₁ cs` decides `∫ e₁ θʲ`, `θⁿ = a`, with the
poles `cs` (each answer correct by `frontRootP_sound`), here with the number field
`ℚ(ζ₃) = ℚ[X]/(X² + X + 1)`, `ζ = X`.
-/

namespace Curves.MT.FrontRootPoleEx

open Curves Curves.MT Curves.MT.Front Curves.MT.KYEx EE

instance (m : ℕ) : Fact (Irreducible (CPoly.toPoly (liftQ Fc m M3))) := ⟨M3_irr m⟩

-- `∫ ∛(log x)/(log x − 1)` is not elementary: the residue at `log x = 1` is not constant.
#guard frontRootP Fc M3 3 1 [0, 1] [[1]] (log x) (inv (add (log x) (cst (-1)))) [cst 1] ps 30
  (fun _ ↦ 2) = some false

-- `∫ ∛(log x)/(x (log x − 1))` is elementary (`u = log x`: `∫ ∛u/(u − 1) du`).
#guard frontRootP Fc M3 3 1 [0, 1] [[1]] (log x) (inv (mul x (add (log x) (cst (-1))))) [cst 1]
  ps 30 (fun _ ↦ 2) = some true

end Curves.MT.FrontRootPoleEx
