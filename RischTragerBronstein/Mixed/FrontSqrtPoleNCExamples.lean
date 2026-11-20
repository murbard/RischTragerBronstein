import RischTragerBronstein.Mixed.FrontSqrtPoleAccepted

/-!
# Pole expressions that need the cubic Mordell–Weil branches

Dependent classes over `eˣ` give both answers. A non-constant cubic over `e^(eˣ)` is rejected
by the automatic search at its first stage, using a Manin certificate.
-/

namespace Curves.MT.FrontSqrtPoleNCEx

open Curves.MT.Front EE

instance : Fact (Irreducible (CPoly.toPoly (fKc [[0, -1], [1]]))) :=
  ⟨fKc_irr_linear [0, -1]⟩

private def t : EE := exp x
private def a : EE := add (sub (pow t 3) t) (cst 1)
private def eNeg : EE := inv (sub t (cst 1))
private def ePos : EE := div (add (add (pow t 2) (mul (cst 3) t)) (cst (-1)))
  (mul (cst 2) (mul (sub t (cst 1)) a))

-- The completeness check accepts both possible answers; it does not test integrability.
#guard frontSqrtPCubicCheck [0, -1] (spE a eNeg [cst 1]) a eNeg [cst 1] = true
#guard frontSqrtPCubicCheck [0, -1] (spE a ePos [cst 1]) a ePos [cst 1] = true

#guard frontSqrtPNCE [0, -1] (spE a eNeg [cst 1]) a eNeg [cst 1]
  [17, 19, 23] 30 (fun _ ↦ 2) 4 0 = some false

#guard frontSqrtPNCE [0, -1] (spE a ePos [cst 1]) a ePos [cst 1]
  [17, 19, 23] 30 (fun _ ↦ 2) 4 0 = some true

private def tt : EE := exp t
private def aa : EE := add (sub (pow tt 3) tt) (pow t 2)
private def ee : EE := inv (sub tt (cst 1))

#guard frontSqrtPCubicCheck [0, -1] (spE aa ee [cst 1]) aa ee [cst 1] = true

-- `∫ √(e^(3eˣ) − e^(eˣ) + e^(2x)) / (e^(eˣ) − 1) dx` is not elementary.
#guard frontSqrtPAuto [0, -1] aa ee [cst 1] 1 = some false

-- Uncovered degree and missing pole data fail the completeness check.
private def a5 : EE := add (sub (pow t 5) t) (cst 1)
#guard frontSqrtPCubicCheck [0, -1] (spE a5 eNeg [cst 1]) a5 eNeg [cst 1] = false
#guard frontSqrtPCubicCheck [0, -1] (spE a eNeg []) a eNeg [] = false

-- The check requires an exponential top level, even for a cubic radicand.
private def u : EE := log x
private def aLog : EE := add (sub (pow u 3) u) (cst 1)
private def eLog : EE := inv (sub u (cst 1))
#guard frontSqrtPCubicCheck [0, -1] (spE aLog eLog [cst 1]) aLog eLog [cst 1] = false

end Curves.MT.FrontSqrtPoleNCEx
