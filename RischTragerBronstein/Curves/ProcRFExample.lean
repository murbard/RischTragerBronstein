import RischTragerBronstein.Curves.ProcRFDecide

/-!
# The residue-free decision on a general curve, checked by the kernel

`decideRF` runs in the kernel (`decide +kernel`); with `decideRF_spec` its answer is a theorem.
Here, on any curve `y² = x` (given as `CurveData`, i.e. with `F = Y² − x` irreducible):
`∫ y/x dx` is elementary.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.RFExample

/-- `y² = x`, `∫ y / x dx`; special point `0` and infinity, both ramified (`N = 2`). -/
def probSqrt : CurveProb ℚ :=
  { Fc := [[0, -1], [], [1]], n := 2, k := 1, A := [[], [1]], D := [0, 1],
    pts := [(0, ⟨2, [[0, 1], [0, -1]], 10⟩)], inf := ⟨2, [[0, 1], [0, -1]], 10⟩ }

set_option maxRecDepth 100000 in
lemma run : probSqrt.decideRF = some true := by decide +kernel

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **`∫ √x / x dx` is elementary** on any curve `y² = x`, decided by the general-curve
procedure. -/
theorem sqrt_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probSqrt.Fc).map (mapRingHom (Rat.castHom Kc))) :
    HasElementaryIntegral (S.y / S.x) := by
  have := (decideRF_spec hC S hx hgen probSqrt (Rat.castHom Kc) hSF true run).mpr rfl
  convert this using 1
  simp [CurveData.fE, CurveData.evXY, probSqrt, toB, CPoly.toPoly]

end Curves.RFExample
