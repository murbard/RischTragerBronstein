import RischTragerBronstein.Curves.ProcLogSearch
import RischTragerBronstein.Curves.ProcLogExample
import RischTragerBronstein.Curves.ProcLogExampleI

/-!
# The automatic decision (searched log witnesses), checked by the kernel

The same two integrals as `ProcLogExample` / `ProcLogExampleI`, now without supplying the
logarithm: `decideAuto` searches the witness (multiplier `≤ B`, `x`-degree `≤ Ew`), `decideLog`
verifies it, and `decideAuto_spec` turns the answer into a theorem.
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.AutoExample

open LogExample LogExampleI RFExampleI

set_option maxRecDepth 200000 in
lemma runLog : probLog.decideAuto 2 3 = some true := by decide +kernel

set_option maxRecDepth 200000 in
lemma runEllLog : probEllLog.decideAuto 1 3 = some false := by decide +kernel

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- `∫ √x/(x (x − 1)) dx` is elementary — logarithm found automatically. -/
theorem log_elementary_auto (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probLog.Fc).map (mapRingHom (Rat.castHom Kc))) :
    HasElementaryIntegral ((S.fE probLog (Rat.castHom Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) :=
  (decideAuto_spec hC S hx hgen probLog (Rat.castHom Kc) hSF 2 3 true runLog).mpr rfl

/-- `∫ (1/y + 1/(x − 9)) dx` on `y² = x (x − 9)(x − 25)` is not elementary — logarithm found
automatically, remainder not exact. -/
theorem ell_log_not_elementary_auto (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E)
    (hx : S.x′ = 1) (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probEllLog.Fc).map (mapRingHom (ιI (Kc := Kc)))) :
    ¬ HasElementaryIntegral ((S.fE probEllLog ιI : Kc⟮S.x⟯⟮S.y⟯) : E) := fun h ↦
  Bool.false_ne_true ((decideAuto_spec hC S hx hgen probEllLog ιI hSF 1 3 false runEllLog).mp h)

end Curves.AutoExample
