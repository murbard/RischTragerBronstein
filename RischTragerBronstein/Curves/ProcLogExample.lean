import RischTragerBronstein.Curves.ProcLogDecide

/-!
# The logarithmic part on a general curve, checked by the kernel

On `y² = x`: `∫ dx / ((x − 1) √x) = ∫ y / (x (x − 1)) dx` is elementary
(`= log((y − 1)/(y + 1))`); the witness `u = (y − 1)²/(x − 1)` is verified by `witCheck` and the
remainder vanishes (`decideLog … = some true`, `decide +kernel`).
-/

open Polynomial CPoly Sup Differential IntermediateField

namespace Curves.LogExample

/-- `ℚ` with its trivial coordinates. -/
instance qCoords : EllQuad.QCoords ℚ where
  dim := 1
  coord := fun _ ↦ LinearMap.id
  bvec := fun _ ↦ 1
  repr := fun z ↦ by simp

/-- `y² = x`, `∫ y / (x (x − 1)) dx`: special points `0` (ramified) and `1`, infinity ramified. -/
def probLog : CurveProb ℚ :=
  { Fc := [[0, -1], [], [1]], n := 2, k := 1, A := [[], [1]], D := [0, -1, 1],
    pts := [(0, ⟨2, [[0, 1], [0, -1]], 8⟩),
            (1, ⟨1, [[1, 1/2, -1/8, 1/16, -5/128, 7/256, -21/1024, 33/2048],
                     [-1, -1/2, 1/8, -1/16, 5/128, -7/256, 21/1024, -33/2048]], 7⟩)],
    inf := ⟨2, [[0, 1], [0, -1]], 10⟩ }

/-- The witness `u = (y − 1)² / (x − 1) = (x + 1 − 2y)/(x − 1)`. -/
def wsLog : List (LogWit ℚ) := [⟨1, [[1, 1], [-2]], [-1, 1]⟩]

set_option maxRecDepth 100000 in
lemma run : probLog.decideLog wsLog = some true := by decide +kernel

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **`∫ √x / (x (x − 1)) dx` is elementary** (with a logarithm), decided by the general-curve
procedure with logarithmic part. -/
theorem log_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hSF : S.F = (toB probLog.Fc).map (mapRingHom (Rat.castHom Kc))) :
    HasElementaryIntegral (S.y / (S.x ^ 2 - S.x)) := by
  have := (decideLog_spec hC S hx hgen probLog (Rat.castHom Kc) hSF wsLog true run).mpr rfl
  convert this using 1
  simp [CurveData.fE, CurveData.evXY, probLog, toB, CPoly.toPoly]
  ring

end Curves.LogExample
