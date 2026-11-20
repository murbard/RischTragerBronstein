import RischTragerBronstein.Mixed.CurveRdeComplete

/-!
# Curve codes under maps of the ambient field

**`sem_cM_map`**: if `j : E → L` maps the curve `S` (over `Kc`) to the curve `SL` (over `Cc`,
`SL.x = j S.x`, `SL.y = j S.y`, both with the same equation over `ℚ`), then every curve code has
value `j (value)`: the models agree.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Map

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable {Cc L : Type*} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc] [Differential L]
variable [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))
  (hCc : ∀ c : Cc, c′ = 0) (SL : CurveData Cc L) (hxL : SL.x′ = 1)
  (hSFL : SL.F = (toB Fc).map (mapRingHom (algebraMap ℚ Cc)))
  (j : E →+* L) (hjx : SL.x = j S.x) (hjy : SL.y = j S.y)

include hjx in
lemma sem_xM_map (q : GFrac ℚ) :
    (xM hCc SL hxL).sem q = j ((xM hC S hx).sem q) := by
  have hQ : ∀ P : ℚ[X], aeval SL.x (P.map (algebraMap ℚ Cc)) =
      j (aeval S.x (P.map (algebraMap ℚ Kc))) := fun P ↦ by
    rw [aeval_map_algebraMap, aeval_map_algebraMap, hjx]
    rw [aeval_def, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_rat _ _
  rw [sem_xModel, sem_xModel, hQ, hQ, map_div₀]

include hjx hjy in
/-- **Codes have compatible values.** -/
lemma sem_cM_map (a : GPoly (GFrac ℚ)) :
    (cM hCc SL hxL Fc hSFL).sem a = j ((cM hC S hx Fc hSF).sem a) := by
  rw [sem_cM, sem_cM]
  induction a with
  | nil => simp
  | cons q a ih =>
    rw [GPoly.toPoly_cons, GPoly.toPoly_cons, eval_add, eval_add, eval_C, eval_C, eval_mul,
      eval_mul, eval_X, eval_X, ih, sem_xM_map hC S hx hCc SL hxL j hjx, hjy, map_add, map_mul]

end Map

end Curves
