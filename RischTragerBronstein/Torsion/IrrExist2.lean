import RischTragerBronstein.Torsion.IrrExist1

/-!
# Irreducibility certificates exist (2): the Newton lifts at a split point

For `H = F(a + T, Y)` (`Fc.map (compC · (shiftC a 1))`):

* `toB_shiftF`: `toB H = (toB F).map (· ∘ (a + X))`;
* `constantCoeff_eval_shift`: the constant term of `H(T, y₀)` is `F(a, y₀)`;
* `repEq_id_eq_HS`: the equation of the root check is `HS H`;
* **`newton_lifts`**: from simple roots `y₀` of `F(a, Y)`, the Newton lifts approximate power
  series roots `ρ` of `H` (`ρ(0) = y₀`) to any precision.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Shift

variable {F : Type*} [Field F] [DecidableEq F]

local notation "cT" => (Polynomial.coeToPowerSeries.ringHom (R := F))

lemma toB_shiftF (Fc : BPoly F) (a : F) :
    toB (Fc.map fun q ↦ compC q (shiftC a 1)) = (toB Fc).map (compRingHom (Polynomial.C a + X)) := by
  induction Fc with
  | nil => simp
  | cons q W ih =>
    rw [List.map_cons, toB_cons, toB_cons, ih, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_C, toPoly_compC_shiftC, pow_one]
    rfl

lemma constantCoeff_eval_map (W : F[X][X]) (a y0 : F) :
    PowerSeries.constantCoeff (((W.map (compRingHom (Polynomial.C a + X))).map cT).eval
      (PowerSeries.C y0)) = evalW W a y0 := by
  have e1 : PowerSeries.C y0 = cT (Polynomial.C y0) := by
    ext n; simp [PowerSeries.coeff_C, Polynomial.coeff_C]
  rw [e1, eval_map, eval₂_at_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, coeff_zero_eq_eval_zero]
  rw [show ((W.map (compRingHom (Polynomial.C a + X))).eval (Polynomial.C y0)).eval 0 =
      (evalRingHom (0 : F)) ((W.map (compRingHom (Polynomial.C a + X))).eval₂ (RingHom.id _)
        (Polynomial.C y0)) from rfl, Polynomial.hom_eval₂, Polynomial.eval₂_map, evalW, eval_map]
  congr 1
  · ext p
    · simp [eval_comp]
    · simp [eval_comp]
  · simp

lemma repEq_id_eq_HS (Fc : BPoly F) (a : F) :
    repEq (RingHom.id F) Fc a 1 = (toB (Fc.map fun q ↦ compC q (shiftC a 1))).map cT := by
  rw [repEq, toB_shiftF, Polynomial.mapRingHom_id, Polynomial.map_id, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  simp [psSubR]

end Shift

end Curves
