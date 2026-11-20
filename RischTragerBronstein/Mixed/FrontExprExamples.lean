import RischTragerBronstein.Mixed.FrontExpr

/-!
# Examples of the expression front end

Over the line `y = x` (and over the conic `y² = −x² − 1`), `frontDecide` builds the tower of the
expression, certifies it (`certC`) and runs `elM`. By `front_sound` every answer is correct for
every realization of the tower; some are turned into theorems by kernel evaluation.
-/

namespace Curves.MT.FrontEx

open Curves Curves.MT.Front EE Polynomial Differential

/-- The line `y − x = 0`. -/
def Fl : Sup.BPoly ℚ := [[0, -1], [1]]

#guard curveShape Fl
-- `∫ exp(x²)` is not elementary.
#guard frontDecide Fl (exp (pow x 2)) 3 = some false
-- `∫ x exp(x²)` is elementary.
#guard frontDecide Fl (mul x (exp (pow x 2))) 3 = some true
-- `∫ 1/log x` is not elementary.
#guard frontDecide Fl (inv (log x)) 3 = some false
-- `∫ (1 + log x)` is elementary.
#guard frontDecide Fl (add (log x) (cst 1)) 3 = some true
-- `∫ exp(x)/x` is not elementary.
#guard frontDecide Fl (div (exp x) x) 3 = some false
-- `∫ exp(exp x) exp x` is elementary.
#guard frontDecide Fl (mul (exp (exp x)) (exp x)) 3 = some true
-- `∫ log(log x)` is not elementary.
#guard frontDecide Fl (log (log x)) 3 = some false
-- `∫ 1/(x log x)` is elementary.
#guard frontDecide Fl (inv (mul x (log x))) 3 = some true
-- dependent generators (`exp x`, `exp 2x`) are not certified: no answer.
#guard frontDecide Fl (mul (exp x) (exp (add x x))) 3 = none

-- After normalization (`frontDecideN`): `∫ eˣ e^{2x} = e^{3x}/3`, `∫ e^{x + log x} = (x − 1) eˣ`,
-- `∫ log(x²)/x = log² x`, and `∫ e^{x + x²}` is not elementary.
#guard frontDecideN Fl (mul (exp x) (exp (mul (cst 2) x))) 3 = some true
#guard frontDecideN Fl (exp (add x (log x))) 3 = some true
#guard frontDecideN Fl (div (log (mul x x)) x) 3 = some true
#guard frontDecideN Fl (exp (add x (pow x 2))) 3 = some false
-- Common generators for rational multiples (`frontDecideN2`): `exp(x/2)` with `exp x`.
#guard frontDecideN Fl (mul (exp (mul (cst (1/2)) x)) (exp x)) 1 = none
#guard frontDecideN2 Fl (mul (exp (mul (cst (1/2)) x)) (exp x)) 1 = some true
#guard frontDecideN2 Fl (add (exp (mul (cst (1/2)) x)) (div (exp x) x)) 1 = some false

lemma hmonF : (Sup.toB Fl).Monic ∧ (Sup.toB Fl).natDegree = cvN Fl := by
  have e : Sup.toB Fl = X + Polynomial.C (-X) := by
    simp [Fl, Sup.toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

/-! Theorems, by kernel evaluation and `front_sound` (any realization, any constants). -/

section Thms

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc] [Differential L]
  [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **`∫ dx/log x` is not elementary** (`li`). -/
theorem inv_log_not_elementary (T : MTower Fl (ksOf Fl (inv (log x))) Cc L)
    (hn : T.n = (inv (log x)).nodesOf.length) (hgen : ∀ z : L, z ∈ T.F (inv (log x)).nodesOf.length) :
    ¬ HasElementaryIntegral (evE Fl T (inv (log x)).nodesOf (inv (log x))) := by
  have h := front_sound Fl hmonF.1 hmonF.2 (inv (log x)) 1 false (by decide +kernel) T hn hgen
  simpa using h

/-- **`∫ exp(x²) dx` is not elementary.** -/
theorem exp_sq_not_elementary (T : MTower Fl (ksOf Fl (exp (pow x 2))) Cc L)
    (hn : T.n = (exp (pow x 2)).nodesOf.length)
    (hgen : ∀ z : L, z ∈ T.F (exp (pow x 2)).nodesOf.length) :
    ¬ HasElementaryIntegral (evE Fl T (exp (pow x 2)).nodesOf (exp (pow x 2))) := by
  have h := front_sound Fl hmonF.1 hmonF.2 (exp (pow x 2)) 1 false (by decide +kernel) T hn hgen
  simpa using h

/-- **`∫ x exp(x²) dx` is elementary.** -/
theorem x_exp_sq_elementary (T : MTower Fl (ksOf Fl (mul x (exp (pow x 2)))) Cc L)
    (hn : T.n = (mul x (exp (pow x 2))).nodesOf.length)
    (hgen : ∀ z : L, z ∈ T.F (mul x (exp (pow x 2))).nodesOf.length) :
    HasElementaryIntegral (evE Fl T (mul x (exp (pow x 2))).nodesOf (mul x (exp (pow x 2)))) := by
  have h := front_sound Fl hmonF.1 hmonF.2 (mul x (exp (pow x 2))) 1 true (by decide +kernel) T hn
    hgen
  simpa using h

/-- **`∫ log(log x) dx` is not elementary.** -/
theorem log_log_not_elementary (T : MTower Fl (ksOf Fl (log (log x))) Cc L)
    (hn : T.n = (log (log x)).nodesOf.length)
    (hgen : ∀ z : L, z ∈ T.F (log (log x)).nodesOf.length) :
    ¬ HasElementaryIntegral (evE Fl T (log (log x)).nodesOf (log (log x))) := by
  have h := front_sound Fl hmonF.1 hmonF.2 (log (log x)) 1 false (by decide +kernel) T hn hgen
  simpa using h

end Thms

/-- The conic `y² + x² + 1 = 0` (no rational point). -/
def Fq : Sup.BPoly ℚ := [[1, 0, 1], [], [1]]

#guard curveShape Fq
-- `∫ log x / y` is not elementary.
#guard frontDecide Fq (div (log x) y) 3 = some false
-- `∫ x log x / y` is elementary.
#guard frontDecide Fq (div (mul x (log x)) y) 3 = some true

end Curves.MT.FrontEx
