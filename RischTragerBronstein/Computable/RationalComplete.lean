import RischTragerBronstein.Computable.HermiteComplete
import RischTragerBronstein.Computable.LogTimesDecision

/-!
# The executable rational integrator is totally correct

* `rationalCheck_integrateRational`: for `D ≠ 0`, the output of `integrateRational A D` always
  passes its certificate.
* `integrateRational_correct`: hence, unconditionally,
  `A / D = (gn / gd + Q)′ + r / s` with `s` squarefree, `deg r < deg s`, and `A / D` has an
  elementary integral, namely `gn / gd + Q + ∑_{s(α)=0} (r(α) / s′(α)) log (x - α)`.
* `integrateRational_rational_iff`: `∫ A / D` is a rational function iff the computed `r` is zero.
* `logTimes_decides'`: the decision theorem for `∫ f(x) log x dx`, now with **no certificate
  hypothesis**: `f log x` is elementary-integrable iff `logCrit` holds for the computed Hermite
  data.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

lemma derivative_X_pow_mul_integAux (n : ℕ) (p : CPoly R) :
    derivative (X ^ (n + 1) * toPoly (integAux (n + 1) p)) = X ^ n * toPoly p := by
  induction p generalizing n with
  | nil => simp [integAux]
  | cons a p ih =>
    have hn : ((n : R) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hstep : X ^ (n + 1) * toPoly (integAux (n + 1) (a :: p)) =
        C (a / ((n : R) + 1)) * X ^ (n + 1) + X ^ (n + 1 + 1) * toPoly (integAux (n + 1 + 1) p) := by
      simp only [integAux, toPoly_cons, Nat.cast_add, Nat.cast_one]
      ring
    rw [hstep, derivative_add, ih, derivative_C_mul, derivative_X_pow, Nat.add_sub_cancel,
      toPoly_cons]
    have : C (a / ((n : R) + 1)) * (C ((n + 1 : ℕ) : R) * X ^ n) = C a * X ^ n := by
      rw [← mul_assoc, ← C_mul]
      congr 2
      push_cast
      field_simp
    rw [this]
    ring

/-- `integ` computes a polynomial antiderivative. -/
theorem derivative_toPoly_integ (p : CPoly R) : derivative (toPoly (integ p)) = toPoly p := by
  have := derivative_X_pow_mul_integAux 0 p
  simpa [integ] using this

/-- **The rational integrator always passes its certificate.** -/
theorem rationalCheck_integrateRational (A D : CPoly R) (hD : toPoly D ≠ 0) :
    rationalCheck A D (integrateRational A D) = true := by
  have hH := hermiteCheck_hermite A D hD
  rw [hermiteCheck_iff] at hH
  obtain ⟨-, hgd, hs0, hid, hsq⟩ := hH
  have hsne : trim (hermite A D).s ≠ [] := fun h ↦ hs0 ((trim_eq_nil_iff _).mp h)
  rw [rationalCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [hermiteCheck_iff]
    refine ⟨hD, hgd, hs0, ?_, hsq⟩
    have hb : toPoly (add (mul (deriv (integrateRational A D).Q) (integrateRational A D).s)
        (integrateRational A D).r) = toPoly (hermite A D).b := by
      simp only [integrateRational, toPoly_add, toPoly_mul, toPoly_deriv, toPoly_trim,
        derivative_toPoly_integ]
      exact (divMod_spec _ _).symm
    simp only [hb]
    exact hid
  · simp only [integrateRational, trim_trim]
    exact divMod_remainder_lt _ _ hsne

variable [Differential R]

/-- **Total correctness of the rational integrator.** -/
theorem integrateRational_correct (h0 : ∀ a : R, a′ = 0) (A D : CPoly R) (hD : toPoly D ≠ 0) :
    letI := ratFuncOfDeriv (1 : R[X])
    (algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D) =
      (algebraMap R[X] (RatFunc R) (toPoly (integrateRational A D).gn) /
          algebraMap R[X] (RatFunc R) (toPoly (integrateRational A D).gd) +
          algebraMap R[X] (RatFunc R) (toPoly (integrateRational A D).Q))′ +
        algebraMap R[X] (RatFunc R) (toPoly (integrateRational A D).r) /
          algebraMap R[X] (RatFunc R) (toPoly (integrateRational A D).s)) ∧
    Squarefree (toPoly (integrateRational A D).s) ∧
    (toPoly (integrateRational A D).r).degree < (toPoly (integrateRational A D).s).degree ∧
    HasElementaryIntegral
      (algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D)) :=
  rationalCheck_sound h0 A D _ (rationalCheck_integrateRational A D hD)

/-- `∫ A / D` is a rational function iff the computed logarithmic numerator vanishes. -/
theorem integrateRational_rational_iff (h0 : ∀ a : R, a′ = 0) (A D : CPoly R)
    (hD : toPoly D ≠ 0) :
    letI := ratFuncOfDeriv (1 : R[X])
    (∃ y : RatFunc R, y′ =
      algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D)) ↔
    isZero (integrateRational A D).r = true :=
  rationalCheck_rational_iff h0 A D _ (rationalCheck_integrateRational A D hD)

/-- **`∫ f(x) log x dx` is decided**, with no certificate hypothesis. -/
theorem logTimes_decides' (h0 : ∀ r : R, r′ = 0) (A D : CPoly R) (hD : toPoly D ≠ 0) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (logEta (R := R)))
    (logCrit (integrateRational A D).r (integrateRational A D).s = true →
      HasElementaryIntegral (logIntegrand A D)) ∧
    (logCrit (integrateRational A D).r (integrateRational A D).s = false →
      ¬HasElementaryIntegral (logIntegrand A D)) :=
  logTimes_decides h0 A D _ (rationalCheck_integrateRational A D hD)

end CPoly
