import RischTragerBronstein.Computable.IntegrateExpArgExpConcrete

/-!
# Verified decisions in `ℚ(x)(eˣ)(e^{eˣ})`

Kernel-checked runs of `Tower.integrateExpArgExp`:

* `∫ e^{eˣ} dx`, `∫ e^{-eˣ} dx`, `∫ e^{eˣ} dx / x` are **not** elementary;
* `∫ eˣ e^{eˣ} dx` (`= e^{eˣ}`) and `∫ 2 eˣ e^{2 eˣ} dx` (`= e^{2 eˣ}`) are.
-/

open Polynomial

namespace Tower.ExpArgExpExamples

open Differential CPoly

local instance : Differential ℚ := ⟨0⟩

/-- `a₁ = x`: `t₁ = eˣ`. -/
def a₁ : CPoly ℚ := [0, 1]
/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `t₁ = eˣ`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), one₁], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `a = t₁ = eˣ`, so that `t₂ = e^{eˣ}`. -/
def aT : GPoly (GFrac ℚ) := [([], [1]), one₁]

theorem cert_a₁ : trim (deriv a₁) ≠ [] := by decide +kernel
theorem cert_deg : 2 ≤ (GPoly.trim (ops₁g ℚ) (GPoly.derivT (ops₁g ℚ) (expW a₁) aT)).length := by
  decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integrateExpArgExp a₁ aT T₂ D₁ = false := by decide +kernel
theorem run₂ : integrateExpArgExp a₁ aT [Z, T₁] D₁ = true := by decide +kernel
theorem run₃ : integrateExpArgExp a₁ aT D₁ T₂ = false := by decide +kernel
theorem run₄ : integrateExpArgExp a₁ aT [Z, c [1] [0, 1]] D₁ = false := by decide +kernel
theorem run₅ : integrateExpArgExp a₁ aT [Z, Z, ([([], [1]), ([2], [1])], [one₁])] D₁ = true := by
  decide +kernel

theorem den₁ : GPoly.isZero (ops₂e a₁) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂e a₁) T₂ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The decision theorem in `ℚ(x)(eˣ)(e^{eˣ})`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂e a₁) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaE a₁ aT)) * X)
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateExpArgExp a₁ aT A D = true :=
  integrateExpArgExp_decides_concrete (R := ℚ) (fun _ ↦ rfl) a₁ aT cert_a₁ cert_deg A D hD0

/-- **`∫ e^{eˣ} dx` is not elementary.** -/
theorem exp_exp_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaE a₁ aT)) * X)
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides T₂ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ e^{-eˣ} dx` is not elementary.** -/
theorem exp_neg_exp_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaE a₁ aT)) * X)
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ D₁ T₂) := fun h ↦ by
  have := (decides D₁ T₂ den₂).mp h
  rw [run₃] at this
  exact Bool.noConfusion this

/-- **`∫ e^{eˣ} / x dx` is not elementary.** -/
theorem exp_exp_div_x_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaE a₁ aT)) * X)
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, c [1] [0, 1]] D₁) :=
  fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₄] at this
  exact Bool.noConfusion this

/-- `∫ eˣ e^{eˣ} dx` is elementary (`= e^{eˣ}`). -/
theorem exp_exp_derivative_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaE a₁ aT)) * X)
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) :=
  (decides _ D₁ den₁).mpr run₂

/-- `∫ 2 eˣ e^{2 eˣ} dx` is elementary (`= e^{2 eˣ}`). -/
theorem exp_exp_sq_derivative_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaE a₁ aT)) * X)
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃
      [Z, Z, ([([], [1]), ([2], [1])], [one₁])] D₁) :=
  (decides _ D₁ den₁).mpr run₅

end Tower.ExpArgExpExamples

namespace Tower.ExpArgExpExamples2

open Differential CPoly

local instance : Differential ℚ := ⟨0⟩

/-- `a₁ = x`: `t₁ = eˣ`. -/
def a₁ : CPoly ℚ := [0, 1]
def one₁ : GFrac ℚ := ([1], [1])
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `a = eˣ + 2x`: `a′ = eˣ + 2` has the non-zero constant term `2 = 2 a₁′`, so a solution of the
Risch equation may have a pole of order `2` at `eˣ` where the right-hand side has order `1`. -/
def aT2 : GPoly (GFrac ℚ) := [([0, 2], [1]), one₁]

theorem cert_deg2 : 2 ≤ (GPoly.trim (ops₁g ℚ) (GPoly.derivT (ops₁g ℚ) (expW a₁) aT2)).length := by
  decide +kernel

/-- `t₂ = exp (eˣ + 2x)`, `∫ t₂ / eˣ dx`: the solution `y = 1 / e^{2x}` has a pole of order `2`
at `eˣ` (`∫ e^{-x} exp (eˣ + 2x) dx = e^{-2x} exp (eˣ + 2x)`), found by the special-denominator
bound. -/
theorem run_cancel : integrateExpArgExp a₁ aT2 [Z, ([one₁], [([], [1]), one₁])] [c [1] [1]] =
    true := by decide +kernel

end Tower.ExpArgExpExamples2
