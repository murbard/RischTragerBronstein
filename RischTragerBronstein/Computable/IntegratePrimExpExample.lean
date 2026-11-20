import RischTragerBronstein.Computable.IntegratePrimExpConcrete

/-!
# Verified decisions in `ℚ(x)(eˣ)(log (eˣ + 1))`

Kernel-checked runs of `Tower.integratePrimExp`:

* `∫ log (eˣ + 1) dx` and `∫ dx / log (eˣ + 1)` are **not** elementary;
* `∫ eˣ log (eˣ + 1) dx`, `∫ eˣ log (eˣ + 1) / (eˣ + 1) dx` (`= log (eˣ + 1)² / 2`) and
  `∫ eˣ / ((eˣ + 1) log (eˣ + 1)) dx` (`= log log (eˣ + 1)`) are.
-/

open Polynomial

namespace Tower.PrimExpExamples

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
/-- `U = eˣ + 1`. -/
def U : GFrac (GFrac ℚ) := ([one₁, one₁], [one₁])
/-- `W = eˣ / (eˣ + 1) = U′ / U`, the derivative of `t₂ = log (eˣ + 1)`. -/
def W : GFrac (GFrac ℚ) := ([([], [1]), one₁], [one₁, one₁])

theorem cert_a₁ : trim (deriv a₁) ≠ [] := by decide +kernel
theorem cert_W0 : GPoly.isZero (ops₁g ℚ) W.2 = false := by decide +kernel
theorem cert_Wnd : isDerivExp a₁ W.1 W.2 = false := by decide +kernel
theorem cert_U0 : (ops₂e a₁).isZero U = false := by decide +kernel
theorem cert_log : (ops₂e a₁).isZero ((ops₂e a₁).add ((ops₂e a₁).mul W U)
    ((ops₂e a₁).neg ((ops₂e a₁).deriv U))) = true := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integratePrimExp a₁ W T₂ D₁ = false := by decide +kernel
theorem run₂ : integratePrimExp a₁ W [W] T₂ = true := by decide +kernel
theorem run₃ : integratePrimExp a₁ W [Z, T₁] D₁ = true := by decide +kernel
theorem run₄ : integratePrimExp a₁ W [Z, W] D₁ = true := by decide +kernel
theorem run₅ : integratePrimExp a₁ W D₁ T₂ = false := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂e a₁) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂e a₁) T₂ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The decision theorem in `ℚ(x)(eˣ)(log (eˣ + 1))`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂e a₁) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integratePrimExp a₁ W A D = true :=
  integratePrimExp_decides_concrete (R := ℚ) (fun _ ↦ rfl) a₁ cert_a₁ W U cert_W0 cert_Wnd
    cert_U0 cert_log A D hD0

/-- **`∫ log (eˣ + 1) dx` is not elementary.** -/
theorem log_exp_add_one_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides T₂ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ dx / log (eˣ + 1)` is not elementary.** -/
theorem inv_log_exp_add_one_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ D₁ T₂) := fun h ↦ by
  have := (decides D₁ T₂ den₂).mp h
  rw [run₅] at this
  exact Bool.noConfusion this

/-- `∫ eˣ / ((eˣ + 1) log (eˣ + 1)) dx` is elementary (`= log log (eˣ + 1)`). -/
theorem loglog_exp_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [W] T₂) :=
  (decides [W] T₂ den₂).mpr run₂

/-- `∫ eˣ log (eˣ + 1) dx` is elementary. -/
theorem exp_log_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) :=
  (decides _ D₁ den₁).mpr run₃

/-- `∫ eˣ log (eˣ + 1) / (eˣ + 1) dx` is elementary (`= log (eˣ + 1)² / 2`). -/
theorem log_sq_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, W] D₁) :=
  (decides _ D₁ den₁).mpr run₄

end Tower.PrimExpExamples
