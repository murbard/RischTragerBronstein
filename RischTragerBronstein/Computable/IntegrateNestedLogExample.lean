import RischTragerBronstein.Computable.IntegrateNestedLogConcrete

/-!
# Verified decisions in `ℚ(x)(log x)(log log x)`

Kernel-checked runs of `Tower.integrateNestedLog`:

* `∫ log log x dx` and `∫ dx / log log x` are **not** elementary;
* `∫ dx / (x log x log log x)` (`= log log log x`), `∫ log log x / x dx`
  (`= log x log log x - log x`) and `∫ log log x / (x log x) dx` (`= (log log x)² / 2`) are.
-/

open Polynomial

namespace Tower.NestedLogExamples

open Differential CPoly CPoly.PrimPolyExample

local instance : Differential ℚ := ⟨0⟩

/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `t₁ = log x`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), ([1], [1])], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `W = 1 / (x log x)`, the derivative of `t₂ = log log x`. -/
def W : GFrac (GFrac ℚ) := ([([1], [0, 1])], [([], [1]), ([1], [1])])

theorem cert_W0 : GPoly.isZero (ops₁g ℚ) W.2 = false := by decide +kernel
theorem cert_rW : GPoly.isZero (ops₁g ℚ) (GPoly.divMod (ops₁g ℚ)
    (GPoly.hermite (ops₁g ℚ) [(En, Ed)] W.1 W.2).b
    (GPoly.hermite (ops₁g ℚ) [(En, Ed)] W.1 W.2).s).2 = false := by decide +kernel
theorem cert_Wnd : isDerivPrim En Ed Iη W.1 W.2 = false := by decide +kernel
theorem cert_U0 : (ops₂p En Ed).isZero T₁ = false := by decide +kernel
theorem cert_log : (ops₂p En Ed).isZero ((ops₂p En Ed).add ((ops₂p En Ed).mul W T₁)
    ((ops₂p En Ed).neg ((ops₂p En Ed).deriv T₁))) = true := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integrateNestedLog En Ed Iη W T₂ D₁ = false := by decide +kernel
theorem run₂ : integrateNestedLog En Ed Iη W [W] T₂ = true := by decide +kernel
theorem run₃ : integrateNestedLog En Ed Iη W [Z, c [1] [0, 1]] D₁ = true := by decide +kernel
theorem run₄ : integrateNestedLog En Ed Iη W [Z, W] D₁ = true := by decide +kernel
theorem run₅ : integrateNestedLog En Ed Iη W D₁ T₂ = false := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂p En Ed) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂p En Ed) T₂ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The decision theorem in `ℚ(x)(log x)(log log x)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂p En Ed) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateNestedLog En Ed Iη W A D = true :=
  integrateNestedLog_decides_concrete (R := ℚ) (fun _ ↦ rfl) En Ed W T₁ Iη check_η
    η_not_derivative cert_W0 cert_rW cert_Wnd cert_U0 cert_log A D hD0

/-- **`∫ log log x dx` is not elementary.** -/
theorem loglog_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides T₂ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ dx / log log x` is not elementary.** -/
theorem inv_loglog_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ D₁ T₂) := fun h ↦ by
  have := (decides D₁ T₂ den₂).mp h
  rw [run₅] at this
  exact Bool.noConfusion this

/-- `∫ dx / (x log x log log x)` is elementary (`= log log log x`). -/
theorem logloglog_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [W] T₂) :=
  (decides [W] T₂ den₂).mpr run₂

/-- `∫ log log x / x dx` is elementary. -/
theorem loglog_div_x_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral
      (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, c [1] [0, 1]] D₁) :=
  (decides _ D₁ den₁).mpr run₃

/-- `∫ log log x / (x log x) dx` is elementary (`= (log log x)² / 2`). -/
theorem loglog_sq_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, W] D₁) :=
  (decides _ D₁ den₁).mpr run₄

end Tower.NestedLogExamples
