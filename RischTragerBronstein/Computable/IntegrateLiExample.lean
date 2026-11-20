import RischTragerBronstein.Computable.IntegrateLiConcrete

/-!
# Verified decisions in `ℚ(x)(log x)(li x)`, `li x = ∫ dx / log x`

Kernel-checked runs of `Tower.integrateLi`:

* `∫ li x dx` and `∫ dx / li x` are **not** elementary (over `ℚ(x, log x, li x)`);
* `∫ li x / x dx` (`= li x · log x - x`), `∫ dx / log² x` (`= li x - x / log x`),
  `∫ li x / log x dx` (`= li² x / 2`) and `∫ dx / (log x · li x)` (`= log li x`) are.
-/

open Polynomial

namespace Tower.LiExamples

open Differential CPoly CPoly.PrimPolyExample

local instance : Differential ℚ := ⟨0⟩

/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `W = 1 / log x`, the derivative of `t₂ = li x`. -/
def W : GFrac (GFrac ℚ) := ([one₁], [([], [1]), one₁])
/-- `1 / log² x`. -/
def W2 : GFrac (GFrac ℚ) := ([one₁], [([], [1]), ([], [1]), one₁])

theorem cert_W0 : GPoly.isZero (ops₁g ℚ) W.2 = false := by decide +kernel
theorem cert_rW : GPoly.isZero (ops₁g ℚ) (GPoly.divMod (ops₁g ℚ)
    (GPoly.hermite (ops₁g ℚ) [(En, Ed)] W.1 W.2).b
    (GPoly.hermite (ops₁g ℚ) [(En, Ed)] W.1 W.2).s).2 = false := by decide +kernel
theorem cert_Wnd : isDerivPrim En Ed Iη W.1 W.2 = false := by decide +kernel
theorem cert_resW : GPoly.residueCheck (ops₁g ℚ) [(En, Ed)]
    (GPoly.divMod (ops₁g ℚ) (GPoly.hermite (ops₁g ℚ) [(En, Ed)] W.1 W.2).b
      (GPoly.hermite (ops₁g ℚ) [(En, Ed)] W.1 W.2).s).2
    (GPoly.hermite (ops₁g ℚ) [(En, Ed)] W.1 W.2).s = false := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integrateLi En Ed Iη W T₂ D₁ = false := by decide +kernel
theorem run₂ : integrateLi En Ed Iη W [Z, c [1] [0, 1]] D₁ = true := by decide +kernel
theorem run₃ : integrateLi En Ed Iη W [W2] D₁ = true := by decide +kernel
theorem run₄ : integrateLi En Ed Iη W [Z, W] D₁ = true := by decide +kernel
theorem run₅ : integrateLi En Ed Iη W [W] T₂ = true := by decide +kernel
theorem run₆ : integrateLi En Ed Iη W D₁ T₂ = false := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂p En Ed) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂p En Ed) T₂ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The decision theorem in `ℚ(x)(log x)(li x)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂p En Ed) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateLi En Ed Iη W A D = true :=
  integrateLi_decides_concrete (R := ℚ) (fun _ ↦ rfl) En Ed W Iη check_η
    η_not_derivative cert_W0 cert_rW cert_Wnd cert_resW A D hD0

/-- **`∫ li x dx` is not elementary** over `ℚ(x, log x, li x)`. -/
theorem li_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides T₂ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ dx / li x` is not elementary.** -/
theorem inv_li_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ D₁ T₂) := fun h ↦ by
  have := (decides D₁ T₂ den₂).mp h
  rw [run₆] at this
  exact Bool.noConfusion this

/-- `∫ li x / x dx` is elementary (`= li x log x - x`). -/
theorem li_div_x_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, c [1] [0, 1]] D₁) :=
  (decides _ D₁ den₁).mpr run₂

/-- `∫ dx / log² x` is elementary in the tower (`= li x - x / log x`). -/
theorem inv_log_sq_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [W2] D₁) :=
  (decides _ D₁ den₁).mpr run₃

/-- `∫ li x / log x dx` is elementary (`= li² x / 2`). -/
theorem li_sq_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, W] D₁) :=
  (decides _ D₁ den₁).mpr run₄

/-- `∫ dx / (log x · li x)` is elementary (`= log li x`). -/
theorem log_li_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [W] T₂) :=
  (decides _ T₂ den₂).mpr run₅

end Tower.LiExamples
