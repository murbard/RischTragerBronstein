import RischTragerBronstein.Computable.IntegrateExpArgPrimConcrete

/-!
# Verified decisions in `ℚ(x)(log x)(x^x)`, `x^x = exp (x log x)`

Kernel-checked runs of `Tower.integrateExpArgPrim`:

* `∫ x^x dx`, `∫ x^x log x dx`, `∫ dx / x^x` are **not** elementary;
* `∫ (1 + log x) x^x dx` (`= x^x`) and `∫ 2 (1 + log x) x^{2x} dx` (`= x^{2x}`) are.
-/

open Polynomial

namespace Tower.ExpArgPrimExamples

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
/-- `a = x log x`, so that `t₂ = x^x`. -/
def aX : GPoly (GFrac ℚ) := [([], [1]), ([0, 1], [1])]

theorem cert_a : 2 ≤ (GPoly.trim (ops₁g ℚ) (GPoly.derivT (ops₁g ℚ) [(En, Ed)] aX)).length := by
  decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]
/-- `1 + log x ∈ ℚ(x)(t₁)`. -/
def L1 : GFrac (GFrac ℚ) := ([one₁, one₁], [one₁])

theorem run₁ : integrateExpArgPrim En Ed Iη aX T₂ D₁ = false := by decide +kernel
theorem run₂ : integrateExpArgPrim En Ed Iη aX [Z, L1] D₁ = true := by decide +kernel
theorem run₃ : integrateExpArgPrim En Ed Iη aX [Z, T₁] D₁ = false := by decide +kernel
theorem run₄ : integrateExpArgPrim En Ed Iη aX D₁ T₂ = false := by decide +kernel
theorem run₅ : integrateExpArgPrim En Ed Iη aX [Z, Z, ([([2], [1]), ([2], [1])], [one₁])] D₁ =
    true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂p En Ed) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂p En Ed) T₂ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The derivation of `t₂ = x^x` on `K₃`. -/
noncomputable abbrev expDeriv : (RatFunc (RatFunc ℚ))[X] :=
  C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaG En Ed aX)) * X

/-- The decision theorem in `ℚ(x)(log x)(x^x)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂p En Ed) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateExpArgPrim En Ed Iη aX A D = true :=
  integrateExpArgPrim_decides_concrete (R := ℚ) (fun _ ↦ rfl) En Ed aX cert_a Iη check_η
    η_not_derivative A D hD0

/-- **`∫ x^x dx` is not elementary.** -/
theorem xx_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides T₂ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ x^x log x dx` is not elementary.** -/
theorem xx_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₃] at this
  exact Bool.noConfusion this

/-- **`∫ dx / x^x` is not elementary.** -/
theorem inv_xx_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ D₁ T₂) := fun h ↦ by
  have := (decides D₁ T₂ den₂).mp h
  rw [run₄] at this
  exact Bool.noConfusion this

/-- `∫ (1 + log x) x^x dx` is elementary (`= x^x`). -/
theorem xx_derivative_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, L1] D₁) :=
  (decides _ D₁ den₁).mpr run₂

/-- `∫ 2 (1 + log x) x^{2x} dx` is elementary (`= x^{2x}`). -/
theorem xx_sq_derivative_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃
      [Z, Z, ([([2], [1]), ([2], [1])], [one₁])] D₁) :=
  (decides _ D₁ den₁).mpr run₅

end Tower.ExpArgPrimExamples
