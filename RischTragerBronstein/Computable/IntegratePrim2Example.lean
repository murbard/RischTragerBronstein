import RischTragerBronstein.Computable.IntegratePrim2Concrete

/-!
# Verified decisions in `ℚ(x)(log x)(log (x + 1))`

Kernel-checked runs of `Tower.integratePrim2`, turned into theorems by
`Tower.integratePrim2_decides_concrete`:

* `∫ log x · log (x + 1) dx` and `∫ dx / (log x · log (x + 1))` and `∫ log (x + 1) / log x dx`
  are **not** elementary;
* `∫ (log (x + 1) / x + log x / (x + 1)) dx` and `∫ dx / ((x + 1) log (x + 1))` are.
-/

open Polynomial

namespace Tower.Prim2Examples

open Differential CPoly CPoly.PrimPolyExample CPoly.Prim2Example

local instance : Differential ℚ := ⟨0⟩

/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `t₁ = log x`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), ([1], [1])], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])

/-- `log x · log (x + 1)`. -/
def A₁ : GPoly (GFrac (GFrac ℚ)) := [Z, T₁]
/-- `log (x + 1) / x + log x / (x + 1)`. -/
def A₂ : GPoly (GFrac (GFrac ℚ)) := [([([], [1]), ([1], [1, 1])], [one₁]), c [1] [0, 1]]
/-- `1 / (x + 1)`. -/
def A₃ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1, 1]]
/-- `log (x + 1) / log x`. -/
def A₅ : GPoly (GFrac (GFrac ℚ)) := [Z, ([one₁], [([], [1]), ([1], [1])])]
/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂ = log (x + 1)`. -/
def D₃ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]
/-- `t₁ t₂ = log x · log (x + 1)`. -/
def D₄ : GPoly (GFrac (GFrac ℚ)) := [Z, T₁]

theorem run₁ : integratePrim2 En Ed Iη En₂ Ed₂ Iη₂ A₁ D₁ = false := by decide +kernel
theorem run₂ : integratePrim2 En Ed Iη En₂ Ed₂ Iη₂ A₂ D₁ = true := by decide +kernel
theorem run₃ : integratePrim2 En Ed Iη En₂ Ed₂ Iη₂ A₃ D₃ = true := by decide +kernel
theorem run₄ : integratePrim2 En Ed Iη En₂ Ed₂ Iη₂ D₁ D₄ = false := by decide +kernel
theorem run₅ : integratePrim2 En Ed Iη En₂ Ed₂ Iη₂ A₅ D₁ = false := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂p En Ed) D₁ = false := by decide +kernel
theorem den₃ : GPoly.isZero (ops₂p En Ed) D₃ = false := by decide +kernel
theorem den₄ : GPoly.isZero (ops₂p En Ed) D₄ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The decision theorem in `ℚ(x)(log x)(log (x + 1))`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂p En Ed) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integratePrim2 En Ed Iη En₂ Ed₂ Iη₂ A D = true :=
  integratePrim2_decides_concrete (R := ℚ) (fun _ ↦ rfl) En Ed En₂ Ed₂ Iη Iη₂ check_η check_η₂
    η_not_derivative indep A D hD0

/-- **`∫ log x · log (x + 1) dx` is not elementary** (full driver). -/
theorem log_mul_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A₁ D₁) := fun h ↦ by
  have := (decides A₁ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ dx / (log x · log (x + 1))` is not elementary.** -/
theorem inv_log_mul_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ D₁ D₄) := fun h ↦ by
  have := (decides D₁ D₄ den₄).mp h
  rw [run₄] at this
  exact Bool.noConfusion this

/-- **`∫ log (x + 1) / log x dx` is not elementary.** -/
theorem log_div_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A₅ D₁) := fun h ↦ by
  have := (decides A₅ D₁ den₁).mp h
  rw [run₅] at this
  exact Bool.noConfusion this

/-- `∫ (log (x + 1) / x + log x / (x + 1)) dx` is elementary (`= log x · log (x + 1)`). -/
theorem product_rule_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A₂ D₁) :=
  (decides A₂ D₁ den₁).mpr run₂

/-- `∫ dx / ((x + 1) log (x + 1))` is elementary (`= log log (x + 1)`). -/
theorem loglog_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A₃ D₃) :=
  (decides A₃ D₃ den₃).mpr run₃

end Tower.Prim2Examples
