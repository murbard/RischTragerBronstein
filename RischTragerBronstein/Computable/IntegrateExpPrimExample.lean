import RischTragerBronstein.Computable.IntegrateExpPrimConcrete

/-!
# Verified decisions in the mixed tower `ℚ(x)(log x)(eˣ)`

Kernel-checked runs of `Tower.integrateExpPrim`:

* `∫ eˣ log x dx`, `∫ eˣ / log x dx`, `∫ log x / eˣ dx`, `∫ eˣ / x dx` are **not** elementary;
* `∫ eˣ (log x + 1 / x) dx` (`= eˣ log x`) and `∫ eˣ / (eˣ + 1) dx` (`= log (eˣ + 1)`) are.
-/

open Polynomial

namespace Tower.ExpPrimExamples

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
/-- `a = x`, so that `t₂ = eˣ`. -/
def ax : CPoly ℚ := [0, 1]

theorem cert_a : trim (deriv ax) ≠ [] := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]
/-- `t₂ + 1`. -/
def T₂1 : GPoly (GFrac (GFrac ℚ)) := [c [1] [1], c [1] [1]]

theorem run₁ : integrateExpPrim En Ed Iη ax [Z, T₁] D₁ = false := by decide +kernel
theorem run₂ : integrateExpPrim En Ed Iη ax [Z, ([([1], [0, 1]), ([1], [1])], [one₁])] D₁ =
    true := by decide +kernel
theorem run₃ : integrateExpPrim En Ed Iη ax [Z, ([one₁], [([], [1]), one₁])] D₁ = false := by
  decide +kernel
theorem run₄ : integrateExpPrim En Ed Iη ax [T₁] T₂ = false := by decide +kernel
theorem run₅ : integrateExpPrim En Ed Iη ax [Z, c [1] [0, 1]] D₁ = false := by decide +kernel
theorem run₆ : integrateExpPrim En Ed Iη ax T₂ T₂1 = true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂p En Ed) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂p En Ed) T₂ = false := by decide +kernel
theorem den₃ : GPoly.isZero (ops₂p En Ed) T₂1 = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The derivation of `t₂ = eˣ` on `K₃`. -/
noncomputable abbrev expDeriv : (RatFunc (RatFunc ℚ))[X] :=
  C (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))
    (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly ax)))) * X

/-- The decision theorem in `ℚ(x)(log x)(eˣ)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂p En Ed) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateExpPrim En Ed Iη ax A D = true :=
  integrateExpPrim_decides_concrete (R := ℚ) (fun _ ↦ rfl) En Ed ax cert_a Iη check_η
    η_not_derivative A D hD0

/-- **`∫ eˣ log x dx` is not elementary.** -/
theorem exp_mul_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ eˣ / log x dx` is not elementary.** -/
theorem exp_div_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃
      [Z, ([one₁], [([], [1]), one₁])] D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₃] at this
  exact Bool.noConfusion this

/-- **`∫ log x / eˣ dx` is not elementary.** -/
theorem log_div_exp_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [T₁] T₂) := fun h ↦ by
  have := (decides _ T₂ den₂).mp h
  rw [run₄] at this
  exact Bool.noConfusion this

/-- **`∫ eˣ / x dx` is not elementary** (over `ℚ(x, log x, eˣ)`). -/
theorem exp_div_x_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, c [1] [0, 1]] D₁) :=
  fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₅] at this
  exact Bool.noConfusion this

/-- `∫ eˣ (log x + 1 / x) dx` is elementary (`= eˣ log x`). -/
theorem exp_log_product_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃
      [Z, ([([1], [0, 1]), ([1], [1])], [one₁])] D₁) :=
  (decides _ D₁ den₁).mpr run₂

/-- `∫ eˣ / (eˣ + 1) dx` is elementary (`= log (eˣ + 1)`). -/
theorem log_exp_plus_one_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ T₂1) :=
  (decides _ T₂1 den₃).mpr run₆

end Tower.ExpPrimExamples
