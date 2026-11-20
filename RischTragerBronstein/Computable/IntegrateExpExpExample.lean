import RischTragerBronstein.Computable.IntegrateExpExpConcrete

/-!
# Verified decisions in `ℚ(x)(e^{x²})(eˣ)`

Kernel-checked runs of `Tower.integrateExpExp`:

* `∫ e^{x²} eˣ dx` and `∫ e^{x²} dx` are **not** elementary;
* `∫ (2x + 1) e^{x²} eˣ dx` (`= e^{x² + x}`) and `∫ eˣ / (eˣ + 1) dx` are.
-/

open Polynomial

namespace Tower.ExpExpExamples

open Differential CPoly

local instance : Differential ℚ := ⟨0⟩

/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `t₁ = e^{x²}`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), ([1], [1])], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `a₁ = x²`. -/
def ax2 : CPoly ℚ := [0, 0, 1]
/-- `a = x`. -/
def ax : CPoly ℚ := [0, 1]

theorem cert_a₁ : trim (deriv ax2) ≠ [] := by decide +kernel
theorem cert_a : trim (deriv ax) ≠ [] := by decide +kernel
theorem cert_ind : expIndep ax2 ax = true := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂ + 1`. -/
def T₂1 : GPoly (GFrac (GFrac ℚ)) := [c [1] [1], c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integrateExpExp ax2 ax [Z, T₁] D₁ = false := by decide +kernel
theorem run₂ : integrateExpExp ax2 ax [Z, ([([], [1]), ([1, 2], [1])], [one₁])] D₁ = true := by
  decide +kernel
theorem run₃ : integrateExpExp ax2 ax [T₁] D₁ = false := by decide +kernel
theorem run₄ : integrateExpExp ax2 ax T₂ T₂1 = true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂e ax2) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂e ax2) T₂1 = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The derivation of `t₁ = e^{x²}` on `ℚ(x)(t₁)`. -/
noncomputable abbrev d₁ : (RatFunc ℚ)[X] :=
  C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly ax2))) * X
/-- The derivation of `t₂ = eˣ` on `K₃`. -/
noncomputable abbrev d₂ : (RatFunc (RatFunc ℚ))[X] :=
  C (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))
    (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly ax)))) * X

/-- The decision theorem in `ℚ(x)(e^{x²})(eˣ)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂e ax2) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv d₁
    letI : Differential K₃ := ratFuncOfDeriv d₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateExpExp ax2 ax A D = true :=
  integrateExpExp_decides_concrete (R := ℚ) (fun _ ↦ rfl) ax2 ax cert_a₁ cert_a cert_ind A D hD0

/-- **`∫ e^{x²} eˣ dx` is not elementary.** -/
theorem exp_sq_mul_exp_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv d₁
    letI : Differential K₃ := ratFuncOfDeriv d₂
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ e^{x²} dx` is not elementary** (over `ℚ(x, e^{x²}, eˣ)`). -/
theorem exp_sq_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv d₁
    letI : Differential K₃ := ratFuncOfDeriv d₂
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [T₁] D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₃] at this
  exact Bool.noConfusion this

/-- `∫ (2x + 1) e^{x²} eˣ dx` is elementary (`= e^{x² + x}`). -/
theorem exp_sum_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv d₁
    letI : Differential K₃ := ratFuncOfDeriv d₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃
      [Z, ([([], [1]), ([1, 2], [1])], [one₁])] D₁) :=
  (decides _ D₁ den₁).mpr run₂

/-- `∫ eˣ / (eˣ + 1) dx` is elementary. -/
theorem log_exp_plus_one_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv d₁
    letI : Differential K₃ := ratFuncOfDeriv d₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ T₂1) :=
  (decides _ T₂1 den₂).mpr run₄

end Tower.ExpExpExamples
