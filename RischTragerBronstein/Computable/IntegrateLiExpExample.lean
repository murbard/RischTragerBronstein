import RischTragerBronstein.Computable.IntegrateLiExpConcrete

/-!
# Verified decisions in `ℚ(x)(eˣ)(t₂)`, `t₂ = ∫ dx / (eˣ + x)`

The primitive `t₂ = ∫ dx / (eˣ + x)` is not elementary over `ℚ(x, eˣ)` (the residue of
`1 / (eˣ + x)` at `eˣ = -x` is `1 / (1 - x)`, not a constant). Kernel-checked runs of
`Tower.integrateLiExp`:

* `∫ x t₂ dx` and `∫ dx / t₂` are **not** elementary;
* `∫ t₂ dx` (`= (x - 1) t₂ - x + log (eˣ + x)`: the limited integration
  `x / (eˣ + x) - c / (eˣ + x)` succeeds with `c = 1`), `∫ dx / (eˣ + x)` (`= t₂`),
  `∫ t₂ / (eˣ + x) dx` (`= t₂² / 2`) and `∫ eˣ dx` are.
-/

open Polynomial

namespace Tower.LiExpExamples

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
/-- `W = 1 / (eˣ + x)`, the derivative of `t₂`. -/
def W : GFrac (GFrac ℚ) := ([one₁], [([0, 1], [1]), one₁])

theorem cert_a₁ : trim (deriv a₁) ≠ [] := by decide +kernel
theorem cert_W0 : GPoly.isZero (ops₁g ℚ) W.2 = false := by decide +kernel
theorem cert_Wnd : isDerivExp a₁ W.1 W.2 = false := by decide +kernel
theorem cert_res : GPoly.residueCheck (ops₁g ℚ) (expW a₁) (expReduce a₁ W.1 W.2).r
    (expReduce a₁ W.1 W.2).s = false := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integrateLiExp a₁ W [Z, c [0, 1] [1]] D₁ = false := by decide +kernel
theorem run₀ : integrateLiExp a₁ W T₂ D₁ = true := by decide +kernel
theorem run₂ : integrateLiExp a₁ W [W] D₁ = true := by decide +kernel
theorem run₃ : integrateLiExp a₁ W [Z, W] D₁ = true := by decide +kernel
theorem run₄ : integrateLiExp a₁ W [T₁] D₁ = true := by decide +kernel
theorem run₅ : integrateLiExp a₁ W D₁ T₂ = false := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂e a₁) D₁ = false := by decide +kernel
theorem den₂ : GPoly.isZero (ops₂e a₁) T₂ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The decision theorem in `ℚ(x)(eˣ)(t₂)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂e a₁) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateLiExp a₁ W A D = true :=
  integrateLiExp_decides_concrete (R := ℚ) (fun _ ↦ rfl) a₁ cert_a₁ W cert_W0 cert_Wnd cert_res
    A D hD0

/-- **`∫ x t₂ dx` is not elementary** (`t₂ = ∫ dx / (eˣ + x)`). -/
theorem x_t₂_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, c [0, 1] [1]] D₁) :=
  fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- `∫ t₂ dx` is elementary (`= (x - 1) t₂ - x + log (eˣ + x)`). -/
theorem t₂_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) :=
  (decides T₂ D₁ den₁).mpr run₀

/-- **`∫ dx / t₂` is not elementary.** -/
theorem inv_t₂_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ D₁ T₂) := fun h ↦ by
  have := (decides D₁ T₂ den₂).mp h
  rw [run₅] at this
  exact Bool.noConfusion this

/-- `∫ dx / (eˣ + x)` is elementary over `ℚ(x, eˣ, t₂)` (`= t₂`). -/
theorem W_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [W] D₁) :=
  (decides [W] D₁ den₁).mpr run₂

/-- `∫ t₂ / (eˣ + x) dx` is elementary (`= t₂² / 2`). -/
theorem t₂_sq_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) :=
      ratFuncOfDeriv (C (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a₁))) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, W] D₁) :=
  (decides _ D₁ den₁).mpr run₃

end Tower.LiExpExamples
