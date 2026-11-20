import RischTragerBronstein.Computable.IntegrateExpArgHexpConcrete
import RischTragerBronstein.Computable.IntegrateHyperexpW

/-!
# Verified decisions in `ℚ(x)(exp (arctan x))(exp (exp (arctan x)))`

`t₁′ = t₁ / (x² + 1)`, `t₂ = exp t₁`, `t₂′ = t₁ t₂ / (x² + 1)`. Kernel-checked runs of
`Tower.integrateExpArgHexp`:

* `∫ exp (exp (arctan x)) dx`, `∫ exp (arctan x) exp (exp (arctan x)) dx` and
  `∫ exp (-exp (arctan x)) dx` are **not** elementary;
* `∫ exp (arctan x) exp (exp (arctan x)) / (x² + 1) dx` (`= exp (exp (arctan x))`) is.
-/

open Polynomial

namespace Tower.ExpArgHexpExamples

open Differential CPoly

local instance : Differential ℚ := ⟨0⟩

/-- `η = 1 / (x² + 1)`. -/
def Hn : CPoly ℚ := [1]
/-- `η = 1 / (x² + 1)`. -/
def Hd : CPoly ℚ := [1, 0, 1]
/-- The annihilator of the residues of `η`. -/
def μ : CPoly ℚ := Tower.hexpMu Hn Hd
/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- `a = t₁`: `t₂ = exp t₁`. -/
def a : GPoly (GFrac ℚ) := [([], [1]), one₁]
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `t₁`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), one₁], [one₁])
/-- `t₁ / (x² + 1)`. -/
def T₁d : GFrac (GFrac ℚ) := ([([], [1]), ([1], [1, 0, 1])], [one₁])

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel
theorem cert_a : 2 ≤ (GPoly.trim (ops₁g ℚ) (GPoly.derivT (ops₁g ℚ) (hexpW Hn Hd) a)).length := by
  decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integrateExpArgHexp Hn Hd μ a T₂ D₁ = false := by decide +kernel
theorem run₂ : integrateExpArgHexp Hn Hd μ a [Z, T₁] D₁ = false := by decide +kernel
theorem run₃ : integrateExpArgHexp Hn Hd μ a D₁ T₂ = false := by decide +kernel
theorem run₄ : integrateExpArgHexp Hn Hd μ a [Z, T₁d] D₁ = true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂h Hn Hd) D₁ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

theorem hHn0 : toPoly Hn ≠ 0 := by simp [Hn, toPoly]
theorem hHd0 : toPoly Hd ≠ 0 := by
  have : toPoly Hd = X ^ 2 + 1 := by simp [Hd, toPoly]; ring
  rw [this]; exact X_pow_add_C_ne_zero two_pos 1
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have : toPoly Hn = 1 := by simp [Hn, toPoly]
  rw [this]; exact isCoprime_one_left

/-- The decision theorem in `ℚ(x)(exp (arctan x))(exp (exp (arctan x)))`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaH Hn Hd a)) * X)
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateExpArgHexp Hn Hd μ a A D = true :=
  integrateExpArgHexp_decides_concrete (R := ℚ) (fun _ ↦ rfl) Hn Hd μ a hHn0 hHd0 hcop cert_η
    cert_a A D hD0

/-- **`∫ exp (exp (arctan x)) dx` is not elementary.** -/
theorem exp_exp_arctan_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaH Hn Hd a)) * X)
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ exp (arctan x) exp (exp (arctan x)) / (x² + 1) dx` is elementary.** -/
theorem exp_exp_arctan_deriv_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ :=
      ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (expEtaH Hn Hd a)) * X)
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁d] D₁) :=
  (decides _ D₁ den₁).mpr run₄

end Tower.ExpArgHexpExamples
