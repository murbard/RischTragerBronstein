import RischTragerBronstein.Computable.IntegratePrimHexpConcrete
import RischTragerBronstein.Computable.IntegrateHyperexpW

/-!
# Verified decisions in `ℚ(x)(exp (arctan x))(log (exp (arctan x) + x))`

`t₁′ = t₁ / (x² + 1)` (a hyperexponential with simple poles), `t₂ = log (t₁ + x)`,
`t₂′ = W = (t₁ + x² + 1) / ((x² + 1)(t₁ + x))`. Kernel-checked runs of `Tower.integratePrimHexp`:

* `∫ log (t₁ + x) dx` is **not** elementary;
* `∫ W dx` (`= t₂`) and `∫ W t₂ dx` (`= t₂² / 2`) are.
-/

open Polynomial

namespace Tower.PrimHexpExamples

open Differential CPoly

local instance : Differential ℚ := ⟨0⟩

/-- `η = 1 / (x² + 1)`: numerator. -/
def Hn : CPoly ℚ := [1]
/-- `η = 1 / (x² + 1)`: denominator. -/
def Hd : CPoly ℚ := [1, 0, 1]
/-- The annihilator of the residues of `η`. -/
def μ : CPoly ℚ := Tower.hexpMu Hn Hd
/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- `n ∈ ℚ[x]` as an element of `ℚ(x)(t₁)`. -/
def c (n : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, [1])], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `U = t₁ + x`. -/
def U : GFrac (GFrac ℚ) := ([([0, 1], [1]), one₁], [one₁])
/-- `W = U′ / U = (t₁ + x² + 1) / ((x² + 1)(t₁ + x))`. -/
def W : GFrac (GFrac ℚ) := ([([1, 0, 1], [1]), one₁], [([0, 1, 0, 1], [1]), ([1, 0, 1], [1])])

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel
theorem cert_W0 : GPoly.isZero (ops₁g ℚ) W.2 = false := by decide +kernel
theorem cert_Wnd : isDerivHexp Hn Hd μ W.1 W.2 = false := by decide +kernel
theorem cert_U0 : (ops₂h Hn Hd).isZero U = false := by decide +kernel
theorem cert_log : (ops₂h Hn Hd).isZero ((ops₂h Hn Hd).add ((ops₂h Hn Hd).mul W U)
    ((ops₂h Hn Hd).neg ((ops₂h Hn Hd).deriv U))) = true := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1]]

theorem run₁ : integratePrimHexp Hn Hd μ W T₂ D₁ = false := by decide +kernel
theorem run₂ : integratePrimHexp Hn Hd μ W [W] D₁ = true := by decide +kernel
theorem run₃ : integratePrimHexp Hn Hd μ W [Z, W] D₁ = true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂h Hn Hd) D₁ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

theorem hHn0 : toPoly Hn ≠ 0 := by simp [Hn, toPoly]
theorem hHd0 : toPoly Hd ≠ 0 := by
  have : toPoly Hd = X ^ 2 + 1 := by simp [Hd, toPoly]; ring
  rw [this]; exact X_pow_add_C_ne_zero two_pos 1
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have : toPoly Hn = 1 := by simp [Hn, toPoly]
  rw [this]; exact isCoprime_one_left

/-- The decision theorem in `ℚ(x)(exp (arctan x))(log (exp (arctan x) + x))`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integratePrimHexp Hn Hd μ W A D = true :=
  integratePrimHexp_decides_concrete (R := ℚ) (fun _ ↦ rfl) Hn Hd μ hHn0 hHd0 hcop cert_η W U
    cert_W0 cert_Wnd cert_U0 cert_log A D hD0

/-- **`∫ log (exp (arctan x) + x) dx` is not elementary.** -/
theorem log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ W t₂ dx` is elementary** (`= t₂² / 2`). -/
theorem W_mul_log_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, W] D₁) :=
  (decides _ D₁ den₁).mpr run₃

end Tower.PrimHexpExamples
