import RischTragerBronstein.Computable.IntegrateLiHexpConcrete
import RischTragerBronstein.Computable.IntegrateHyperexpW

/-!
# Verified decisions in `ℚ(x)(exp (arctan x))(t₂)`, `t₂ = ∫ dx / (exp (arctan x) + x)`

`t₁′ = t₁ / (x² + 1)`; the primitive `t₂ = ∫ dx / (t₁ + x)` is not elementary over `ℚ(x, t₁)`
(the residue of `W = 1 / (t₁ + x)` at `t₁ = -x` is `(x² + 1) / (x² - x + 1)`, not a constant).
Kernel-checked runs of `Tower.integrateLiHexp`:

* `∫ x t₂ dx`, `∫ t₂ dx` and `∫ exp (arctan x) dx` are **not** elementary;
* `∫ t₂ / (t₁ + x) dx` (`= t₂² / 2`) is.
-/

open Polynomial

namespace Tower.LiHexpExamples

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
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `t₁`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), one₁], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `W = 1 / (t₁ + x)`, the derivative of `t₂`. -/
def W : GFrac (GFrac ℚ) := ([one₁], [([0, 1], [1]), one₁])

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel
theorem cert_W0 : GPoly.isZero (ops₁g ℚ) W.2 = false := by decide +kernel
theorem cert_Wnd : isDerivHexp Hn Hd μ W.1 W.2 = false := by decide +kernel
theorem cert_res : GPoly.residueCheck (ops₁g ℚ) (hexpW Hn Hd) (hexpReduce Hn Hd W.1 W.2).r
    (hexpReduce Hn Hd W.1 W.2).s = false := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]
/-- `t₂`. -/
def T₂ : GPoly (GFrac (GFrac ℚ)) := [Z, c [1] [1]]

theorem run₁ : integrateLiHexp Hn Hd μ W [Z, c [0, 1] [1]] D₁ = false := by decide +kernel
theorem run₂ : integrateLiHexp Hn Hd μ W T₂ D₁ = false := by decide +kernel
theorem run₃ : integrateLiHexp Hn Hd μ W [Z, W] D₁ = true := by decide +kernel
theorem run₄ : integrateLiHexp Hn Hd μ W [T₁] D₁ = false := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂h Hn Hd) D₁ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

theorem hHn0 : toPoly Hn ≠ 0 := by simp [Hn, toPoly]
theorem hHd0 : toPoly Hd ≠ 0 := by
  have : toPoly Hd = X ^ 2 + 1 := by simp [Hd, toPoly]; ring
  rw [this]; exact X_pow_add_C_ne_zero two_pos 1
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have : toPoly Hn = 1 := by simp [Hn, toPoly]
  rw [this]; exact isCoprime_one_left

/-- The decision theorem in `ℚ(x)(exp (arctan x))(t₂)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateLiHexp Hn Hd μ W A D = true :=
  integrateLiHexp_decides_concrete (R := ℚ) (fun _ ↦ rfl) Hn Hd μ hHn0 hHd0 hcop cert_η W
    cert_W0 cert_Wnd cert_res A D hD0

/-- **`∫ t₂ dx` is not elementary**, `t₂ = ∫ dx / (exp (arctan x) + x)`. -/
theorem li_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ T₂ D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₂] at this
  exact Bool.noConfusion this

/-- **`∫ t₂ / (exp (arctan x) + x) dx` is elementary** (`= t₂² / 2`). -/
theorem li_mul_W_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv (C (val₂ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) W))
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, W] D₁) :=
  (decides _ D₁ den₁).mpr run₃

end Tower.LiHexpExamples
