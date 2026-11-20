import RischTragerBronstein.Computable.IntegrateHexpPrimConcrete
import RischTragerBronstein.Computable.IntegrateExpPrimExample
import RischTragerBronstein.Computable.IntegrateHyperexpW

/-!
# Verified decisions in the tower `ℚ(x)(log x)(exp (arctan x))`

`t₁ = log x`, `t₂′ = t₂ / (x² + 1)`: a hyperexponential whose `η` has simple poles (at `x = ±i`,
with non-rational residues `∓ i / 2`). Kernel-checked runs of `Tower.integrateHexpPrim`:

* `∫ exp (arctan x) log x dx` and `∫ exp (arctan x) log x / (x² + 1) dx` are **not** elementary;
* `∫ exp (arctan x) (1 / x + log x / (x² + 1)) dx` (`= exp (arctan x) log x`) and
  `∫ log x / x dx` (`= log² x / 2`) are.
-/

open Polynomial

namespace Tower.HexpPrimExamples

open Differential CPoly CPoly.PrimPolyExample Tower.ExpPrimExamples

local instance : Differential ℚ := ⟨0⟩

/-- `η = 1 / (x² + 1)`: numerator. -/
def Hn : CPoly ℚ := [1]
/-- `η = 1 / (x² + 1)`: denominator. -/
def Hd : CPoly ℚ := [1, 0, 1]
/-- The annihilator of the residues of `η`. -/
def μ : CPoly ℚ := Tower.hexpMu Hn Hd

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel

/-- `t₁ / (x² + 1)`. -/
def T₁d : GFrac (GFrac ℚ) := ([([], [1]), ([1], [1, 0, 1])], [one₁])
/-- `1 / x + t₁ / (x² + 1)`. -/
def W₁ : GFrac (GFrac ℚ) := ([([1], [0, 1]), ([1], [1, 0, 1])], [one₁])
/-- `t₁ / x`. -/
def T₁x : GFrac (GFrac ℚ) := ([([], [1]), ([1], [0, 1])], [one₁])

theorem run₁ : integrateHexpPrim En Ed Iη Hn Hd μ [Z, T₁] D₁ = false := by decide +kernel
theorem run₂ : integrateHexpPrim En Ed Iη Hn Hd μ [Z, T₁d] D₁ = false := by decide +kernel
theorem run₃ : integrateHexpPrim En Ed Iη Hn Hd μ [Z, W₁] D₁ = true := by decide +kernel
theorem run₄ : integrateHexpPrim En Ed Iη Hn Hd μ [T₁x] D₁ = true := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

/-- The derivation of `t₂ = exp (arctan x)` on `K₃`. -/
noncomputable abbrev hexpDeriv : (RatFunc (RatFunc ℚ))[X] :=
  C (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))
    (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd))) * X

theorem hHn0 : toPoly Hn ≠ 0 := by simp [Hn, toPoly]
theorem hHd0 : toPoly Hd ≠ 0 := by
  have : toPoly Hd = X ^ 2 + 1 := by simp [Hd, toPoly]; ring
  rw [this]; exact X_pow_add_C_ne_zero two_pos 1
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have : toPoly Hn = 1 := by simp [Hn, toPoly]
  rw [this]; exact isCoprime_one_left

/-- The decision theorem in `ℚ(x)(log x)(exp (arctan x))`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂p En Ed) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateHexpPrim En Ed Iη Hn Hd μ A D = true :=
  integrateHexpPrim_decides_concrete (R := ℚ) (fun _ ↦ rfl) En Ed Hn Hd μ hHn0 hHd0 hcop cert_η
    Iη check_η η_not_derivative A D hD0

/-- **`∫ exp (arctan x) log x dx` is not elementary.** -/
theorem hexp_mul_log_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ exp (arctan x) (1 / x + log x / (x² + 1)) dx` is elementary** (`= exp (arctan x) log x`). -/
theorem hexp_log_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (C (primEta En Ed))
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, W₁] D₁) :=
  (decides _ D₁ den₁).mpr run₃

end Tower.HexpPrimExamples
