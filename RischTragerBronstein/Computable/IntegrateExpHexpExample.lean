import RischTragerBronstein.Computable.IntegrateExpHexpConcrete
import RischTragerBronstein.Computable.IntegrateHyperexpW

/-!
# Verified decisions in `ℚ(x)(exp (arctan x))(eˣ)`

`t₁′ = t₁ / (x² + 1)` (a hyperexponential with simple poles), `t₂ = eˣ`; the independence of `t₁`
and `t₂` is certified by `hexpExpIndep` (the residues of `1 / (x² + 1)` are not rational).
Kernel-checked runs of `Tower.integrateExpHexp`:

* `∫ exp (arctan x + x) dx`, `∫ eˣ / (x² + 1) dx` and `∫ exp (arctan x) dx` are **not**
  elementary;
* `∫ eˣ exp (arctan x) (x² + 2) / (x² + 1) dx` (`= eˣ exp (arctan x)`), `∫ eˣ dx`,
  `∫ e^{-x} dx` and `∫ dx / (x² + 1)` are.
-/

open Polynomial

namespace Tower.ExpHexpExamples

open Differential CPoly

local instance : Differential ℚ := ⟨0⟩

/-- `η = 1 / (x² + 1)`: numerator. -/
def Hn : CPoly ℚ := [1]
/-- `η = 1 / (x² + 1)`: denominator. -/
def Hd : CPoly ℚ := [1, 0, 1]
/-- The annihilator of the residues of `η`. -/
def μ : CPoly ℚ := Tower.hexpMu Hn Hd
/-- `a = x`: `t₂ = eˣ`. -/
def a : CPoly ℚ := [0, 1]
/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `t₁`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), one₁], [one₁])
/-- `t₁ (x² + 2) / (x² + 1)`. -/
def T₁c : GFrac (GFrac ℚ) := ([([], [1]), ([2, 0, 1], [1, 0, 1])], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel
theorem cert_a : trim (deriv a) ≠ [] := by decide +kernel
theorem cert_ind : hexpExpIndep Hn Hd μ a = true := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]

theorem run₁ : integrateExpHexp Hn Hd μ a [Z, T₁] D₁ = false := by decide +kernel
theorem run₂ : integrateExpHexp Hn Hd μ a [Z, c [1] [1, 0, 1]] D₁ = false := by decide +kernel
theorem run₃ : integrateExpHexp Hn Hd μ a [T₁] D₁ = false := by decide +kernel
theorem run₄ : integrateExpHexp Hn Hd μ a [Z, T₁c] D₁ = true := by decide +kernel
theorem run₅ : integrateExpHexp Hn Hd μ a [Z, c [1] [1]] D₁ = true := by decide +kernel
theorem run₆ : integrateExpHexp Hn Hd μ a D₁ [Z, c [1] [1]] = true := by decide +kernel
theorem run₇ : integrateExpHexp Hn Hd μ a [c [1] [1, 0, 1]] D₁ = true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂h Hn Hd) D₁ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

theorem hHn0 : toPoly Hn ≠ 0 := by simp [Hn, toPoly]
theorem hHd0 : toPoly Hd ≠ 0 := by
  have : toPoly Hd = X ^ 2 + 1 := by simp [Hd, toPoly]; ring
  rw [this]; exact X_pow_add_C_ne_zero two_pos 1
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have : toPoly Hn = 1 := by simp [Hn, toPoly]
  rw [this]; exact isCoprime_one_left

/-- The derivation of `t₂ = eˣ` on `K₃`. -/
noncomputable abbrev expDeriv : (RatFunc (RatFunc ℚ))[X] :=
  C (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))
    (algebraMap ℚ[X] (RatFunc ℚ) (derivative (toPoly a)))) * X

/-- The decision theorem in `ℚ(x)(exp (arctan x))(eˣ)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateExpHexp Hn Hd μ a A D = true :=
  integrateExpHexp_decides_concrete (R := ℚ) (fun _ ↦ rfl) Hn Hd μ a hHn0 hHd0 hcop cert_η cert_a
    cert_ind A D hD0

/-- **`∫ exp (arctan x + x) dx` is not elementary.** -/
theorem exp_arctan_add_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) := fun h ↦ by
  have := (decides _ D₁ den₁).mp h
  rw [run₁] at this
  exact Bool.noConfusion this

/-- **`∫ eˣ exp (arctan x) (x² + 2) / (x² + 1) dx` is elementary** (`= eˣ exp (arctan x)`). -/
theorem exp_mul_hexp_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv expDeriv
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁c] D₁) :=
  (decides _ D₁ den₁).mpr run₄

end Tower.ExpHexpExamples
