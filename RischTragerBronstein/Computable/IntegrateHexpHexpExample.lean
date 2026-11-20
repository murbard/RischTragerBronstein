import RischTragerBronstein.Computable.IntegrateHexpHexpConcrete
import RischTragerBronstein.Computable.IntegrateHyperexpW

/-!
# Verified decisions in `ℚ(x)(exp (arctan x))(exp (1/x))`

`t₁′ = t₁ / (x² + 1)`, `t₂′ = -t₂ / x²`: two general hyperexponentials, independent
(`hexpHexpIndep`). Kernel-checked runs of `Tower.integrateHexpHexp`:

* `∫ exp (1/x) dx` and `∫ exp (arctan x + 1/x) dx` are **not** elementary;
* `∫ exp (1/x) / x² dx` (`= -exp (1/x)`),
  `∫ exp (arctan x + 1/x) (1/(x²+1) - 1/x²) dx` (`= exp (arctan x + 1/x)`) and
  `∫ exp (arctan x) / (x² + 1) dx` are.
-/

open Polynomial

namespace Tower.HexpHexpExamples

open Differential CPoly

local instance : Differential ℚ := ⟨0⟩

/-- `η₁ = 1 / (x² + 1)`. -/
def Hn : CPoly ℚ := [1]
/-- `η₁ = 1 / (x² + 1)`. -/
def Hd : CPoly ℚ := [1, 0, 1]
/-- The annihilator of the residues of `η₁`. -/
def μ : CPoly ℚ := Tower.hexpMu Hn Hd
/-- `η₂ = -1 / x²`. -/
def Hn₂ : CPoly ℚ := [-1]
/-- `η₂ = -1 / x²`. -/
def Hd₂ : CPoly ℚ := [0, 0, 1]
/-- The annihilator of the residues of `η₂`. -/
def μ₂ : CPoly ℚ := Tower.hexpMu Hn₂ Hd₂
/-- `1 ∈ ℚ(x)`. -/
def one₁ : GFrac ℚ := ([1], [1])
/-- The element `n / d ∈ ℚ(x)` as an element of `ℚ(x)(t₁)`. -/
def c (n d : CPoly ℚ) : GFrac (GFrac ℚ) := ([(n, d)], [one₁])
/-- `0`. -/
def Z : GFrac (GFrac ℚ) := ([], [one₁])
/-- `t₁`. -/
def T₁ : GFrac (GFrac ℚ) := ([([], [1]), one₁], [one₁])
/-- `t₁ (1/(x²+1) - 1/x²) = -t₁ / (x² (x² + 1))`. -/
def T₁c : GFrac (GFrac ℚ) := ([([], [1]), ([-1], [0, 0, 1, 0, 1])], [one₁])
/-- `t₁ / (x² + 1)`. -/
def T₁d : GFrac (GFrac ℚ) := ([([], [1]), ([1], [1, 0, 1])], [one₁])

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel
theorem cert_η₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true := by decide +kernel
theorem cert_ind : hexpHexpIndepAll Hn Hd μ Hn₂ Hd₂ μ₂ = true := by decide +kernel

/-- `1`. -/
def D₁ : GPoly (GFrac (GFrac ℚ)) := [c [1] [1]]

theorem run₁ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, c [1] [1]] D₁ = false := by decide +kernel
theorem run₂ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, T₁] D₁ = false := by decide +kernel
theorem run₃ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, c [1] [0, 0, 1]] D₁ = true := by
  decide +kernel
theorem run₄ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, T₁c] D₁ = true := by decide +kernel
theorem run₅ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [T₁d] D₁ = true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂h Hn Hd) D₁ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

theorem hHn0 : toPoly Hn ≠ 0 := by simp [Hn, toPoly]
theorem hHd0 : toPoly Hd ≠ 0 := by
  have : toPoly Hd = X ^ 2 + 1 := by simp [Hd, toPoly]; ring
  rw [this]; exact X_pow_add_C_ne_zero two_pos 1
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have : toPoly Hn = 1 := by simp [Hn, toPoly]
  rw [this]; exact isCoprime_one_left
theorem hHn20 : toPoly Hn₂ ≠ 0 := by simp [Hn₂, toPoly]
theorem hHd20 : toPoly Hd₂ ≠ 0 := by
  have : toPoly Hd₂ = X ^ 2 := by simp [Hd₂, toPoly]; ring
  rw [this]; exact pow_ne_zero 2 X_ne_zero
theorem hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂) := by
  have : toPoly Hn₂ = C (-1) := by simp [Hn₂, toPoly]
  rw [this, show (C (-1 : ℚ) : ℚ[X]) = -1 by simp]
  exact isCoprime_one_left.neg_left

/-- The derivation of `t₂ = exp (1/x)` on `K₃`. -/
noncomputable abbrev hexpDeriv₂ : (RatFunc (RatFunc ℚ))[X] :=
  C (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))
    (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn₂) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd₂))) * X

/-- The decision theorem in `ℚ(x)(exp (arctan x))(exp (1/x))`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateHexpHexp Hn Hd μ Hn₂ Hd₂ A D = true :=
  integrateHexpHexp_decides_concrete (R := ℚ) (fun _ ↦ rfl) Hn Hd μ hHn0 hHd0 hcop cert_η
    Hn₂ Hd₂ μ₂ hHn20 hHd20 hcop₂ cert_η₂ cert_ind A D hD0

/-- **`∫ exp (1/x) dx` is not elementary.** -/
theorem exp_inv_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, c [1] [1]] D₁) :=
  fun h ↦ by
    have := (decides _ D₁ den₁).mp h
    rw [run₁] at this
    exact Bool.noConfusion this

/-- **`∫ exp (arctan x + 1/x) dx` is not elementary.** -/
theorem exp_arctan_add_inv_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) :=
  fun h ↦ by
    have := (decides _ D₁ den₁).mp h
    rw [run₂] at this
    exact Bool.noConfusion this

/-- **`∫ exp (arctan x + 1/x) (1/(x²+1) - 1/x²) dx` is elementary.** -/
theorem exp_arctan_add_inv_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁c] D₁) :=
  (decides _ D₁ den₁).mpr run₄

end Tower.HexpHexpExamples

/-!
## Shared poles: `ℚ(x)(x eˣ)(x e^{-1/x})`

`η₁ = 1 + 1/x`, `η₂ = (1 + x)/x²`: both denominators vanish at `x = 0`, so the coprime certificate
does not apply; `hexpHexpComb` certifies independence (the Hermite parts `1` and `1/x²` are not
proportional). `∫ x e^{-1/x} dx` is not elementary; `∫ (1 + x) e^{-1/x} / x dx = x e^{-1/x}`.
-/

namespace Tower.HexpHexpExamples₂

open Differential CPoly Tower.HexpHexpExamples

local instance : Differential ℚ := ⟨0⟩

/-- `η₁ = (x + 1)/x`. -/
def Hn : CPoly ℚ := [1, 1]
/-- `η₁ = (x + 1)/x`. -/
def Hd : CPoly ℚ := [0, 1]
/-- The annihilator of the residues of `η₁`. -/
def μ : CPoly ℚ := Tower.hexpMu Hn Hd
/-- `η₂ = (x + 1)/x²`. -/
def Hn₂ : CPoly ℚ := [1, 1]
/-- `η₂ = (x + 1)/x²`. -/
def Hd₂ : CPoly ℚ := [0, 0, 1]
/-- The annihilator of the residues of `η₂`. -/
def μ₂ : CPoly ℚ := Tower.hexpMu Hn₂ Hd₂

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel
theorem cert_η₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true := by decide +kernel
theorem cert_ind : hexpHexpIndepAll Hn Hd μ Hn₂ Hd₂ μ₂ = true := by decide +kernel
theorem not_coprime_cert : hexpHexpIndep Hn Hd μ Hn₂ Hd₂ μ₂ = false := by decide +kernel

theorem run₁ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, c [1] [1]] D₁ = false := by decide +kernel
theorem run₂ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, c [1, 1] [0, 0, 1]] D₁ = true := by
  decide +kernel

theorem den₁ : GPoly.isZero (ops₂h Hn Hd) D₁ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

theorem hHn0 : toPoly Hn ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 0) h; simp [Hn, toPoly] at this
theorem hHd0 : toPoly Hd ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 1) h; simp [Hd, toPoly] at this
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have e1 : toPoly Hn = X + 1 := by simp [Hn, toPoly]; ring
  have e2 : toPoly Hd = X := by simp [Hd, toPoly]
  rw [e1, e2]
  exact ⟨1, -1, by ring⟩
theorem hHn20 : toPoly Hn₂ ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 0) h; simp [Hn₂, toPoly] at this
theorem hHd20 : toPoly Hd₂ ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 2) h; simp [Hd₂, toPoly] at this
theorem hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂) := by
  have e1 : toPoly Hn₂ = X + 1 := by simp [Hn₂, toPoly]; ring
  have e2 : toPoly Hd₂ = X ^ 2 := by simp [Hd₂, toPoly]; ring
  rw [e1, e2]
  exact ⟨1 - X, 1, by ring⟩

/-- The derivation of `t₂ = x e^{-1/x}` on `K₃`. -/
noncomputable abbrev hexpDeriv₂ : (RatFunc (RatFunc ℚ))[X] :=
  C (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))
    (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn₂) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd₂))) * X

/-- The decision theorem in `ℚ(x)(x eˣ)(x e^{-1/x})`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateHexpHexp Hn Hd μ Hn₂ Hd₂ A D = true :=
  integrateHexpHexp_decides_concrete (R := ℚ) (fun _ ↦ rfl) Hn Hd μ hHn0 hHd0 hcop cert_η
    Hn₂ Hd₂ μ₂ hHn20 hHd20 hcop₂ cert_η₂ cert_ind A D hD0

/-- **`∫ x e^{-1/x} dx` is not elementary** (decided in a tower with shared poles). -/
theorem x_exp_inv_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, c [1] [1]] D₁) :=
  fun h ↦ by
    have := (decides _ D₁ den₁).mp h
    rw [run₁] at this
    exact Bool.noConfusion this

end Tower.HexpHexpExamples₂
