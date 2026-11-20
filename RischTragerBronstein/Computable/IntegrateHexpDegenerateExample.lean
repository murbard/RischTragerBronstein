import RischTragerBronstein.Computable.IntegrateHexpHexpExample

/-!
# A degenerate pair of hyperexponentials: `η₁ = 6/(x³ - 2)`, `η₂ = 6x/(x³ - 2)`

Both `ηᵢ` have only simple poles (at the roots of `x³ - 2`) and no polynomial part, and the poles
are shared: neither the coprime-denominator certificate nor the Hermite-part certificate applies.
The residues are `ρ₁ = x`, `ρ₂ = x²` (at a root `α`: `α` and `α²`); no `λ ∈ ℚ` makes `λ α + α²`
rational, so `hexpDegen` certifies independence. Kernel-checked runs of `Tower.integrateHexpHexp`:

* `∫ t₂ dx` and `∫ t₁ t₂ dx` are **not** elementary;
* `∫ η₂ t₂ dx = t₂` and `∫ (η₁ + η₂) t₁ t₂ dx = t₁ t₂` are.
-/

open Polynomial

namespace Tower.HexpDegenerateExamples

open Differential CPoly Tower.HexpHexpExamples

local instance : Differential ℚ := ⟨0⟩

/-- `η₁ = 6/(x³ - 2)`. -/
def Hn : CPoly ℚ := [6]
/-- `η₁ = 6/(x³ - 2)`. -/
def Hd : CPoly ℚ := [-2, 0, 0, 1]
/-- The annihilator of the residues of `η₁`. -/
def μ : CPoly ℚ := Tower.hexpMu Hn Hd
/-- `η₂ = 6x/(x³ - 2)`. -/
def Hn₂ : CPoly ℚ := [0, 6]
/-- `η₂ = 6x/(x³ - 2)`. -/
def Hd₂ : CPoly ℚ := [-2, 0, 0, 1]
/-- The annihilator of the residues of `η₂`. -/
def μ₂ : CPoly ℚ := Tower.hexpMu Hn₂ Hd₂
/-- `t₁ (η₁ + η₂)`. -/
def T₁c : GFrac (GFrac ℚ) := ([([], [1]), ([6, 6], [-2, 0, 0, 1])], [one₁])

set_option maxRecDepth 100000

theorem cert_η : hyperexpMonomialCheck Hn Hd μ = true := by decide +kernel
theorem cert_η₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true := by decide +kernel
/-- The earlier certificates do not apply ... -/
theorem not_full_cert : hexpHexpIndepFull Hn Hd μ Hn₂ Hd₂ μ₂ = false := by decide +kernel
/-- ... but the degenerate-pair certificate does. -/
theorem cert_ind : hexpHexpIndepAll Hn Hd μ Hn₂ Hd₂ μ₂ = true := by decide +kernel

theorem run₁ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, c [1] [1]] D₁ = false := by decide +kernel
theorem run₂ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, T₁] D₁ = false := by decide +kernel
theorem run₃ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, c [0, 6] [-2, 0, 0, 1]] D₁ = true := by
  decide +kernel
theorem run₄ : integrateHexpHexp Hn Hd μ Hn₂ Hd₂ [Z, T₁c] D₁ = true := by decide +kernel

theorem den₁ : GPoly.isZero (ops₂h Hn Hd) D₁ = false := by decide +kernel

local notation "K₃" => RatFunc (RatFunc (RatFunc ℚ))

theorem hHn0 : toPoly Hn ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 0) h; simp [Hn, toPoly] at this
theorem hHd0 : toPoly Hd ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 0) h; simp [Hd, toPoly] at this
theorem hcop : IsCoprime (toPoly Hn) (toPoly Hd) := by
  have e1 : toPoly Hn = C 6 := by simp [Hn, toPoly]
  rw [e1]
  exact ⟨C (1 / 6), 0, by rw [zero_mul, add_zero, ← C_mul]; norm_num⟩
theorem hHn20 : toPoly Hn₂ ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 1) h; simp [Hn₂, toPoly] at this
theorem hHd20 : toPoly Hd₂ ≠ 0 := by
  intro h; have := congrArg (fun p ↦ p.coeff 0) h; simp [Hd₂, toPoly] at this
theorem hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂) := by
  have e1 : toPoly Hn₂ = C 6 * X := by simp [Hn₂, toPoly]
  have e2 : toPoly Hd₂ = X ^ 3 - C 2 := by simp [Hd₂, toPoly]; ring
  have h1 : C (1 / 2 : ℚ) * C 2 = 1 := by rw [← C_mul]; norm_num
  have h2 : C (1 / 12 : ℚ) * C 6 = C (1 / 2) := by rw [← C_mul]; norm_num
  rw [e1, e2]
  exact ⟨C (1 / 12) * X ^ 2, -C (1 / 2), by linear_combination X ^ 3 * h2 + h1⟩

/-- The derivation of `t₂` on `K₃`. -/
noncomputable abbrev hexpDeriv₂ : (RatFunc (RatFunc ℚ))[X] :=
  C (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))
    (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn₂) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd₂))) * X

/-- The decision theorem in `ℚ(x)(t₁)(t₂)`, `t₁′ = 6 t₁/(x³ - 2)`, `t₂′ = 6x t₂/(x³ - 2)`. -/
theorem decides (A D : GPoly (GFrac (GFrac ℚ))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ A D) ↔
      integrateHexpHexp Hn Hd μ Hn₂ Hd₂ A D = true :=
  integrateHexpHexp_decides_concrete (R := ℚ) (fun _ ↦ rfl) Hn Hd μ hHn0 hHd0 hcop cert_η
    Hn₂ Hd₂ μ₂ hHn20 hHd20 hcop₂ cert_η₂ cert_ind A D hD0

/-- **`∫ t₁ t₂ dx` is not elementary** (a degenerate pair). -/
theorem prod_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    ¬HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁] D₁) :=
  fun h ↦ by
    have := (decides _ D₁ den₁).mp h
    rw [run₂] at this
    exact Bool.noConfusion this

/-- **`∫ (η₁ + η₂) t₁ t₂ dx` is elementary** (`= t₁ t₂`). -/
theorem prod_deriv_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (1 : ℚ[X])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv
      (C (algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hn) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Hd)) * X)
    letI : Differential K₃ := ratFuncOfDeriv hexpDeriv₂
    HasElementaryIntegral (val₃ (RatFunc ℚ) (RatFunc (RatFunc ℚ)) K₃ [Z, T₁c] D₁) :=
  (decides _ D₁ den₁).mpr run₄

end Tower.HexpDegenerateExamples
