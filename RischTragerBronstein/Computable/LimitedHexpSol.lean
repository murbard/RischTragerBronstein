import RischTragerBronstein.Computable.LimitedHexpW
import RischTragerBronstein.Computable.ReduceF2
import RischTragerBronstein.Computable.DerivHexpSol

import RischTragerBronstein.Computable.LimitedExpSol
/-!
# Limited integration in `R(x)(t)`, `t′ = η t` with `η ∈ R(x)` arbitrary: constant and antiderivative

`Tower.limitedHexpSol Hn Hd μ G W`: the constant `c` (from `limitedHexpW`) and an antiderivative of
`G - c W` (from `derivHexpSol`). Sound and complete (`W` not a derivative).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- `G - c W` as a fraction code of `R(x)(exp a)` with non-zero denominator. -/
def subSmulCodeH (Hn Hd : CPoly R) (G W : GFrac (GFrac R)) (c : R) : GFrac (GFrac R) :=
  reduceF₂ ((ops₂h Hn Hd).add G ((ops₂h Hn Hd).neg ((ops₂h Hn Hd).mul (constCode₂ c) W)))

/-- Limited integration with parameter function `W`: the constant and the antiderivative. -/
def limitedHexpSol (Hn Hd μ : CPoly R) (G W : GFrac (GFrac R)) : Option (R × GFrac (GFrac R)) :=
  match limitedHexpW Hn Hd μ G.1 G.2 W.1 W.2 with
  | none => none
  | some c =>
    (derivHexpSol Hn Hd μ (subSmulCodeH Hn Hd G W c).1 (subSmulCodeH Hn Hd G W c).2).map
      fun y ↦ (c, reduceF₂ y)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [DecidableEq S]
variable [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [CPoly.HasRatRoots R] [HasNatTest R]
variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
local notation "𝓜₁" => M₁In (K₁ := K₁) ι h0 hD

include h0 hD

lemma sem_constCode₂_H {Hn Hd : CPoly R} (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (c : R) : (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem (constCode₂ c) = φ₂ (C (φ (C (ι c)))) := by
  have h1 : GPoly.toPoly 𝓜₁ [(ops₁g R).one] = 1 := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1]
  rw [sem_M₂H, constCode₂, h1, map_one, div_one, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero,
    add_zero, sem_M₁In]
  simp [CPoly.ev, CPoly.toPoly]

lemma subSmulCodeH_spec {Hn Hd : CPoly R} (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (G W : GFrac (GFrac R)) (c : R) :
    GPoly.toPoly 𝓜₁ (subSmulCodeH Hn Hd G W c).2 ≠ 0 ∧
      (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem (subSmulCodeH Hn Hd G W c) =
        (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem G -
          φ₂ (C (φ (C (ι c)))) * (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem W := by
  have hsem : (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem ((ops₂h Hn Hd).add G ((ops₂h Hn Hd).neg
      ((ops₂h Hn Hd).mul (constCode₂ c) W))) = (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem G -
        φ₂ (C (φ (C (ι c)))) * (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem W := by
    rw [CField.sem_add, CField.sem_neg, CField.sem_mul, sem_constCode₂_H]
    ring
  rw [← hsem]
  unfold subSmulCodeH
  obtain ⟨hden, hval⟩ := reduceF₂_spec (K₁ := K₁) (K₂ := K₂) ι h0 hD
    ((ops₂h Hn Hd).add G ((ops₂h Hn Hd).neg ((ops₂h Hn Hd).mul (constCode₂ c) W)))
  refine ⟨hden, ?_⟩
  rw [sem_M₂H, sem_M₂H]
  exact hval

/-- **Soundness.** -/
theorem limitedHexpSol_sound (Hn Hd μ : CPoly R) (hHd0 : CPoly.toPoly Hd ≠ 0)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (G W : GFrac (GFrac R)) {c : R} {y : GFrac (GFrac R)}
    (h : limitedHexpSol Hn Hd μ G W = some (c, y)) :
    ((M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem y)′ =
      (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem G -
        φ₂ (C (φ (C (ι c)))) * (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem W := by
  simp only [limitedHexpSol] at h
  cases hc : limitedHexpW Hn Hd μ G.1 G.2 W.1 W.2 with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c' =>
    rw [hc] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨y', hsol, rfl, rfl⟩ := h
    obtain ⟨hden, hsem⟩ := subSmulCodeH_spec (K₂ := K₂) ι h0 hD hD₂ G W c'
    rw [← hsem, sem_M₂H]
    obtain ⟨-, hred⟩ := reduceF₂_spec (K₁ := K₁) (K₂ := K₂) ι h0 hD y'
    rw [sem_M₂H, hred, ← sem_M₂H ι h0 hD Hn Hd hD₂]
    exact derivHexpSol_sound (K₂ := K₂) ι h0 hD Hn Hd μ hHd0 hD₂ hconst _ _ hden hsol

/-- **Completeness.** -/
theorem limitedHexpSol_complete (Hn Hd μ : CPoly R)
    (hHn0 : CPoly.toPoly Hn ≠ 0) (hHd0 : CPoly.toPoly Hd ≠ 0)
    (hcop : IsCoprime (CPoly.toPoly Hn) (CPoly.toPoly Hd))
    (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (G W : GFrac (GFrac R)) (hGd : GPoly.toPoly 𝓜₁ G.2 ≠ 0) (hWd : GPoly.toPoly 𝓜₁ W.2 ≠ 0)
    (hW : isDerivHexp Hn Hd μ W.1 W.2 = false) (c : S) (z : K₂)
    (hz : z′ = (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem G -
      φ₂ (C (φ (C c))) * (M₂H (K₂ := K₂) ι h0 hD Hn Hd hD₂).sem W) :
    ∃ (c' : R) (y : GFrac (GFrac R)), limitedHexpSol Hn Hd μ G W = some (c', y) ∧ ι c' = c := by
  obtain ⟨c', hc', hιc⟩ := limitedHexpW_complete (K₂ := K₂) ι h0 hD Hn Hd μ hHn0 hHd0 hcop hcert hD₂ hconst G.1 G.2 W.1 W.2
    hGd hWd hW c z (by rw [hz, sem_M₂H, sem_M₂H])
  obtain ⟨hden, hsem⟩ := subSmulCodeH_spec (K₂ := K₂) ι h0 hD hD₂ G W c'
  have hz' : z′ = φ₂ (GPoly.toPoly 𝓜₁ (subSmulCodeH Hn Hd G W c').1) /
      φ₂ (GPoly.toPoly 𝓜₁ (subSmulCodeH Hn Hd G W c').2) := by
    rw [← sem_M₂H ι h0 hD Hn Hd hD₂, hsem, hιc, hz]
  have hder := isDerivHexp_complete (K₂ := K₂) ι h0 hD Hn Hd μ hHn0 hHd0 hcop hcert hD₂ hconst _ _ hden z hz'
  rw [← derivHexpSol_isSome] at hder
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hder
  refine ⟨c', reduceF₂ y, ?_, hιc⟩
  simp only [limitedHexpSol, hc', hy, Option.map_some]

end Tower
