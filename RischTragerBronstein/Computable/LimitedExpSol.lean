import RischTragerBronstein.Computable.LimitedExpW
import RischTragerBronstein.Computable.DerivExpSol

/-!
# Limited integration in `R(x)(exp a)`: the solver

`Tower.limitedExpSol a G W`: the constant `c` (from `limitedExpW`) and an antiderivative of
`G - c W` in `R(x)(exp a)` (from `derivExpSol`).

* `limitedExpSol_sound`: a returned `(c, y)` satisfies `y′ = G - c W`, in every model;
* `limitedExpSol_complete`: if `W` is not a derivative (`isDerivExp a W = false`) and `z′ = G - c W`
  has a solution over **any** extension of the constants, the solver succeeds with that constant.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- `G - c W` as a fraction code of `R(x)(exp a)` with non-zero denominator. -/
def subSmulCodeE (a : CPoly R) (G W : GFrac (GFrac R)) (c : R) : GFrac (GFrac R) :=
  normF₂ ((ops₂e a).add G ((ops₂e a).neg ((ops₂e a).mul (constCode₂ c) W)))

/-- Limited integration with parameter function `W`: the constant and the antiderivative. -/
def limitedExpSol (a : CPoly R) (G W : GFrac (GFrac R)) : Option (R × GFrac (GFrac R)) :=
  match limitedExpW a G.1 G.2 W.1 W.2 with
  | none => none
  | some c =>
    (derivExpSol a (subSmulCodeE a G W c).1 (subSmulCodeE a G W c).2).map fun y ↦ (c, y)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [DecidableEq S]
variable [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
local notation "𝓜₁" => M₁In (K₁ := K₁) ι h0 hD

include h0 hD

lemma sem_constCode₂_E {a : CPoly R} (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (c : R) : (M₂E (K₂ := K₂) ι h0 hD hD₂).sem (constCode₂ c) = φ₂ (C (φ (C (ι c)))) := by
  have h1 : GPoly.toPoly 𝓜₁ [(ops₁g R).one] = 1 := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1]
  rw [sem_M₂E, constCode₂, h1, map_one, div_one, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero,
    add_zero, sem_M₁In]
  simp [CPoly.ev, CPoly.toPoly]

lemma subSmulCodeE_spec {a : CPoly R} (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (G W : GFrac (GFrac R)) (c : R) :
    GPoly.toPoly 𝓜₁ (subSmulCodeE a G W c).2 ≠ 0 ∧
      (M₂E (K₂ := K₂) ι h0 hD hD₂).sem (subSmulCodeE a G W c) =
        (M₂E (K₂ := K₂) ι h0 hD hD₂).sem G -
          φ₂ (C (φ (C (ι c)))) * (M₂E (K₂ := K₂) ι h0 hD hD₂).sem W := by
  have hsem : (M₂E (K₂ := K₂) ι h0 hD hD₂).sem ((ops₂e a).add G ((ops₂e a).neg
      ((ops₂e a).mul (constCode₂ c) W))) = (M₂E (K₂ := K₂) ι h0 hD hD₂).sem G -
        φ₂ (C (φ (C (ι c)))) * (M₂E (K₂ := K₂) ι h0 hD hD₂).sem W := by
    rw [CField.sem_add, CField.sem_neg, CField.sem_mul, sem_constCode₂_E]
    ring
  rw [← hsem]
  unfold subSmulCodeE normF₂
  split_ifs with hz
  · have hz' := (GPoly.isZero_iff 𝓜₁ _).mp hz
    refine ⟨by simp [CField.sem_one], ?_⟩
    rw [sem_M₂E, sem_M₂E, hz']
    simp
  · exact ⟨fun h ↦ hz ((GPoly.isZero_iff 𝓜₁ _).mpr h), rfl⟩

/-- **Soundness.** -/
theorem limitedExpSol_sound (a : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (G W : GFrac (GFrac R)) {c : R} {y : GFrac (GFrac R)}
    (h : limitedExpSol a G W = some (c, y)) :
    ((M₂E (K₂ := K₂) ι h0 hD hD₂).sem y)′ =
      (M₂E (K₂ := K₂) ι h0 hD hD₂).sem G -
        φ₂ (C (φ (C (ι c)))) * (M₂E (K₂ := K₂) ι h0 hD hD₂).sem W := by
  simp only [limitedExpSol] at h
  cases hc : limitedExpW a G.1 G.2 W.1 W.2 with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c' =>
    rw [hc] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨y', hsol, rfl, rfl⟩ := h
    obtain ⟨hden, hsem⟩ := subSmulCodeE_spec (K₂ := K₂) ι h0 hD hD₂ G W c'
    rw [← hsem, sem_M₂E]
    exact derivExpSol_sound (K₂ := K₂) ι h0 hD a hD₂ hconst _ _ hden hsol

/-- **Completeness.** -/
theorem limitedExpSol_complete (a : CPoly R) (ha : CPoly.trim (CPoly.deriv a) ≠ [])
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (G W : GFrac (GFrac R)) (hGd : GPoly.toPoly 𝓜₁ G.2 ≠ 0) (hWd : GPoly.toPoly 𝓜₁ W.2 ≠ 0)
    (hW : isDerivExp a W.1 W.2 = false) (c : S) (z : K₂)
    (hz : z′ = (M₂E (K₂ := K₂) ι h0 hD hD₂).sem G -
      φ₂ (C (φ (C c))) * (M₂E (K₂ := K₂) ι h0 hD hD₂).sem W) :
    ∃ (c' : R) (y : GFrac (GFrac R)), limitedExpSol a G W = some (c', y) ∧ ι c' = c := by
  obtain ⟨c', hc', hιc⟩ := limitedExpW_complete (K₂ := K₂) ι h0 hD a ha hD₂ hconst G.1 G.2 W.1 W.2
    hGd hWd hW c z (by rw [hz, sem_M₂E, sem_M₂E])
  obtain ⟨hden, hsem⟩ := subSmulCodeE_spec (K₂ := K₂) ι h0 hD hD₂ G W c'
  have hz' : z′ = φ₂ (GPoly.toPoly 𝓜₁ (subSmulCodeE a G W c').1) /
      φ₂ (GPoly.toPoly 𝓜₁ (subSmulCodeE a G W c').2) := by
    rw [← sem_M₂E ι h0 hD hD₂, hsem, hιc, hz]
  have hder := isDerivExp_complete (K₂ := K₂) ι h0 hD a ha hD₂ hconst _ _ hden z hz'
  rw [← derivExpSol_isSome] at hder
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hder
  refine ⟨c', y, ?_, hιc⟩
  simp only [limitedExpSol, hc', hy, Option.map_some]

end Tower
