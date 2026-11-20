import RischTragerBronstein.Computable.RDENonCancel
import RischTragerBronstein.Computable.RDEPrimTop
import RischTragerBronstein.Computable.RDEExp
import RischTragerBronstein.RDE.PrimitiveDenominator

/-!
# The non-cancellation Risch equation over `R(x)(t₁)`, as a decision on codes

`y′ + g y = A / D` in `K₂ = K₁(t₁)` with `g ∈ R(x)[t₁]` of positive degree (a code
`GPoly (GFrac R)`), `t₁` primitive or exponential (code `w` of `t₁′`). Every prime of `K₁[X]` is
normal, so `y = Y / D` (`rde_denominator_regular`), and `GPoly.rdeNC` decides.

* `rdeNC_sound_model`: a returned `Y` gives the solution `Y / D`;
* `rdeNC_complete_model`: a solution `y ∈ K₂` forces `rdeNC` to succeed.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R]

/-- The integer `z` as a constant code of `R(x)`. -/
def constZ (z : ℤ) : GFrac R := ([(z : R)], [1])

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
local notation "𝓜₁" => M₁In (K₁ := K₁) ι h0 hD

include h0 hD

lemma sem_constZ (z : ℤ) : (M₁In (K₁ := K₁) ι h0 hD).sem (constZ z) = (z : K₁) := by
  rw [sem_M₁In, constZ, CPoly.ev]
  simp [CPoly.toPoly]

/-- **Soundness**, for any tower step `w`. -/
theorem rdeNC_sound_model (w g A D : GPoly (GFrac R))
    (hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ w) P)
    (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) {Y : GPoly (GFrac R)}
    (h : GPoly.rdeNC (ops₁g R) w g A D = some Y) :
    (φ₂ (GPoly.toPoly 𝓜₁ Y) / φ₂ (GPoly.toPoly 𝓜₁ D))′ +
        φ₂ (GPoly.toPoly 𝓜₁ g) * (φ₂ (GPoly.toPoly 𝓜₁ Y) / φ₂ (GPoly.toPoly 𝓜₁ D)) =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D) := by
  have hs := GPoly.rdeNC_sound 𝓜₁ w g A D hDW h
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφD : φ₂ (GPoly.toPoly 𝓜₁ D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have := congrArg φ₂ hs
  simp only [map_add, map_mul, map_sub] at this
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap]
  simp only [smul_eq_mul]
  field_simp
  linear_combination this

/-- **Completeness**, for any tower step `w` with normal primes and `deg P′ ≤ deg P`. -/
theorem rdeNC_complete_model (w g A D : GPoly (GFrac R))
    (hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ w) P)
    (hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′)
    (hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree)
    (hg : 1 ≤ (GPoly.toPoly 𝓜₁ g).natDegree) (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) (y : K₂)
    (hy : y′ + φ₂ (GPoly.toPoly 𝓜₁ g) * y =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D)) :
    (GPoly.rdeNC (ops₁g R) w g A D).isSome = true := by
  obtain ⟨Y, hY⟩ := rde_denominator_regular (K := K₂) hnorm (φ₂ (GPoly.toPoly 𝓜₁ g))
    (fun p hp ↦ algebraMap_mem_regularAt hp.prime _) _ _ hD0 y hy
  have hpoly := rde_poly_of_rde (K := K₂) (GPoly.toPoly 𝓜₁ g) _ _ Y hD0 y hY hy
  have hg0 : GPoly.toPoly 𝓜₁ g ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hg; omega
  obtain ⟨Y', hY'⟩ := GPoly.rdeNC_complete 𝓜₁ w g A D hDW hder hg hg0 hD0 Y hpoly
  rw [hY']
  rfl

end Tower
