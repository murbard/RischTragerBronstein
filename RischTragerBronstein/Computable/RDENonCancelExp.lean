import RischTragerBronstein.Computable.RDENonCancelModel
import RischTragerBronstein.Computable.ExpReduce
import RischTragerBronstein.RDE.ExponentialDenominatorPoly

/-!
# The non-cancellation Risch equation over `R(x)(exp a₁)`, as a decision on codes

`y′ + g y = A / D` in `K₂ = K₁(t₁)`, `t₁ = exp a₁`, with `g ∈ R(x)[t₁]` of positive degree. Write
`D = t₁^m D₁` (`splitX`); then `y = Y / (t₁^m D₁)` (`rde_denominator_exp_poly`, provided the
constant term `g₀` of `g` satisfies `g₀ - r a₁′ ≠ 0` as a polynomial for `r > 0`), and `Y` solves
`D₁ Y′ + ((g - m a₁′) D₁ - D₁′) Y = A D₁`, decided by `GPoly.rdeNC`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The constant `m a₁′` as a code of `R(x)[t₁]`. -/
def mEta (a₁ : CPoly R) (m : ℕ) : GPoly (GFrac R) := [(CPoly.smul (m : R) (CPoly.deriv a₁), [1])]

/-- **The non-cancellation solver over `R(x)(exp a₁)`**: `y = Y / (t₁^m D₁)`. -/
def rdeNCExp (a₁ : CPoly R) (g A D : GPoly (GFrac R)) : Option (GPoly (GFrac R)) :=
  let sp := GPoly.splitX (ops₁g R) D
  GPoly.rdeNC (ops₁g R) (expW a₁) (GPoly.sub (ops₁g R) g (mEta a₁ sp.1)) A sp.2

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

lemma toPoly_mEta (a₁ : CPoly R) (m : ℕ) :
    GPoly.toPoly 𝓜₁ (mEta a₁ m) = C ((m : K₁) * ηa ι a₁) := by
  rw [mEta, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, sem_M₁In]
  congr 1
  rw [CPoly.ev, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_mul, map_C, map_mul]
  simp [CPoly.toPoly, ηa]

/-- **Soundness.** -/
theorem rdeNCExp_sound (a₁ : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a₁) * X) P)
    (g A D : GPoly (GFrac R)) (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) {Y : GPoly (GFrac R)}
    (h : rdeNCExp a₁ g A D = some Y) :
    (φ₂ (GPoly.toPoly 𝓜₁ Y) / φ₂ (GPoly.toPoly 𝓜₁ D))′ +
        φ₂ (GPoly.toPoly 𝓜₁ g) * (φ₂ (GPoly.toPoly 𝓜₁ Y) / φ₂ (GPoly.toPoly 𝓜₁ D)) =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D) := by
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ (expW a₁)) P := fun P ↦ by
    rw [toPoly_expW_In]; exact hD₂ P
  have hsp := GPoly.toPoly_splitX 𝓜₁ D
  simp only [rdeNCExp] at h
  generalize GPoly.splitX (ops₁g R) D = sp at h hsp
  have hD₁0 : GPoly.toPoly 𝓜₁ sp.2 ≠ 0 := fun h0' ↦ hD0 (by rw [hsp, h0', mul_zero])
  have hs := GPoly.rdeNC_sound 𝓜₁ (expW a₁) _ A sp.2 hDW h
  rw [GPoly.toPoly_sub, toPoly_mEta] at hs
  have hφD₁ : φ₂ (GPoly.toPoly 𝓜₁ sp.2) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD₁0
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hXm : (φ₂ (X : K₁[X]) ^ sp.1)′ = φ₂ (C ((sp.1 : K₁) * ηa ι a₁)) * φ₂ X ^ sp.1 := by
    rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
  have := congrArg φ₂ hs
  simp only [map_add, map_mul, map_sub] at this
  rw [hsp, map_mul, map_pow, Derivation.leibniz_div, deriv_algebraMap, Derivation.leibniz, hXm,
    deriv_algebraMap]
  simp only [smul_eq_mul]
  have hCm : φ₂ (C ((sp.1 : K₁) * ηa ι a₁)) = φ₂ (C (sp.1 : K₁)) * φ₂ (C (ηa ι a₁)) := by
    rw [C_mul, map_mul]
  rw [hCm]
  field_simp
  linear_combination this

/-- **Completeness**, when `g₀ - r a₁′` is never a logarithmic derivative in `K₁` (`r > 0`). -/
theorem rdeNCExp_complete (a₁ : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a₁) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (g A D : GPoly (GFrac R)) (hg : 1 ≤ (GPoly.toPoly 𝓜₁ g).natDegree)
    (hg₀ : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 →
      e′ + ((GPoly.toPoly 𝓜₁ g).coeff 0 - r * ηa ι a₁) * e ≠ 0)
    (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) (y : K₂)
    (hy : y′ + φ₂ (GPoly.toPoly 𝓜₁ g) * y =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D)) :
    (rdeNCExp a₁ g A D).isSome = true := by
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ (expW a₁)) P := fun P ↦ by
    rw [toPoly_expW_In]; exact hD₂ P
  have hnorm' := normal_of_hconst (ηa ι a₁) hD₂ hconst
  have hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree := fun P ↦ by
    rw [hD₂]; exact natDegree_implicitDeriv_C_mul_X_le _ P
  have hsp := GPoly.toPoly_splitX 𝓜₁ D
  have hXD₁ := GPoly.not_X_dvd_splitX 𝓜₁ D hD0
  simp only [rdeNCExp]
  generalize GPoly.splitX (ops₁g R) D = sp at hsp hXD₁
  have hD₁0 : GPoly.toPoly 𝓜₁ sp.2 ≠ 0 := fun h0' ↦ hD0 (by rw [hsp, h0', mul_zero])
  rw [hsp, map_mul, map_pow] at hy
  obtain ⟨Y, -, hYode⟩ := rde_denominator_exp_poly (K := K₂) (ηa ι a₁) hD₂ hnorm' _ sp.1
    (fun r hr ↦ hg₀ r (by omega)) _ _ hXD₁ y hy
  have hg' : 1 ≤ (GPoly.toPoly 𝓜₁ (GPoly.sub (ops₁g R) g (mEta a₁ sp.1))).natDegree := by
    rw [GPoly.toPoly_sub, toPoly_mEta, natDegree_sub_C]; exact hg
  have hg'0 : GPoly.toPoly 𝓜₁ (GPoly.sub (ops₁g R) g (mEta a₁ sp.1)) ≠ 0 := fun h0' ↦ by
    rw [h0', natDegree_zero] at hg'; omega
  obtain ⟨Y', hY'⟩ := GPoly.rdeNC_complete 𝓜₁ (expW a₁) _ A sp.2 hDW hder hg' hg'0 hD₁0 Y (by
    rw [GPoly.toPoly_sub, toPoly_mEta]
    exact hYode)
  rw [hY']
  rfl

end Tower
