import RischTragerBronstein.Computable.HexpSpecialBound
import RischTragerBronstein.Computable.RDENonCancelExp
import RischTragerBronstein.Computable.DerivExpSol

/-!
# The non-cancellation Risch equation over `R(x)(t₁)`, `t₁′ = η t₁` general hyperexponential

`y′ + g y = A / D` in `K₂ = K₁(t₁)` with `g ∈ R(x)[t₁]` of positive degree and `t₁⁰` coefficient
`z a₀′`. Write `D = t₁^m D₁`; then `y = Y / (t₁^{n₀} D₁)` with `n₀ = specialBoundH Hn Hd a₀ z m`,
and `Y` solves `D₁ Y′ + ((g - n₀ η) D₁ - D₁′) Y = A t₁^{n₀-m} D₁`, decided by `GPoly.rdeNC`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasNatTest R]

/-- The constant `m η` as a code of `R(x)[t₁]`. -/
def mEtaH (Hn Hd : CPoly R) (m : ℕ) : GPoly (GFrac R) := [(CPoly.smul (m : R) Hn, Hd)]

/-- **The non-cancellation solver over `R(x)(t₁)`** with the special bound. -/
def rdeNCHexpB (Hn Hd : CPoly R) (a₀ : GFrac R) (z : ℤ) (g A D : GPoly (GFrac R)) :
    Option (GPoly (GFrac R)) :=
  let sp := GPoly.splitX (ops₁g R) D
  let n₀ := specialBoundH Hn Hd a₀ z sp.1
  GPoly.rdeNC (ops₁g R) (hexpW Hn Hd) (GPoly.sub (ops₁g R) g (mEtaH Hn Hd n₀))
    (GPoly.mul (ops₁g R) A (GPoly.monomial (ops₁g R) (n₀ - sp.1) (ops₁g R).one)) sp.2

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [HasNatTest R] [Field S]
variable [CPoly.HasRatRoots R] [DecidableEq S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
local notation "𝓜₁" => M₁In (K₁ := K₁) ι h0 hD

include h0 hD

lemma toPoly_mEtaH (Hn Hd : CPoly R) (m : ℕ) :
    GPoly.toPoly 𝓜₁ (mEtaH Hn Hd m) = C ((m : K₁) * ηh ι Hn Hd) := by
  rw [mEtaH, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, sem_M₁In]
  congr 1
  rw [CPoly.ev, CPoly.toPoly_smul, Polynomial.map_mul, map_C, map_mul, ηh, mul_div_assoc,
    map_natCast, C_eq_natCast, map_natCast]

/-- The `t₁⁰` coefficient of `z a′` is `z a₀′`, `a₀` the (normalised) `t₁⁰` coefficient of `a`. -/
lemma coeff_zero_smul_derivT_hexpW (Hn Hd : CPoly R) (a : GPoly (GFrac R)) (z : ℤ) :
    (GPoly.toPoly 𝓜₁ (GPoly.smul (ops₁g R) (constZ z)
      (GPoly.derivT (ops₁g R) (hexpW Hn Hd) a))).coeff 0 =
      (z : K₁) * (CPoly.ev K₁ ι (normFrac (GPoly.coeffAt (ops₁g R) a 0)))′ := by
  rw [GPoly.toPoly_smul, coeff_C_mul, sem_constZ, GPoly.toPoly_derivT, toPoly_hexpW_In,
    coeff_implicitDeriv_C_mul_X, ev_normFrac, ← sem_M₁In ι h0 hD, GPoly.sem_coeffAt]
  simp

/-- **Soundness.** -/
theorem rdeNCHexpB_sound (Hn Hd : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P) (a₀ : GFrac R) (z : ℤ)
    (g A D : GPoly (GFrac R)) (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) {Y : GPoly (GFrac R)}
    (h : rdeNCHexpB Hn Hd a₀ z g A D = some Y) :
    (φ₂ (GPoly.toPoly 𝓜₁ Y) / (φ₂ X ^ specialBoundH Hn Hd a₀ z (GPoly.splitX (ops₁g R) D).1 *
        φ₂ (GPoly.toPoly 𝓜₁ (GPoly.splitX (ops₁g R) D).2)))′ +
      φ₂ (GPoly.toPoly 𝓜₁ g) * (φ₂ (GPoly.toPoly 𝓜₁ Y) /
        (φ₂ X ^ specialBoundH Hn Hd a₀ z (GPoly.splitX (ops₁g R) D).1 *
          φ₂ (GPoly.toPoly 𝓜₁ (GPoly.splitX (ops₁g R) D).2))) =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D) := by
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ (hexpW Hn Hd)) P := fun P ↦ by
    rw [toPoly_hexpW_In]; exact hD₂ P
  have hsp := GPoly.toPoly_splitX 𝓜₁ D
  simp only [rdeNCHexpB] at h
  generalize GPoly.splitX (ops₁g R) D = sp at h hsp ⊢
  have hge := le_specialBoundH Hn Hd a₀ z sp.1
  generalize specialBoundH Hn Hd a₀ z sp.1 = n₀ at h hge ⊢
  have hD₁0 : GPoly.toPoly 𝓜₁ sp.2 ≠ 0 := fun h0' ↦ hD0 (by rw [hsp, h0', mul_zero])
  have hs := GPoly.rdeNC_sound 𝓜₁ (hexpW Hn Hd) _ _ sp.2 hDW h
  rw [GPoly.toPoly_sub, toPoly_mEtaH ι h0 hD, GPoly.toPoly_mul, toPoly_monomial_one ι h0 hD] at hs
  have hφD₁ : φ₂ (GPoly.toPoly 𝓜₁ sp.2) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD₁0
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hXn : (φ₂ (X : K₁[X]) ^ n₀)′ = φ₂ (C ((n₀ : K₁) * ηh ι Hn Hd)) * φ₂ X ^ n₀ := by
    rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
  have := congrArg φ₂ hs
  simp only [map_add, map_mul, map_sub, map_pow] at this
  rw [hsp, map_mul, map_pow, Derivation.leibniz_div, Derivation.leibniz, hXn, deriv_algebraMap,
    deriv_algebraMap]
  simp only [smul_eq_mul]
  have hCm : φ₂ (C ((n₀ : K₁) * ηh ι Hn Hd)) = φ₂ (C (n₀ : K₁)) * φ₂ (C (ηh ι Hn Hd)) := by
    rw [C_mul, map_mul]
  rw [hCm]
  have hpow : φ₂ (X : K₁[X]) ^ n₀ = φ₂ X ^ (n₀ - sp.1) * φ₂ X ^ sp.1 := by
    rw [← pow_add, Nat.sub_add_cancel hge]
  rw [hpow]
  field_simp
  linear_combination this

/-- **Completeness**, when the `t₁⁰` coefficient of `g` is `z a₀′`. -/
theorem rdeNCHexpB_complete (Hn Hd μ : CPoly R) (hHn0 : CPoly.toPoly Hn ≠ 0)
    (hHd0 : CPoly.toPoly Hd ≠ 0) (hcop : IsCoprime (CPoly.toPoly Hn) (CPoly.toPoly Hd))
    (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (a₀ : GFrac R) (ha₀ : CPoly.toPoly a₀.2 ≠ 0) (z : ℤ)
    (g A D : GPoly (GFrac R)) (hg : 1 ≤ (GPoly.toPoly 𝓜₁ g).natDegree)
    (hg₀ : (GPoly.toPoly 𝓜₁ g).coeff 0 = (z : K₁) * (CPoly.ev K₁ ι a₀)′)
    (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) (y : K₂)
    (hy : y′ + φ₂ (GPoly.toPoly 𝓜₁ g) * y =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D)) :
    (rdeNCHexpB Hn Hd a₀ z g A D).isSome = true := by
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ (hexpW Hn Hd)) P := fun P ↦ by
    rw [toPoly_hexpW_In]; exact hD₂ P
  have hnorm' := normal_of_hconst (ηh ι Hn Hd) hD₂ hconst
  have hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree := fun P ↦ by
    rw [hD₂]; exact natDegree_implicitDeriv_C_mul_X_le _ P
  have hsp := GPoly.toPoly_splitX 𝓜₁ D
  have hXD₁ := GPoly.not_X_dvd_splitX 𝓜₁ D hD0
  simp only [rdeNCHexpB]
  generalize GPoly.splitX (ops₁g R) D = sp at hsp hXD₁
  have hge := le_specialBoundH Hn Hd a₀ z sp.1
  have hspec := specialBoundH_spec (K₁ := K₁) ι hD Hn Hd μ hHn0 hHd0 hcop hcert a₀ ha₀ z sp.1
  generalize specialBoundH Hn Hd a₀ z sp.1 = n₀ at hge hspec ⊢
  have hD₁0 : GPoly.toPoly 𝓜₁ sp.2 ≠ 0 := fun h0' ↦ hD0 (by rw [hsp, h0', mul_zero])
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hy' : y′ + φ₂ (GPoly.toPoly 𝓜₁ g) * y =
      φ₂ (GPoly.toPoly 𝓜₁ A * X ^ (n₀ - sp.1)) / (φ₂ X ^ n₀ * φ₂ (GPoly.toPoly 𝓜₁ sp.2)) := by
    rw [hy, hsp, map_mul, map_pow, map_mul, map_pow]
    have hpow : φ₂ (X : K₁[X]) ^ n₀ = φ₂ X ^ (n₀ - sp.1) * φ₂ X ^ sp.1 := by
      rw [← pow_add, Nat.sub_add_cancel hge]
    rw [hpow]
    have := (map_ne_zero_iff _ hinj).mpr hD₁0
    field_simp
  obtain ⟨Y, -, hYode⟩ := rde_denominator_exp_poly (K := K₂) (ηh ι Hn Hd) hD₂ hnorm' _ n₀
    (fun r hr e he ↦ by rw [hg₀]; exact hspec r hr e he) _ _ hXD₁ y hy'
  have hg' : 1 ≤ (GPoly.toPoly 𝓜₁ (GPoly.sub (ops₁g R) g (mEtaH Hn Hd n₀))).natDegree := by
    rw [GPoly.toPoly_sub, toPoly_mEtaH ι h0 hD, natDegree_sub_C]; exact hg
  have hg'0 : GPoly.toPoly 𝓜₁ (GPoly.sub (ops₁g R) g (mEtaH Hn Hd n₀)) ≠ 0 := fun h0' ↦ by
    rw [h0', natDegree_zero] at hg'; omega
  obtain ⟨Y', hY'⟩ := GPoly.rdeNC_complete 𝓜₁ (hexpW Hn Hd)
    (GPoly.sub (ops₁g R) g (mEtaH Hn Hd n₀))
    (GPoly.mul (ops₁g R) A (GPoly.monomial (ops₁g R) (n₀ - sp.1) (ops₁g R).one)) sp.2 hDW hder
    hg' hg'0 hD₁0 Y (by
    rw [GPoly.toPoly_sub, toPoly_mEtaH ι h0 hD, GPoly.toPoly_mul, toPoly_monomial_one ι h0 hD]
    exact hYode)
  rw [hY']
  rfl

end Tower
