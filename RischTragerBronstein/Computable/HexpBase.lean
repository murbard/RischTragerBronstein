import RischTragerBronstein.Computable.IntegrateHyperexpW
import RischTragerBronstein.Computable.ExpReduce

/-!
# A general hyperexponential `t′ = η t`, `η = Gn / Gd ∈ R(x)`, as the base of a tower

The analogues of `ηa`, `toPoly_expW_In`, `ops₂e`, `exp_pow_not_in_base` for the code
`hexpW Gn Gd` of `t′ = η t`, with `η` an arbitrary rational function certified by
`hyperexpMonomialCheck` to make `t` a monomial. These are the ingredients for putting a general
hyperexponential under a logarithm (`log` over `exp (arctan x)`, …).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The operations of `R(x)(t)`, `t′ = η t`. -/
def ops₂h (Gn Gd : CPoly R) : COps (GFrac (GFrac R)) := (ops₁g R).monomial (hexpW Gn Gd)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
  (Gn Gd : CPoly R)

/-- The value of `η = Gn / Gd` in `K₁`. -/
noncomputable abbrev ηh : K₁ := φ ((CPoly.toPoly Gn).map ι) / φ ((CPoly.toPoly Gd).map ι)

lemma toPoly_hexpW_In :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpW Gn Gd) = C (ηh ι Gn Gd) * X := by
  have hexp : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (hexpW Gn Gd) =
      C ((M₁In (K₁ := K₁) ι h0 hD).sem (ops₁g R).zero) +
        X * (C ((M₁In (K₁ := K₁) ι h0 hD).sem (Gn, Gd)) + X * 0) := rfl
  rw [hexp, CField.sem_zero, sem_M₁In, C_0, zero_add, mul_zero, add_zero, mul_comm]
  rfl

/-- The model of `R(x)(t)` in `K₂`, from the one-level hypotheses. -/
noncomputable def M₂H (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Gn Gd) * X) P) :
    CField (GFrac (GFrac R)) K₂ (ops₂h Gn Gd) :=
  CField.monomialIn (M₁In (K₁ := K₁) ι h0 hD) (hexpW Gn Gd) K₂ fun P ↦ by
    rw [toPoly_hexpW_In]; exact hD₂ P

lemma sem_M₂H (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Gn Gd) * X) P)
    (q : GFrac (GFrac R)) :
    (M₂H (K₂ := K₂) ι h0 hD Gn Gd hD₂).sem q =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) q.1) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) q.2) := rfl

variable [CPoly.HasRatRoots R]

include hD in
/-- `t^r` is not in `S(x)` for `r > 0`: `e′ ≠ r η e` for `e ≠ 0`. -/
lemma hexp_pow_not_in_base {μ : CPoly R} (hGn0 : CPoly.toPoly Gn ≠ 0)
    (hGd0 : CPoly.toPoly Gd ≠ 0) (hcop : IsCoprime (CPoly.toPoly Gn) (CPoly.toPoly Gd))
    (hcert : CPoly.hyperexpMonomialCheck Gn Gd μ = true) :
    ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ - r * ηh ι Gn Gd * e ≠ 0 := by
  intro r hr e he h'
  refine he (CPoly.hyperexpW_homogeneous (K := K₁) ι hD hGn0 hGd0 hcop hcert r
    (by exact_mod_cast hr.ne') e ?_)
  rw [C_eq_intCast, map_intCast, Int.cast_natCast]
  linear_combination h'

/-- The scaled coefficient `c η` as a code: `(smul c Gn, Gd)`. -/
lemma ev_hexpCoeff (c : R) :
    φ ((CPoly.toPoly (CPoly.smul c Gn)).map ι) / φ ((CPoly.toPoly Gd).map ι) =
      φ (C (ι c)) * ηh ι Gn Gd := by
  rw [CPoly.toPoly_smul, Polynomial.map_mul, map_C, map_mul, ηh, mul_div_assoc]

end Tower
