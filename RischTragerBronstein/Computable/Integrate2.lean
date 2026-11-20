import RischTragerBronstein.Computable.IntegrateHyperexpW

/-!
# One entry point for all decided towers of height two over `R(x)`

`Tower2Spec R` describes a tower `R(x)(t)` by the data of its monomial: a primitive `t′ = η`
(`log`, `arctan`, …), an exponential `t = exp a(x)` with `a ∈ R[x]`, or a hyperexponential
`t′ = η t` with `η ∈ R(x)` arbitrary (certified monomial). `certs` are the executable side
conditions, `code` the code of `t′`, `integrate2` dispatches, and `integrate2_decides` states that
for every shape with valid certificates and every `A / D ∈ R(x)(t)`, the answer is `true` iff
`A / D` has an elementary integral.
-/

open Polynomial

namespace Tower

open Differential CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- The decided shapes of height two. -/
inductive Tower2Spec (R : Type*) [Field R]
  /-- `t′ = η = En / Ed`, with `Iη` the rational integration data of `η` -/
  | prim (En Ed : CPoly R) (Iη : RationalIntegral R)
  /-- `t = exp a(x)`, `a ∈ R[x]` -/
  | exp (a : CPoly R)
  /-- `t′ = η t`, `η = Gn / Gd ∈ R(x)` arbitrary, `μ` an annihilator of the residues of `η` -/
  | hyperexp (Gn Gd μ : CPoly R)

namespace Tower2Spec

/-- `gcd (p, q)` is a nonzero constant. -/
def coprimeCheck (p q : CPoly R) : Bool := (trim (egcd p q).1).length == 1

/-- The executable side conditions. -/
def certs [HasRatRoots R] : Tower2Spec R → Bool
  | prim En Ed Iη => rationalCheck En Ed Iη && !isZero Iη.r
  | exp a => decide (trim (deriv a) ≠ [])
  | hyperexp Gn Gd μ =>
    !isZero Gn && !isZero Gd && coprimeCheck Gn Gd && hyperexpMonomialCheck Gn Gd μ

/-- The code of `t′`. -/
def code : Tower2Spec R → GPoly (GFrac R)
  | prim En Ed _ => [(En, Ed)]
  | exp a => expW a
  | hyperexp Gn Gd _ => hexpW Gn Gd

/-- The integrator. -/
def integrate2 [HasRatRoots R] [HasNatTest R] : Tower2Spec R → GPoly (GFrac R) →
    GPoly (GFrac R) → Bool
  | prim En Ed Iη, A, D => integratePrim En Ed Iη A D
  | exp a, A, D => integrateExp a A D
  | hyperexp Gn Gd μ, A, D => integrateHyperexpW Gn Gd μ A D

end Tower2Spec

variable [CharZero R]

theorem coprimeCheck_sound {p q : CPoly R} (h : Tower2Spec.coprimeCheck p q = true) :
    IsCoprime (toPoly p) (toPoly q) := by
  rw [Tower2Spec.coprimeCheck, beq_iff_eq] at h
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp h
  obtain ⟨hγ0, hg⟩ := trim_singleton hγ
  have hbez := egcd_spec p q
  rw [hg] at hbez
  refine ⟨C γ⁻¹ * toPoly (egcd p q).2.1, C γ⁻¹ * toPoly (egcd p q).2.2, ?_⟩
  have : C γ⁻¹ * C γ = (1 : R[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  linear_combination C γ⁻¹ * hbez + this

variable [Differential R] [HasRatRoots R] [HasNatTest R]

/-- **Every decided height-two tower, one theorem.** -/
theorem integrate2_decides (h0 : ∀ r : R, r′ = 0) (s : Tower2Spec R) (hc : s.certs = true)
    (A D : GPoly (GFrac R)) (hD0 : GPoly.isZero (ops₁g R) D = false) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) s.code)
    HasElementaryIntegral (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R))
        (GPoly.toPoly (M₁g h0) A) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) D)) ↔
      s.integrate2 A D = true := by
  have hD0' : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      GPoly.toPoly (M₁g h0) D ≠ 0 := by
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    intro h
    rw [← GPoly.isZero_iff (M₁g h0)] at h
    rw [h] at hD0
    exact absurd hD0 (by decide)
  cases s with
  | prim En Ed Iη =>
    simp only [Tower2Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact integratePrim_decides h0 En Ed Iη hc.1 hc.2 A D hD0'
  | exp a =>
    simp only [Tower2Spec.certs, decide_eq_true_eq] at hc
    exact integrateExp_decides h0 a hc A D hD0'
  | hyperexp Gn Gd μ =>
    simp only [Tower2Spec.certs, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    refine integrateHyperexpW_decides h0 Gn Gd μ ?_ ?_ (coprimeCheck_sound h3) h4 A D hD0'
    · intro h; rw [← isZero_iff] at h; rw [h] at h1; exact absurd h1 (by decide)
    · intro h; rw [← isZero_iff] at h; rw [h] at h2; exact absurd h2 (by decide)

end Tower

-- the certificates of `log x`, `eˣ`, `exp (arctan x)` over `ℚ`
#eval (Tower.Tower2Spec.hyperexp ([1] : CPoly ℚ) [1, 0, 1]
  (Tower.hexpMu [1] [1, 0, 1])).certs
#eval (Tower.Tower2Spec.exp ([0, 1] : CPoly ℚ)).certs
