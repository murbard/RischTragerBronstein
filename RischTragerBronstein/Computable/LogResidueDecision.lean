import RischTragerBronstein.Computable.PrimResidueStrong
import RischTragerBronstein.Computable.NormCoeff
import RischTragerBronstein.Computable.GResidueTest
import RischTragerBronstein.Computable.PrimPolyExample
import RischTragerBronstein.Liouville.PrimitiveConstants
import RischTragerBronstein.Liouville.HermitePrimitive

/-!
# Simple poles in `log x`: decided executably

In `ℚ(x)(t)`, `t = log x`, with the computable model `Tower.M₁` of `ℚ(x)`: for codes `b, s` of
polynomials in `t` over `ℚ(x)`, `s` squarefree, `deg b < deg s`,

  `b / s` has an elementary integral  **iff**  `GPoly.residueCheck ops₁ [invX] b s = true`.

Both directions are proved, with no assumption on constants; the check is a Bézout computation, a
few polynomial products and one division with remainder over `ℚ(x)` — no resultants, no
factorisation, no algebraic numbers, even when the residues are irrational (`logResidue_decides`).
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Tower

section Generic

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

/-- `η = 1 / x`, numerator. -/
def logEn : CPoly R := [1]
/-- `η = 1 / x`, denominator. -/
def logEd : CPoly R := [0, 1]
/-- The code of `1 / x`. -/
def invXg : GFrac R := ([1], [0, 1])

variable (R) in
/-- Operations of `R(x)`: fractions of polynomials, every result reduced by `CPoly.normCoeff`. -/
def ops₁g : COps (GFrac R) := ((COps.ofDecidableField R).monomial [1]).normalizeBy CPoly.normCoeff

/-- The model of `R`. -/
noncomputable def M₀g (h0 : ∀ r : R, r′ = 0) : CField R R (COps.ofDecidableField R) :=
  CField.ofDecidableField R h0

lemma toPoly_M₀g (h0 : ∀ r : R, r′ = 0) (p : List R) :
    GPoly.toPoly (M₀g h0) p = CPoly.toPoly p := by
  induction p with
  | nil => rfl
  | cons a p ih => rw [GPoly.toPoly_cons, CPoly.toPoly_cons, ih]; rfl

/-- The model of `R(x)`, `x′ = 1`. -/
noncomputable def M₁g (h0 : ∀ r : R, r′ = 0) :
    @CField (GFrac R) (RatFunc R) _ (ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])) (ops₁g R) :=
  letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  ((M₀g h0).monomial [1]).normalizeBy CPoly.normCoeff fun q ↦ by
    change GFrac.sem (M₀g h0) _ = GFrac.sem (M₀g h0) q
    simp only [GFrac.sem, toPoly_M₀g]
    exact CPoly.normCoeff_spec (algebraMap R[X] (RatFunc R))
      (IsFractionRing.injective R[X] (RatFunc R)) q

lemma sem_M₁g (h0 : ∀ r : R, r′ = 0) (q : GFrac R) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    (M₁g h0).sem q = aeval (RatFunc.X : RatFunc R) (CPoly.toPoly q.1) /
      aeval (RatFunc.X : RatFunc R) (CPoly.toPoly q.2) := by
  rw [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap, ← toPoly_M₀g h0,
    ← toPoly_M₀g h0]
  rfl

theorem primResidue_decides_gen (h0 : ∀ r : R, r′ = 0) (En Ed : CPoly R)
    (Iη : CPoly.RationalIntegral R) (hcη : CPoly.rationalCheck En Ed Iη = true)
    (hη0 : CPoly.isZero Iη.r = false) (b s : GPoly (GFrac R))
    (hsq : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      Squarefree (GPoly.toPoly (M₁g h0) s))
    (hdeg : letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
      (GPoly.toPoly (M₁g h0) b).degree < (GPoly.toPoly (M₁g h0) s).degree) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
    HasElementaryIntegral (algebraMap (RatFunc R)[X] (RatFunc (RatFunc R))
        (GPoly.toPoly (M₁g h0) b) /
        algebraMap (RatFunc R)[X] (RatFunc (RatFunc R)) (GPoly.toPoly (M₁g h0) s)) ↔
      GPoly.residueCheck (ops₁g R) [(En, Ed)] b s = true := by
  let _ : Differential R[X] := polynomialOfDeriv (GPoly.toPoly (M₀g h0) [1])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (GPoly.toPoly (M₀g h0) [1])
  have hDA0 : DifferentialAlgebra R (RatFunc R) := differentialAlgebra_ratFuncOfDeriv _
  have hDA0' : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)])
  have hDA2 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  have h1 : GPoly.toPoly (M₀g h0) [1] = 1 := by
    simp [GPoly.toPoly, M₀g, CField.ofDecidableField]
  -- `η = 1 / x`
  set η : RatFunc R := aeval (RatFunc.X : RatFunc R) (CPoly.toPoly En) /
    aeval (RatFunc.X : RatFunc R) (CPoly.toPoly Ed) with hη
  have hW : GPoly.toPoly (M₁g h0) [(En, Ed)] = C η := by
    have : (M₁g h0).sem (En, Ed) = η := sem_M₁g h0 (En, Ed)
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, this]
  have hR : ∀ r : R, (algebraMap R (RatFunc R) r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, h0, map_zero]
  have hx₀ : (RatFunc.X : RatFunc R)′ = 1 := by
    rw [ratFuncOfDeriv_X, h1, map_one]
  have ht : (RatFunc.X : RatFunc (RatFunc R))′ = algebraMap (RatFunc R) (RatFunc (RatFunc R)) η := by
    rw [ratFuncOfDeriv_X, hW, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  have hD : ∀ P : (RatFunc R)[X], P′ = implicitDeriv (C η) P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) P = _
    rw [hW]
  have hDx : ∀ P : R[X], P′ = derivative P := fun P ↦ by
    change implicitDeriv (GPoly.toPoly (M₀g h0) [1]) P = _
    rw [h1]
    exact implicitDeriv_one_of_trivial h0 P
  -- `η` is not a derivative in `R(x)`
  obtain ⟨hdecη, hsqη, hdegη⟩ :=
    CPoly.rationalCheck_sound_map (K := RatFunc R) (RingHom.id R) hDx En Ed Iη hcη
  simp only [Polynomial.map_id] at hdecη hsqη hdegη
  have hrη0 : CPoly.toPoly Iη.r ≠ 0 := by
    rw [Ne, ← CPoly.isZero_iff, hη0]
    exact Bool.noConfusion
  have hηnd : ∀ y : RatFunc R, y′ ≠ η := fun y hy ↦ hrη0 <| by
    refine eq_zero_of_deriv_eq_proper_fraction (K := RatFunc R) hDx _ _ hsqη hdegη
      (y - (algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.gn) /
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.gd) +
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Iη.Q))) ?_
    have hηφ : η = algebraMap R[X] (RatFunc R) (CPoly.toPoly En) /
        algebraMap R[X] (RatFunc R) (CPoly.toPoly Ed) := by
      rw [hη, RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap]
    rw [CPoly.deriv_sub', hy, hηφ, hdecη]
    ring
  -- normality and coprimality
  have hconstP : ∀ P : (RatFunc R)[X], P′ = 0 → ∃ e : RatFunc R, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero η hηnd (by rw [← hD, hP])
  set S := GPoly.toPoly (M₁g h0) s with hS
  set B := GPoly.toPoly (M₁g h0) b with hB
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) S) S := by
    have := isCoprime_deriv_of_squarefree (s := S) hsq fun p hp _ ↦
      not_dvd_deriv_of_irreducible_primitive η hD hconstP hp
    exact this
  have hS0 : S ≠ 0 := hsq.ne_zero
  have hr := GPoly.residuePoly_spec (M₁g h0) [(En, Ed)] b s hS0 hcop
  have hr' : S ∣ GPoly.toPoly (M₁g h0) (GPoly.residuePoly (ops₁g R) [(En, Ed)] b s) *
      (mapCoeffs S + C η * derivative S) - B := by
    have hid : implicitDeriv (GPoly.toPoly (M₁g h0) [(En, Ed)]) S = mapCoeffs S + C η * derivative S := by
      rw [hW]
      simp [implicitDeriv]
    rwa [hid] at hr
  have hst : aeval (RatFunc.X : RatFunc (RatFunc R)) S ≠ 0 := by
    rw [RatFunc.aeval_X_left_eq_algebraMap]
    exact RatFunc.algebraMap_ne_zero hS0
  have key := CPoly.primResidue_decides (R := R) (F₀ := RatFunc R) (K := RatFunc (RatFunc R))
    hR RatFunc.X hx₀ RatFunc.adjoin_X RatFunc.X RatFunc.adjoin_X En Ed ht Iη hcη
    hη0 B S _ hsq hdeg hst hr'
  rw [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.aeval_X_left_eq_algebraMap] at key
  rw [key, GPoly.residueCheck_iff (M₁g h0) [(En, Ed)] b s hS0]


end Generic

open CPoly.PrimPolyExample in
/-- **Simple poles in `log x` over `ℚ(x)`: decided by `residueCheck`.** -/
theorem logResidue_decides (b s : GPoly (GFrac ℚ))
    (hsq : letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
      Squarefree (GPoly.toPoly M₁ s))
    (hdeg : letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
      (GPoly.toPoly M₁ b).degree < (GPoly.toPoly M₁ s).degree) :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (GPoly.toPoly M₁ [invX])
    HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ b) /
        algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ s)) ↔
      GPoly.residueCheck ops₁ [invX] b s = true :=
  primResidue_decides_gen (fun _ ↦ rfl) En Ed Iη check_η η_not_derivative b s hsq hdeg

end Tower
