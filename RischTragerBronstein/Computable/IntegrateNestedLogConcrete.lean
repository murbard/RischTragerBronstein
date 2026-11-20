import RischTragerBronstein.Computable.IntegrateNestedLog
import RischTragerBronstein.Computable.IntegratePrim2Concrete

/-!
# Nested logarithms: model-free statement, the concrete tower, and `log log x`

`integrateNestedLog_decides_val` restates the decision theorem with the model-free semantics
`val₃`; `integrateNestedLog_decides_concrete` is the instance
`K₃ = RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = η₁(x)`, `t₂′ = W(x, t₁)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section Checks

variable {R K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R]
variable [Differential R] [Differential R[X]] [Field K₁] [CharZero K₁] [Algebra R[X] K₁]
variable [IsFractionRing R[X] K₁] [Differential K₁] [DifferentialAlgebra R[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

/-- The model hypotheses from the executable certificate that `η₁` is not a derivative. -/
theorem modelW_of_checks {En₁ Ed₁ : CPoly R}
    (hD : ∀ P : R[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ev K₁ (RingHom.id R) (En₁, Ed₁))) P)
    {Iη₁ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false) :
    ModelW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) En₁ Ed₁ := by
  obtain ⟨hdec₁, hsq₁, hdeg₁⟩ :=
    rationalCheck_sound_map (K := K₁) (RingHom.id R) hD En₁ Ed₁ Iη₁ hcη₁
  have hrη0 : (toPoly Iη₁.r).map (RingHom.id R) ≠ 0 := by
    rw [Polynomial.map_id, Ne, ← isZero_iff, hη₁0]
    exact Bool.noConfusion
  refine ModelW.of (RingHom.id R) hD hD₂ fun y hy ↦ hrη0 <| ?_
  refine eq_zero_of_deriv_eq_proper_fraction (K := K₁) hD _ _ hsq₁ hdeg₁
    (y - (algebraMap R[X] K₁ ((toPoly Iη₁.gn).map (RingHom.id R)) /
      algebraMap R[X] K₁ ((toPoly Iη₁.gd).map (RingHom.id R)) +
      algebraMap R[X] K₁ ((toPoly Iη₁.Q).map (RingHom.id R)))) ?_
  rw [deriv_sub', hy, ev, hdec₁]
  ring

end Checks

universe u

variable {R K₁ K₂ : Type*} {K₃ : Type u} [Field R] [DecidableEq R] [CharZero R]
variable [Differential R] [Differential R[X]] [Field K₁] [CharZero K₁] [Algebra R[X] K₁]
variable [IsFractionRing R[X] K₁] [Differential K₁] [DifferentialAlgebra R[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]
variable [Differential K₂[X]] [Field K₃] [Differential K₃] [Algebra K₂[X] K₃]
variable [IsFractionRing K₂[X] K₃] [DifferentialAlgebra K₂[X] K₃]
variable [Algebra K₂ K₃] [IsScalarTower K₂ K₂[X] K₃] [DifferentialAlgebra K₂ K₃]

/-- **Nested logarithms are decided**, model-free statement. -/
theorem integrateNestedLog_decides_val (h0 : ∀ r : R, r′ = 0) {En₁ Ed₁ : CPoly R}
    (W U : GFrac (GFrac R))
    (hD : ∀ P : R[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (val₁ K₁ (En₁, Ed₁))) P)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (val₂ K₁ K₂ W)) P)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hrW : GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 = false)
    (hWnd : isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 = false)
    (hU0 : (ops₂p En₁ Ed₁).isZero U = false)
    (hlog : (ops₂p En₁ Ed₁).isZero ((ops₂p En₁ Ed₁).add ((ops₂p En₁ Ed₁).mul W U)
      ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).deriv U))) = true)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false) :
    HasElementaryIntegral (val₃ K₁ K₂ K₃ A D) ↔
      integrateNestedLog En₁ Ed₁ Iη₁ W A D = true := by
  have hval₁ : ∀ q : GFrac R, ev K₁ (RingHom.id R) q = val₁ K₁ q := fun q ↦ by
    rw [ev, val₁, Polynomial.map_id, Polynomial.map_id]
  have M : ModelW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) En₁ Ed₁ :=
    modelW_of_checks hD (fun P ↦ by rw [hval₁]; exact hD₂ P) hcη₁ hη₁0
  have hp₁ : ∀ p : GPoly (GFrac R),
      GPoly.toPoly (M₁In (K₁ := K₁) (RingHom.id R) h0 M.hD) p = polyVal (val₁ K₁) p :=
    toPoly_eq_polyVal _ _ fun a ↦ by rw [sem_M₁In, hval₁]
  have hs₂ : ∀ a : GFrac (GFrac R), (M.cf (RingHom.id R) h0).sem a = val₂ K₁ K₂ a := fun a ↦ by
    rw [sem_M₂W, hp₁, hp₁, val₂]
  have hp₂ : ∀ p : GPoly (GFrac (GFrac R)),
      GPoly.toPoly (M.cf (RingHom.id R) h0) p = polyVal (val₂ K₁ K₂) p :=
    toPoly_eq_polyVal _ _ hs₂
  rw [val₃, ← hp₂, ← hp₂]
  exact integrateNestedLog_decides h0 M W U (fun P ↦ by rw [hs₂]; exact hD₃ P) Iη₁ hcη₁ hη₁0
    hW0 hrW hWnd hU0 hlog A D hD0

end Tower

namespace Tower

open Differential CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

set_option maxHeartbeats 1000000 in
/-- **The concrete tower** `RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = η₁`, `t₂′ = W`. -/
theorem integrateNestedLog_decides_concrete (h0 : ∀ r : R, r′ = 0) (En₁ Ed₁ : CPoly R)
    (W U : GFrac (GFrac R))
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hrW : GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 = false)
    (hWnd : isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 = false)
    (hU0 : (ops₂p En₁ Ed₁).isZero U = false)
    (hlog : (ops₂p En₁ Ed₁).isZero ((ops₂p En₁ Ed₁).add ((ops₂p En₁ Ed₁).mul W U)
      ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).deriv U))) = true)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En₁ Ed₁))
    letI : Differential (RatFunc (RatFunc (RatFunc R))) :=
      ratFuncOfDeriv (C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W))
    HasElementaryIntegral
        (val₃ (RatFunc R) (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) A D) ↔
      integrateNestedLog En₁ Ed₁ Iη₁ W A D = true := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA0 : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] := polynomialOfDeriv (C (primEta En₁ Ed₁))
  let _ : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En₁ Ed₁))
  have hDA1 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA1' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc (RatFunc R))[X] :=
    polynomialOfDeriv (C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W))
  let _ : Differential (RatFunc (RatFunc (RatFunc R))) :=
    ratFuncOfDeriv (C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W))
  have hDA2 : DifferentialAlgebra (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc (RatFunc R))[X] (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ofFractionRing _ _
  exact integrateNestedLog_decides_val (K₁ := RatFunc R) (K₂ := RatFunc (RatFunc R))
    (K₃ := RatFunc (RatFunc (RatFunc R))) h0 W U
    (fun P ↦ implicitDeriv_one_of_trivial h0 P) (fun P ↦ rfl) (fun P ↦ rfl) Iη₁ hcη₁
    hη₁0 hW0 hrW hWnd hU0 hlog A D hD0

end Tower
