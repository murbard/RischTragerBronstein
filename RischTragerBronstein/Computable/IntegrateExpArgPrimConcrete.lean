import RischTragerBronstein.Computable.IntegrateExpArgPrim
import RischTragerBronstein.Computable.IntegrateExpPrimConcrete
import RischTragerBronstein.Computable.IntegrateNestedLogConcrete

/-!
# Exponentials with argument in `R(x)[t₁]`: model-free statement and the concrete tower

`integrateExpArgPrim_decides_val` / `integrateExpArgPrim_decides_concrete`: the instance
`K₃ = RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = η₁(x)`, `t₂′ = a′(x, t₁) t₂`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

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

/-- **Exponentials with argument in `R(x)[t₁]` are decided**, model-free statement. -/
theorem integrateExpArgPrim_decides_val (h0 : ∀ r : R, r′ = 0) {En₁ Ed₁ : CPoly R}
    (a : GPoly (GFrac R))
    (hηc : 2 ≤ (GPoly.trim (ops₁g R) (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] a)).length)
    (hD : ∀ P : R[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (val₁ K₁ (En₁, Ed₁))) P)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (val₂ K₁ K₂ (expEtaG En₁ Ed₁ a)) * X) P)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false) :
    HasElementaryIntegral (val₃ K₁ K₂ K₃ A D) ↔
      integrateExpArgPrim En₁ Ed₁ Iη₁ a A D = true := by
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
  exact integrateExpArgPrim_decides h0 M a hηc (fun P ↦ by rw [hs₂]; exact hD₃ P) Iη₁ hcη₁ hη₁0
    A D hD0

end Tower

namespace Tower

open Differential CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

set_option maxHeartbeats 1000000 in
/-- **The concrete tower** `RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = η₁`, `t₂′ = a′ t₂`. -/
theorem integrateExpArgPrim_decides_concrete (h0 : ∀ r : R, r′ = 0) (En₁ Ed₁ : CPoly R)
    (a : GPoly (GFrac R))
    (hηc : 2 ≤ (GPoly.trim (ops₁g R) (GPoly.derivT (ops₁g R) [(En₁, Ed₁)] a)).length)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En₁ Ed₁))
    letI : Differential (RatFunc (RatFunc (RatFunc R))) :=
      ratFuncOfDeriv (C (val₂ (RatFunc R) (RatFunc (RatFunc R)) (expEtaG En₁ Ed₁ a)) * X)
    HasElementaryIntegral
        (val₃ (RatFunc R) (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) A D) ↔
      integrateExpArgPrim En₁ Ed₁ Iη₁ a A D = true := by
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
    polynomialOfDeriv (C (val₂ (RatFunc R) (RatFunc (RatFunc R)) (expEtaG En₁ Ed₁ a)) * X)
  let _ : Differential (RatFunc (RatFunc (RatFunc R))) :=
    ratFuncOfDeriv (C (val₂ (RatFunc R) (RatFunc (RatFunc R)) (expEtaG En₁ Ed₁ a)) * X)
  have hDA2 : DifferentialAlgebra (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc (RatFunc R))[X] (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ofFractionRing _ _
  exact integrateExpArgPrim_decides_val (K₁ := RatFunc R) (K₂ := RatFunc (RatFunc R))
    (K₃ := RatFunc (RatFunc (RatFunc R))) h0 a hηc
    (fun P ↦ implicitDeriv_one_of_trivial h0 P) (fun P ↦ rfl) (fun P ↦ rfl) Iη₁ hcη₁
    hη₁0 A D hD0

end Tower
