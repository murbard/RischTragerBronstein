import RischTragerBronstein.Computable.IntegratePrimExp
import RischTragerBronstein.Computable.IntegrateExpExpConcrete

/-!
# Logarithms over an exponential: model-free statement and the concrete tower

`integratePrimExp_decides_val` restates the decision theorem with the model-free semantics
`val₃`; `integratePrimExp_decides_concrete` is the instance
`K₃ = RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = a₁′(x) t₁`, `t₂′ = W(x, t₁)`.
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

/-- **Logarithms over an exponential are decided**, model-free statement. -/
theorem integratePrimExp_decides_val (h0 : ∀ r : R, r′ = 0) (a₁ : CPoly R)
    (ha₁ : trim (deriv a₁) ≠ []) (W U : GFrac (GFrac R))
    (hD : ∀ P : R[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (algebraMap R[X] K₁ (derivative (toPoly a₁))) * X) P)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (val₂ K₁ K₂ W)) P)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivExp a₁ W.1 W.2 = false)
    (hU0 : (ops₂e a₁).isZero U = false)
    (hlog : (ops₂e a₁).isZero ((ops₂e a₁).add ((ops₂e a₁).mul W U)
      ((ops₂e a₁).neg ((ops₂e a₁).deriv U))) = true)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂e a₁) D = false) :
    HasElementaryIntegral (val₃ K₁ K₂ K₃ A D) ↔ integratePrimExp a₁ W A D = true := by
  have hval₁ : ∀ q : GFrac R, ev K₁ (RingHom.id R) q = val₁ K₁ q := fun q ↦ by
    rw [ev, val₁, Polynomial.map_id, Polynomial.map_id]
  have hD₂' : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa (RingHom.id R) a₁) * X) P := fun P ↦ by
    rw [ηa, Polynomial.map_id]; exact hD₂ P
  have M : ModelEW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) a₁ :=
    ModelEW.of (RingHom.id R) hD ha₁ hD₂'
  have hp₁ : ∀ p : GPoly (GFrac R),
      GPoly.toPoly (M₁In (K₁ := K₁) (RingHom.id R) h0 M.hD) p = polyVal (val₁ K₁) p :=
    toPoly_eq_polyVal _ _ fun a ↦ by rw [sem_M₁In, hval₁]
  have hs₂ : ∀ a : GFrac (GFrac R), (M.cf (RingHom.id R) h0).sem a = val₂ K₁ K₂ a := fun a ↦ by
    rw [ModelEW.cf, sem_M₂E, hp₁, hp₁, val₂]
  have hp₂ : ∀ p : GPoly (GFrac (GFrac R)),
      GPoly.toPoly (M.cf (RingHom.id R) h0) p = polyVal (val₂ K₁ K₂) p :=
    toPoly_eq_polyVal _ _ hs₂
  rw [val₃, ← hp₂, ← hp₂]
  exact integratePrimExp_decides h0 M W U (fun P ↦ by rw [hs₂]; exact hD₃ P) hW0 hWnd hU0 hlog
    A D hD0

end Tower

namespace Tower

open Differential CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

set_option maxHeartbeats 1000000 in
/-- **The concrete tower** `RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = a₁′ t₁`, `t₂′ = W`. -/
theorem integratePrimExp_decides_concrete (h0 : ∀ r : R, r′ = 0) (a₁ : CPoly R)
    (ha₁ : trim (deriv a₁) ≠ []) (W U : GFrac (GFrac R))
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivExp a₁ W.1 W.2 = false)
    (hU0 : (ops₂e a₁).isZero U = false)
    (hlog : (ops₂e a₁).isZero ((ops₂e a₁).add ((ops₂e a₁).mul W U)
      ((ops₂e a₁).neg ((ops₂e a₁).deriv U))) = true)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂e a₁) D = false) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) :=
      ratFuncOfDeriv (C (algebraMap R[X] (RatFunc R) (derivative (toPoly a₁))) * X)
    letI : Differential (RatFunc (RatFunc (RatFunc R))) :=
      ratFuncOfDeriv (C (val₂ (RatFunc R) (RatFunc (RatFunc R)) W))
    HasElementaryIntegral
        (val₃ (RatFunc R) (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) A D) ↔
      integratePrimExp a₁ W A D = true := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA0 : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] :=
    polynomialOfDeriv (C (algebraMap R[X] (RatFunc R) (derivative (toPoly a₁))) * X)
  let _ : Differential (RatFunc (RatFunc R)) :=
    ratFuncOfDeriv (C (algebraMap R[X] (RatFunc R) (derivative (toPoly a₁))) * X)
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
  exact integratePrimExp_decides_val (K₁ := RatFunc R) (K₂ := RatFunc (RatFunc R))
    (K₃ := RatFunc (RatFunc (RatFunc R))) h0 a₁ ha₁ W U
    (fun P ↦ implicitDeriv_one_of_trivial h0 P) (fun P ↦ rfl) (fun P ↦ rfl) hW0 hWnd hU0 hlog
    A D hD0

end Tower
