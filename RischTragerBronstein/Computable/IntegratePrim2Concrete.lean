import RischTragerBronstein.Computable.IntegratePrim2
import RischTragerBronstein.Computable.Prim2TimesConcrete

/-!
# The height-three integrator, model-free statement and the concrete tower

`Tower.val₃ A D` is the element of `K₃` denoted by a pair of codes, defined without any reference
to derivations or models. `integratePrim2_decides_val` restates `integratePrim2_decides` with it;
`integratePrim2_decides_concrete` is the instance `K₃ = RatFunc (RatFunc (RatFunc R))`,
`x′ = 1`, `t₁′ = η₁(x)`, `t₂′ = η₂(x)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section Val

variable {α K : Type*} [Semiring K]

/-- The polynomial with coefficients `f aⱼ`. -/
noncomputable def polyVal (f : α → K) : GPoly α → K[X]
  | [] => 0
  | a :: l => C (f a) + X * polyVal f l

lemma toPoly_eq_polyVal {α K : Type*} [Field K] [Differential K] {O : COps α}
    (M : CField α K O) (f : α → K) (hf : ∀ a, M.sem a = f a) (p : GPoly α) :
    GPoly.toPoly M p = polyVal f p := by
  induction p with
  | nil => rfl
  | cons a l ih => rw [GPoly.toPoly_cons, polyVal, ih, hf]

end Val

variable {R : Type*} (K₁ K₂ K₃ : Type*) [Field R] [Field K₁] [Algebra R[X] K₁]
variable [Field K₂] [Algebra K₁[X] K₂] [Field K₃] [Algebra K₂[X] K₃]

/-- The element of `K₁ = R(x)` denoted by a fraction code. -/
noncomputable def val₁ (q : GFrac R) : K₁ :=
  algebraMap R[X] K₁ (CPoly.toPoly q.1) / algebraMap R[X] K₁ (CPoly.toPoly q.2)

/-- The element of `K₂ = R(x)(t₁)` denoted by a fraction code. -/
noncomputable def val₂ (q : GFrac (GFrac R)) : K₂ :=
  algebraMap K₁[X] K₂ (polyVal (val₁ K₁) q.1) / algebraMap K₁[X] K₂ (polyVal (val₁ K₁) q.2)

/-- The element of `K₃ = R(x)(t₁)(t₂)` denoted by a pair of polynomial codes. -/
noncomputable def val₃ (A D : GPoly (GFrac (GFrac R))) : K₃ :=
  algebraMap K₂[X] K₃ (polyVal (val₂ K₁ K₂) A) / algebraMap K₂[X] K₃ (polyVal (val₂ K₁ K₂) D)

end Tower

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

/-- **Towers of two primitives are decided**, model-free statement. -/
theorem integratePrim2_decides_val (h0 : ∀ r : R, r′ = 0) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (hD : ∀ P : R[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (val₁ K₁ (En₁, Ed₁))) P)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (algebraMap K₁ K₂ (val₁ K₁ (En₂, Ed₂)))) P)
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false) :
    HasElementaryIntegral (val₃ K₁ K₂ K₃ A D) ↔
      integratePrim2 En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A D = true := by
  have hval₁ : ∀ q : GFrac R, ev K₁ (RingHom.id R) q = val₁ K₁ q := fun q ↦ by
    rw [ev, val₁, Polynomial.map_id, Polynomial.map_id]
  have M : Model2 (K₁ := K₁) (K₂ := K₂) (RingHom.id R) En₁ Ed₁ En₂ Ed₂ :=
    model2_of_checks hD (fun P ↦ by rw [hval₁]; exact hD₂ P) hcη₁ hcη₂ hη₁0 hindep
  have hp₁ : ∀ p : GPoly (GFrac R),
      GPoly.toPoly (M₁In (K₁ := K₁) (RingHom.id R) h0 M.hD) p = polyVal (val₁ K₁) p :=
    toPoly_eq_polyVal _ _ fun a ↦ by rw [sem_M₁In, hval₁]
  have hp₂ : ∀ p : GPoly (GFrac (GFrac R)),
      GPoly.toPoly (M₂In (RingHom.id R) h0 M) p = polyVal (val₂ K₁ K₂) p :=
    toPoly_eq_polyVal _ _ fun a ↦ by rw [sem_M₂In, hp₁, hp₁, val₂]
  rw [val₃, ← hp₂, ← hp₂]
  exact integratePrim2_decides h0 M (fun P ↦ by rw [hval₁]; exact hD₃ P) Iη₁ Iη₂ hcη₁ hcη₂ hη₁0
    hindep A D hD0

end Tower

namespace Tower

open Differential CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]

set_option maxHeartbeats 1000000 in
/-- **The concrete tower** `RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = η₁`, `t₂′ = η₂`. -/
theorem integratePrim2_decides_concrete (h0 : ∀ r : R, r′ = 0) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂p En₁ Ed₁) D = false) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (primEta En₁ Ed₁))
    letI : Differential (RatFunc (RatFunc (RatFunc R))) :=
      ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
    HasElementaryIntegral
        (val₃ (RatFunc R) (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) A D) ↔
      integratePrim2 En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A D = true := by
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
    polynomialOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
  let _ : Differential (RatFunc (RatFunc (RatFunc R))) :=
    ratFuncOfDeriv (C (RatFunc.C (primEta En₂ Ed₂)))
  have hDA2 : DifferentialAlgebra (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc (RatFunc R))[X] (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ofFractionRing _ _
  exact integratePrim2_decides_val (K₁ := RatFunc R) (K₂ := RatFunc (RatFunc R))
    (K₃ := RatFunc (RatFunc (RatFunc R))) h0
    (fun P ↦ implicitDeriv_one_of_trivial h0 P) (fun P ↦ rfl) (fun P ↦ rfl) Iη₁ Iη₂ hcη₁ hcη₂
    hη₁0 hindep A D hD0

end Tower
