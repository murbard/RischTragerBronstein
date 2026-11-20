import RischTragerBronstein.Computable.IntegrateHexpHexp
import RischTragerBronstein.Computable.IntegrateNestedLogConcrete

/-!
# Two general hyperexponentials: model-free statement and the concrete tower
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
variable [CPoly.HasRatRoots R] [HasNatTest R]

/-- **Two general hyperexponentials are decided**, model-free statement. -/
theorem integrateHexpHexp_decides_val (h0 : ∀ r : R, r′ = 0) (Hn Hd μ : CPoly R)
    (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0) (hcop : IsCoprime (toPoly Hn) (toPoly Hd))
    (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (Hn₂ Hd₂ μ₂ : CPoly R) (hHn20 : toPoly Hn₂ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂))
    (hcert₂ : CPoly.hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true)
    (hind : CPoly.hexpHexpIndepAll Hn Hd μ Hn₂ Hd₂ μ₂ = true)
    (hD : ∀ P : R[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (algebraMap R[X] K₁ (toPoly Hn) /
      algebraMap R[X] K₁ (toPoly Hd)) * X) P)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (algebraMap K₁ K₂ (algebraMap R[X] K₁ (toPoly Hn₂) /
      algebraMap R[X] K₁ (toPoly Hd₂))) * X) P)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    HasElementaryIntegral (val₃ K₁ K₂ K₃ A D) ↔ integrateHexpHexp Hn Hd μ Hn₂ Hd₂ A D = true := by
  have hval₁ : ∀ q : GFrac R, ev K₁ (RingHom.id R) q = val₁ K₁ q := fun q ↦ by
    rw [ev, val₁, Polynomial.map_id, Polynomial.map_id]
  have M : ModelHW (K₁ := K₁) (K₂ := K₂) (RingHom.id R) Hn Hd μ :=
    ModelHW.of (RingHom.id R) hD hHn0 hHd0 hcop hcert fun P ↦ by
      rw [ηh, Polynomial.map_id, Polynomial.map_id]; exact hD₂ P
  have hp₁ : ∀ p : GPoly (GFrac R),
      GPoly.toPoly (M₁In (K₁ := K₁) (RingHom.id R) h0 M.hD) p = polyVal (val₁ K₁) p :=
    toPoly_eq_polyVal _ _ fun a ↦ by rw [sem_M₁In, hval₁]
  have hs₂ : ∀ a : GFrac (GFrac R), (M.cf (K₂ := K₂) (RingHom.id R) h0).sem a = val₂ K₁ K₂ a := fun a ↦ by
    rw [ModelHW.cf, sem_M₂H, hp₁, hp₁, val₂]
  have hp₂ : ∀ p : GPoly (GFrac (GFrac R)),
      GPoly.toPoly (M.cf (K₂ := K₂) (RingHom.id R) h0) p = polyVal (val₂ K₁ K₂) p :=
    toPoly_eq_polyVal _ _ hs₂
  rw [val₃, ← hp₂, ← hp₂]
  exact integrateHexpHexp_decides h0 M Hn₂ Hd₂ μ₂ hHn20 hHd20 hcop₂ hcert₂ hind hD₃ A D hD0

end Tower

namespace Tower

open Differential CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [CPoly.HasRatRoots R] [HasNatTest R]

set_option maxHeartbeats 1000000 in
/-- **The concrete tower** `RatFunc (RatFunc (RatFunc R))`, `x′ = 1`, `t₁′ = η t₁`, `t₂′ = η₂ t₂`. -/
theorem integrateHexpHexp_decides_concrete (h0 : ∀ r : R, r′ = 0) (Hn Hd μ : CPoly R)
    (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0) (hcop : IsCoprime (toPoly Hn) (toPoly Hd))
    (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (Hn₂ Hd₂ μ₂ : CPoly R) (hHn20 : toPoly Hn₂ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂))
    (hcert₂ : CPoly.hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true)
    (hind : CPoly.hexpHexpIndepAll Hn Hd μ Hn₂ Hd₂ μ₂ = true)
    (A D : GPoly (GFrac (GFrac R))) (hD0 : GPoly.isZero (ops₂h Hn Hd) D = false) :
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) :=
      ratFuncOfDeriv (C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X)
    letI : Differential (RatFunc (RatFunc (RatFunc R))) :=
      ratFuncOfDeriv (C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
        (algebraMap R[X] (RatFunc R) (toPoly Hn₂) / algebraMap R[X] (RatFunc R) (toPoly Hd₂))) * X)
    HasElementaryIntegral
        (val₃ (RatFunc R) (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) A D) ↔
      integrateHexpHexp Hn Hd μ Hn₂ Hd₂ A D = true := by
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
  have hDA0 : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc R)[X] :=
    polynomialOfDeriv (C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X)
  let _ : Differential (RatFunc (RatFunc R)) :=
    ratFuncOfDeriv (C (algebraMap R[X] (RatFunc R) (toPoly Hn) / algebraMap R[X] (RatFunc R) (toPoly Hd)) * X)
  have hDA1 : DifferentialAlgebra (RatFunc R) (RatFunc (RatFunc R)) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA1' : DifferentialAlgebra (RatFunc R)[X] (RatFunc (RatFunc R)) :=
    differentialAlgebra_ofFractionRing _ _
  let _ : Differential (RatFunc (RatFunc R))[X] :=
    polynomialOfDeriv (C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
      (algebraMap R[X] (RatFunc R) (toPoly Hn₂) / algebraMap R[X] (RatFunc R) (toPoly Hd₂))) * X)
  let _ : Differential (RatFunc (RatFunc (RatFunc R))) :=
    ratFuncOfDeriv (C (algebraMap (RatFunc R) (RatFunc (RatFunc R))
      (algebraMap R[X] (RatFunc R) (toPoly Hn₂) / algebraMap R[X] (RatFunc R) (toPoly Hd₂))) * X)
  have hDA2 : DifferentialAlgebra (RatFunc (RatFunc R)) (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ratFuncOfDeriv _
  have hDA2' : DifferentialAlgebra (RatFunc (RatFunc R))[X] (RatFunc (RatFunc (RatFunc R))) :=
    differentialAlgebra_ofFractionRing _ _
  exact integrateHexpHexp_decides_val (K₁ := RatFunc R) (K₂ := RatFunc (RatFunc R))
    (K₃ := RatFunc (RatFunc (RatFunc R))) h0 Hn Hd μ hHn0 hHd0 hcop hcert Hn₂ Hd₂ μ₂ hHn20 hHd20 hcop₂ hcert₂ hind
    (fun P ↦ implicitDeriv_one_of_trivial h0 P) (fun P ↦ rfl) (fun P ↦ rfl) A D hD0

end Tower
