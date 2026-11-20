import RischTragerBronstein.Elementary.Closed
import RischTragerBronstein.Differential.Monomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# A simple transcendental extension inside an ambient differential field

Let `E / F` be differential fields and `t ∈ E` transcendental over `F` with `t′ = w(t)` for some
`w ∈ F[X]` (a *monomial* over `F` in Bronstein's sense). Then `F⟮t⟯ ⊆ E`

* is closed under the derivation (`derivClosed_adjoin_simple`), hence a differential field;
* is a fraction field of `F[X]` via `X ↦ t` (`isFractionRing_adjoin_simple`);
* and `F[X] → F⟮t⟯` is a morphism of differential rings when `F[X]` carries the derivation with
  `X′ = w` (`differentialAlgebra_adjoin_simple`).

This is the bridge from towers of subfields of an abstract `E` to the concrete theory of monomial
extensions (`Liouville/PrimitiveCore.lean`, `Liouville/ExponentialCore.lean`), which is stated for an
arbitrary fraction field of `F[X]`.
-/

open IntermediateField Polynomial

namespace Differential

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (t : E)

/-- `F[X]` acts on `F⟮t⟯` through `X ↦ t`. -/
@[reducible] noncomputable def algebraAdjoinSimple : Algebra F[X] F⟮t⟯ :=
  (aeval (AdjoinSimple.gen F t)).toRingHom.toAlgebra

lemma algebraMap_adjoinSimple (P : F[X]) :
    letI := algebraAdjoinSimple (F := F) t
    ((algebraMap F[X] F⟮t⟯ P : F⟮t⟯) : E) = aeval t P := by
  change ((aeval (AdjoinSimple.gen F t) P : F⟮t⟯) : E) = _
  rw [← AdjoinSimple.coe_gen F t, ← IntermediateField.coe_val, ← aeval_algHom_apply]
  rfl

/-- `F⟮t⟯` is a fraction field of `F[X]` when `t` is transcendental. -/
theorem isFractionRing_adjoin_simple (ht : Transcendental F t) :
    letI := algebraAdjoinSimple (F := F) t
    IsFractionRing F[X] F⟮t⟯ := by
  let _ := algebraAdjoinSimple (F := F) t
  let e : RatFunc F ≃ₐ[F[X]] F⟮t⟯ :=
    AlgEquiv.ofRingEquiv (f := (RatFunc.algEquivOfTranscendental t ht).toRingEquiv) fun P ↦ by
      change RatFunc.algEquivOfTranscendental t ht (algebraMap F[X] (RatFunc F) P) = _
      rw [RatFunc.algEquivOfTranscendental_algebraMap]
      rfl
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors F[X]) e

variable [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- If `t′ = w(t)` with `w ∈ F[X]`, then `F⟮t⟯` is closed under the derivation. -/
theorem derivClosed_adjoin_simple (w : F[X]) (hw : t′ = aeval t w) : DerivClosed F⟮t⟯ := by
  have h := (derivClosed_bot (F := F) (K := E)).adjoin t (by
    rw [hw, bot_sup_eq, aeval_eq_sum_range]
    refine sum_mem fun i _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (F⟮t⟯.algebraMap_mem _) (pow_mem (mem_adjoin_simple_self F t) i))
  rwa [bot_sup_eq] at h

/-- `F[X] → F⟮t⟯` commutes with the derivations, for `X′ = w` and `t′ = w(t)`. -/
theorem differentialAlgebra_adjoin_simple (w : F[X]) (hw : t′ = aeval t w) :
    letI := algebraAdjoinSimple (F := F) t
    letI := polynomialOfDeriv w
    letI := differentialOfDerivClosed (derivClosed_adjoin_simple t w hw)
    DifferentialAlgebra F[X] F⟮t⟯ := by
  let _ := algebraAdjoinSimple (F := F) t
  let _ := polynomialOfDeriv w
  let _ := differentialOfDerivClosed (derivClosed_adjoin_simple t w hw)
  refine ⟨fun P ↦ Subtype.ext ?_⟩
  rw [coe_deriv_of_derivClosed, algebraMap_adjoinSimple, algebraMap_adjoinSimple]
  exact deriv_aeval_eq_implicitDeriv t w hw P

end Differential
