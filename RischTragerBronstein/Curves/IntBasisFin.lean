import RischTragerBronstein.Curves.ResIntegral
import RischTragerBronstein.Curves.IntBasisLog
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral bases

**`exists_intBasis`**: the function field `C(x, y)` of a curve over a field of characteristic `0`
has a basis `w₀, …, w_{n−1}` over `C(x)` of elements integral over `C[x]` such that every integral
element is a `C[x]`-combination of the `wᵢ`. (Mathlib: the integral closure of the principal ring
`C[x]` is free of rank `n`, `IsIntegralClosure.module_free`, `IsIntegralClosure.rank`; its basis
is a `C(x)`-basis, `Module.Basis.localizationLocalization`.)
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section IB

variable {C L : Type*} [Field C] [Field L] [Algebra C L] [CharZero C]

namespace CurveData

variable (S : CurveData C L)

/-- `z` satisfies a monic equation over `C[x]`. -/
def IntegralX (z : C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∃ M : C[X][X], M.Monic ∧ (M.map (aeval S.x).toRingHom).eval (z : L) = 0

/-- **Integral bases exist.** -/
theorem exists_intBasis :
    ∃ b : Module.Basis (Fin S.F.natDegree) C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯), (∀ i, S.IntegralX (b i)) ∧
      ∀ z, S.IntegralX z → ∃ c : Fin S.F.natDegree → C[X],
        (z : L) = ∑ i, aeval S.x (c i) * (b i : L) := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  letI : Algebra C[X] (C⟮S.x⟯⟮S.y⟯) :=
    ((algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯)).comp (algebraMap C[X] C⟮S.x⟯)).toAlgebra
  haveI : IsScalarTower C[X] C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := IntermediateField.adjoin.finiteDimensional S.isIntegral
  have hcomp : ∀ P : C[X], ((algebraMap C[X] (C⟮S.x⟯⟮S.y⟯) P : C⟮S.x⟯⟮S.y⟯) : L) = aeval S.x P :=
    fun P ↦ by
    change ((algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ P) : C⟮S.x⟯⟮S.y⟯) : L) = _
    rw [← algebraMap_adjoinSimple S.x P, IntermediateField.coe_algebraMap_apply,
      IntermediateField.algebraMap_apply]
  have hhom : (algebraMap (C⟮S.x⟯⟮S.y⟯) L).comp (algebraMap C[X] (C⟮S.x⟯⟮S.y⟯)) =
      (aeval S.x).toRingHom := RingHom.ext fun P ↦ hcomp P
  have hev : ∀ (p : C[X][X]) (t : C⟮S.x⟯⟮S.y⟯),
      ((eval₂ (algebraMap C[X] (C⟮S.x⟯⟮S.y⟯)) t p : C⟮S.x⟯⟮S.y⟯) : L) =
        (p.map (aeval S.x).toRingHom).eval (t : L) := fun p t ↦ by
    rw [eval_map, ← hhom]
    exact Polynomial.hom_eval₂ p _ (algebraMap (C⟮S.x⟯⟮S.y⟯) L) t
  have hint : ∀ z : C⟮S.x⟯⟮S.y⟯, IsIntegral C[X] z ↔ S.IntegralX z := fun z ↦ by
    constructor
    · rintro ⟨M, hM, hz⟩
      refine ⟨M, hM, ?_⟩
      rw [← hev, hz]; rfl
    · rintro ⟨M, hM, hz⟩
      refine ⟨M, hM, Subtype.val_injective ?_⟩
      rw [hev, hz]; rfl
  haveI : Module.IsTorsionFree C[X] (C⟮S.x⟯⟮S.y⟯) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    intro P Q h
    have := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) h
    simp only [hcomp] at this
    exact transcendental_iff_injective.mp S.htr this
  set A := integralClosure C[X] (C⟮S.x⟯⟮S.y⟯)
  have hrank : Module.finrank C[X] A = S.F.natDegree := by
    rw [IsIntegralClosure.rank C[X] C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) A, IntermediateField.adjoin.finrank S.isIntegral,
      S.natDegree_minpoly]
  haveI : Module.Free C[X] A := IsIntegralClosure.module_free C[X] C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) A
  haveI : Module.Finite C[X] A := IsIntegralClosure.finite C[X] C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) A
  let b := Module.finBasisOfFinrankEq C[X] A hrank
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors C[X])) (C⟮S.x⟯⟮S.y⟯) :=
    IsIntegralClosure.isLocalization C[X] C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) A
  let b' := Module.Basis.localizationLocalization C⟮S.x⟯ (nonZeroDivisors C[X]) (C⟮S.x⟯⟮S.y⟯) b
  have hb' : ∀ i, b' i = ((b i : A) : C⟮S.x⟯⟮S.y⟯) := fun i ↦ by
    rw [Module.Basis.localizationLocalization_apply]; rfl
  refine ⟨b', fun i ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hb']; exact (hint _).mp (b i).2
  · have hzA : z ∈ A := (hint z).mpr hz
    refine ⟨fun i ↦ b.repr ⟨z, hzA⟩ i, ?_⟩
    have := b.sum_repr ⟨z, hzA⟩
    have h2 := congrArg (fun t : A ↦ ((t : C⟮S.x⟯⟮S.y⟯) : L)) this
    simp only at h2
    rw [← h2]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hb', Algebra.smul_def]
    push_cast
    rw [hcomp]

end CurveData

end IB

end Curves
