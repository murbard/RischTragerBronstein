import RischTragerBronstein.Curves.Integral
import RischTragerBronstein.Curves.DiscrRes

/-!
# Denominators of integral functions

**`res_mul_integral`**: if `z ∈ C(x, y)` is integral over `C[x]`, then `Res_Y(F, F_Y) · z` is a
polynomial `W(x, y)`. The resultant is, up to sign, the discriminant of the power basis of `y`
(`discr_eq_resultant`), and `discr · z` lies in `C[x][y]` for integral `z`
(Mathlib's `Algebra.discr_mul_isIntegral_mem_adjoin`).
-/

open Polynomial IntermediateField

namespace Curves

open Differential

section Res

variable {C L : Type*} [Field C] [Field L] [Algebra C L] [CharZero C]

namespace CurveData

variable (S : CurveData C L)

/-- **`Res(F, F_Y) · z ∈ C[x][y]` for integral `z`.** -/
theorem res_mul_integral (z : C⟮S.x⟯⟮S.y⟯) (M : C[X][X]) (hM : M.Monic)
    (hMz : (M.map (aeval S.x).toRingHom).eval (z : L) = 0) :
    ∃ W : C[X][X], (z : L) * aeval S.x
      (resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1)) = S.evXY W := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  set pb := IntermediateField.adjoin.powerBasis S.isIntegral with hpb
  letI : Algebra C[X] (C⟮S.x⟯⟮S.y⟯) := ((algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯)).comp (algebraMap C[X] C⟮S.x⟯)).toAlgebra
  haveI : IsScalarTower C[X] C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- the composite `C[X] → L` is `aeval x`
  have hcomp : ∀ P : C[X], ((algebraMap C[X] (C⟮S.x⟯⟮S.y⟯) P : C⟮S.x⟯⟮S.y⟯) : L) = aeval S.x P := fun P ↦ by
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
  -- integrality of `y` and of `z` over `C[X]`
  have hint : IsIntegral C[X] pb.gen := by
    refine ⟨S.F, S.monic, ?_⟩
    apply Subtype.val_injective
    rw [hpb, IntermediateField.adjoin.powerBasis_gen, hev, AdjoinSimple.coe_gen]
    exact S.root
  have hz' : IsIntegral C[X] z := by
    refine ⟨M, hM, ?_⟩
    apply Subtype.val_injective
    rw [hev]
    exact hMz
  haveI := IntermediateField.adjoin.finiteDimensional S.isIntegral
  have key := Algebra.discr_mul_isIntegral_mem_adjoin (R := C[X]) (K := C⟮S.x⟯) (L := C⟮S.x⟯⟮S.y⟯)
    hint hz'
  rw [Algebra.adjoin_singleton_eq_range_aeval] at key
  obtain ⟨W, hW⟩ := key
  -- the discriminant is `± Res(F, F_Y)`
  have hmin : minpoly C⟮S.x⟯ pb.gen = S.F.map (algebraMap C[X] C⟮S.x⟯) := by
    rw [hpb, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, S.minpoly_eq]
  have hd := discr_eq_resultant pb
  have hinj : Function.Injective (algebraMap C[X] C⟮S.x⟯) := IsFractionRing.injective _ _
  rw [hmin, Polynomial.derivative_map, S.monic.natDegree_map,
    natDegree_map_eq_of_injective hinj, resultant_map_map] at hd
  set e := Module.finrank C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) * (Module.finrank C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) - 1) / 2
  set R := resultant S.F (derivative S.F) S.F.natDegree (derivative S.F).natDegree with hR
  refine ⟨Polynomial.C (Polynomial.C ((-1) ^ e)) * W, ?_⟩
  have hW' := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) hW

  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def, hev, hd, Algebra.smul_def,
    IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply,
    IntermediateField.algebraMap_apply] at hW'
  have hgen : ((pb.gen : C⟮S.x⟯⟮S.y⟯) : L) = S.y := by
    rw [hpb, IntermediateField.adjoin.powerBasis_gen, AdjoinSimple.coe_gen]
  rw [hgen] at hW'
  change S.evXY W = _ at hW'
  have hc : (((-1) ^ e * algebraMap C[X] C⟮S.x⟯ R : C⟮S.x⟯) : L) = (-1) ^ e * aeval S.x R := by
    rw [IntermediateField.coe_mul, ← algebraMap_adjoinSimple S.x R]; simp
  rw [hc] at hW'
  have hdeg : (derivative S.F).natDegree = S.F.natDegree - 1 := natDegree_derivative _
  rw [hdeg] at hR
  rw [← hR]
  have hev2 : S.evXY (Polynomial.C (Polynomial.C ((-1) ^ e)) * W) = (-1) ^ e * S.evXY W := by
    simp [CurveData.evXY, Polynomial.map_mul]
  rw [hev2, hW']
  have : ((-1 : L) ^ e) * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  linear_combination (-(aeval S.x R) * (z : L)) * this

end CurveData

end Res

end Curves
