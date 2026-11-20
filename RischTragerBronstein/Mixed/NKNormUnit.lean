import RischTragerBronstein.Mixed.NKResOrd
import RischTragerBronstein.Mixed.NKTrace

/-!
# The norm of a unit at the finite places is a constant

`norm_const_of_unitFin`: an element `z` of `C(x, y)` without zeros or poles at the finite places
is integral over `C[x]` together with `z⁻¹`, so its norm to `C(x)` and the norm of `z⁻¹` are
polynomials with product `1`: `N(z) ∈ C*`. Hence `zⁿ/N(z)` has a trace-free logarithmic
derivative (`trace_logDeriv`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

lemma unitFin_regular {z : C⟮S.x⟯⟮S.y⟯} (hU : S.UnitFin K z) : S.RegularFinite K z :=
  fun a N hN l hl r hr ↦ (hU a N hN l hl r hr).ge

lemma unitFin_inv {z : C⟮S.x⟯⟮S.y⟯} (hz : z ≠ 0) (hU : S.UnitFin K z) : S.UnitFin K z⁻¹ := by
  intro a N hN l hl r hr
  rw [map_inv₀, order_inv_nk _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr hz),
    hU a N hN l hl r hr, neg_zero]

lemma isIntegral_of_regular {z : C⟮S.x⟯⟮S.y⟯} (hreg : S.RegularFinite K z) :
    letI := algebraAdjoinSimple (F := C) S.x
    letI : Algebra C[X] C⟮S.x⟯⟮S.y⟯ :=
      ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).comp (algebraMap C[X] C⟮S.x⟯)).toAlgebra
    IsIntegral C[X] z := by
  letI := algebraAdjoinSimple (F := C) S.x
  letI : Algebra C[X] C⟮S.x⟯⟮S.y⟯ :=
    ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).comp (algebraMap C[X] C⟮S.x⟯)).toAlgebra
  obtain ⟨M, hM, hev⟩ := S.integral_of_regular (K := K) z hreg
  refine ⟨M, hM, ?_⟩
  have key : ∀ p : C[X], ((algebraMap C[X] C⟮S.x⟯⟮S.y⟯ p : C⟮S.x⟯⟮S.y⟯) : L) = aeval S.x p :=
    fun p ↦ by
      show ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ p) : C⟮S.x⟯⟮S.y⟯) : L) = _
      rw [← algebraMap_adjoinSimple]
      rfl
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← hev, eval_map, eval₂_eq_sum_range, eval₂_eq_sum_range]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [key]
  rfl

/-- **The norm of a unit at the finite places is a non-zero constant.** -/
theorem norm_const_of_unitFin {z : C⟮S.x⟯⟮S.y⟯} (hz : z ≠ 0) (hU : S.UnitFin K z) :
    ∃ c : C, c ≠ 0 ∧ Algebra.norm C⟮S.x⟯ z = algebraMap C C⟮S.x⟯ c := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  letI : Algebra C[X] C⟮S.x⟯⟮S.y⟯ :=
    ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).comp (algebraMap C[X] C⟮S.x⟯)).toAlgebra
  haveI : IsScalarTower C[X] C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have h1 := Algebra.isIntegral_norm C⟮S.x⟯ (S.isIntegral_of_regular (K := K) (S.unitFin_regular hU))
  have h2 := Algebra.isIntegral_norm C⟮S.x⟯
    (S.isIntegral_of_regular (K := K) (S.unitFin_regular (S.unitFin_inv hz hU)))
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have hpq : p * q = 1 := IsFractionRing.injective C[X] C⟮S.x⟯ (by
    rw [map_mul, hp, hq, ← map_mul, mul_inv_cancel₀ hz, map_one, map_one])
  obtain ⟨c, hcu, hc⟩ := Polynomial.isUnit_iff.mp (IsUnit.of_mul_eq_one q hpq)
  refine ⟨c, hcu.ne_zero, ?_⟩
  rw [← hp, ← hc]
  show aeval (AdjoinSimple.gen C S.x) (Polynomial.C c) = _
  rw [aeval_C]

lemma unitFin_const (c : C) (hc : c ≠ 0) : S.UnitFin K (algebraMap C C⟮S.x⟯⟮S.y⟯ c) := by
  intro a N hN l hl r hr
  have h := DFunLike.congr_fun (S.embG_algebraMapC (branchSub N a)
    (branchSub_injective N (Nat.pos_of_ne_zero hN) a) (fun c ↦ branchSub_C N a c) r
    (S.root_of_mem hl hr)) c
  rw [RingHom.comp_apply, RingHom.comp_apply] at h
  rw [h, HahnSeries.order_C]

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)

include hx in
/-- **Normalized units**: for `z` without zeros or poles at the finite places, `zⁿ/N(z)` has a
trace-free logarithmic derivative. -/
theorem normalize_unit {z : C⟮S.x⟯⟮S.y⟯} (hz : z ≠ 0) (hU : S.UnitFin K z) :
    ∃ c : C, c ≠ 0 ∧ S.UnitFin K (z ^ S.F.natDegree * (algebraMap C C⟮S.x⟯⟮S.y⟯ c)⁻¹) ∧
      z ^ S.F.natDegree * (algebraMap C C⟮S.x⟯⟮S.y⟯ c)⁻¹ ≠ 0 ∧
      ∀ hm : ((z ^ S.F.natDegree * (algebraMap C C⟮S.x⟯⟮S.y⟯ c)⁻¹ : C⟮S.x⟯⟮S.y⟯) : L)′ /
          ((z ^ S.F.natDegree * (algebraMap C C⟮S.x⟯⟮S.y⟯ c)⁻¹ : C⟮S.x⟯⟮S.y⟯) : L) ∈ C⟮S.x⟯⟮S.y⟯,
        Algebra.trace C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨_, hm⟩ = 0 := by
  classical
  obtain ⟨c, hc0, hc⟩ := S.norm_const_of_unitFin (K := K) hz hU
  set n := S.F.natDegree with hn
  have hcz : algebraMap C C⟮S.x⟯⟮S.y⟯ c ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hc0
  have hz' : z ^ n * (algebraMap C C⟮S.x⟯⟮S.y⟯ c)⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hz) (inv_ne_zero hcz)
  refine ⟨c, hc0, ?_, hz', fun hm ↦ ?_⟩
  · have h1 := S.unitFin_zpow (K := K) hz hU (n : ℤ)
    have h2 := S.unitFin_zpow (K := K) hcz (S.unitFin_const (K := K) c hc0) (-1)
    rw [zpow_natCast] at h1
    rw [zpow_neg_one] at h2
    exact S.unitFin_mul (K := K) (pow_ne_zero _ hz) (inv_ne_zero hcz) h1 h2
  · have hK : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x ω hx
    letI : Differential C⟮S.x⟯ := differentialOfDerivClosed hK
    letI : DifferentialAlgebra C⟮S.x⟯ L := differentialAlgebra_of_derivClosed hK
    have hM : DerivClosed C⟮S.x⟯⟮S.y⟯ := S.derivClosedXYW' ω hx
    letI : Differential C⟮S.x⟯⟮S.y⟯ := differentialOfDerivClosed hM
    haveI : DifferentialAlgebra C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ := ⟨fun k ↦ Subtype.ext rfl⟩
    haveI : FiniteDimensional C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ :=
      IntermediateField.adjoin.finiteDimensional S.isIntegral
    haveI : CharZero C⟮S.x⟯ := charZero_of_injective_algebraMap (algebraMap C C⟮S.x⟯).injective
    have hfin : Module.finrank C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) = n := by
      rw [IntermediateField.adjoin.finrank S.isIntegral, S.natDegree_minpoly]
    set w := z ^ n * (algebraMap C C⟮S.x⟯⟮S.y⟯ c)⁻¹ with hw
    have hwd : (⟨_, hm⟩ : C⟮S.x⟯⟮S.y⟯) = w′ / w := Subtype.ext rfl
    rw [hwd]
    have hca : algebraMap C C⟮S.x⟯⟮S.y⟯ c =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C C⟮S.x⟯ c) := rfl
    have hlog : w′ / w = (n : C⟮S.x⟯⟮S.y⟯) * (z′ / z) -
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ((algebraMap C C⟮S.x⟯ c)′ / algebraMap C C⟮S.x⟯ c) := by
      have hc' : algebraMap C C⟮S.x⟯ c ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hc0
      have e1 : w′ / w = logDeriv w := rfl
      rw [e1, hw, ← div_eq_mul_inv, logDeriv_div (z ^ n) _ (pow_ne_zero _ hz) hcz, logDeriv_pow, hca]
      unfold logDeriv
      rw [deriv_algebraMap, map_div₀]
    rw [hlog, map_sub, Algebra.trace_algebraMap, hfin]
    rw [show ((n : C⟮S.x⟯⟮S.y⟯)) * (z′ / z) = (n : C⟮S.x⟯) • (z′ / z) by
      rw [Algebra.smul_def]; simp, map_smul, trace_logDeriv z hz, hc, smul_eq_mul, nsmul_eq_mul]
    ring

end CurveData

end Curves
