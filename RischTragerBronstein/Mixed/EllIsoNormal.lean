import RischTragerBronstein.Mixed.EllIsoCert
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normal form of curves with constant `j`-invariant

`iso_normal_form`: if `A, B ∈ K[X]` are non-zero with `A³ = r B²` (`r ∈ K`, i.e. constant `j`),
then `D = B / A` is a polynomial (its square `A / r` is, and `K[X]` is integrally closed) and
`A = r D²`, `B = r D³`: the quadratic-twist form of `EllIso` with `a = b = r`. Together with
`A = 0` (`EllIso0`) and `B = 0` (`EllIso1728`) this covers every curve with constant `j`.
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K]

local notation "ι" => algebraMap K[X] (RatFunc K)

theorem iso_normal_form (A B : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) (r : K)
    (hr : A ^ 3 = C r * B ^ 2) : ∃ D : K[X], A = C r * D ^ 2 ∧ B = C r * D ^ 3 := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hA' : ι A ≠ 0 := (map_ne_zero_iff _ hinj).mpr hA
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [C_0, zero_mul] at hr; exact hA (pow_eq_zero_iff (by norm_num) |>.mp hr)
  set x : RatFunc K := ι B / ι A with hx
  -- `x² = A / r`
  have hx2 : x ^ 2 = ι (C r⁻¹ * A) := by
    have h := congrArg ι hr
    simp only [map_pow, map_mul, RatFunc.algebraMap_C] at h
    rw [hx, map_mul, RatFunc.algebraMap_C, div_pow]
    have hrC : RatFunc.C r ≠ 0 := by simpa using hr0
    rw [div_eq_iff (pow_ne_zero 2 hA')]
    rw [show RatFunc.C r⁻¹ = (RatFunc.C r)⁻¹ by simp]
    field_simp
    linear_combination -h
  -- integrality
  have hint : IsIntegral K[X] x := by
    refine ⟨X ^ 2 - Polynomial.C (C r⁻¹ * A), ?_, ?_⟩
    · exact monic_X_pow_sub_C _ (by norm_num)
    · simp [eval₂_sub, hx2]
  obtain ⟨D, hD⟩ := (IsIntegrallyClosed.isIntegral_iff (R := K[X]) (K := RatFunc K)).mp hint
  have hBAD : B = A * D := by
    apply hinj
    rw [map_mul, hD, hx]; field_simp
  have hDsq : A = C r * D ^ 2 := by
    apply hinj
    have : ι D ^ 2 = ι (C r⁻¹ * A) := by rw [hD]; exact hx2
    rw [map_mul, map_pow, this, map_mul, ← mul_assoc, ← map_mul, ← C_mul, mul_inv_cancel₀ hr0, C_1,
      map_one, one_mul]
  refine ⟨D, hDsq, ?_⟩
  rw [hBAD, hDsq]; ring

end FFHeight

