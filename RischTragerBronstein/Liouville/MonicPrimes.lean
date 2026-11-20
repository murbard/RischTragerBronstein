import RischTragerBronstein.Liouville.LocalRing
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Monic irreducible polynomials as the places of `F(t)`

Global-from-local statements for `K = Frac F[t]`:

* `exists_monic_irreducible_dvd`: a nonzero nonunit polynomial has a monic irreducible factor;
* `eq_C_of_forall_monic_irreducible_not_dvd`: a nonzero polynomial without monic irreducible factors
  is a nonzero constant;
* `exists_polynomial_of_regularAt`: an element of `K` regular at every monic irreducible `p`
  is a polynomial.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Differential

variable {F K : Type*} [Field F] [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]

local notation "φ" => algebraMap F[X] K

lemma exists_monic_irreducible_dvd {a : F[X]} (ha : ¬IsUnit a) (ha0 : a ≠ 0) :
    ∃ p : F[X], p.Monic ∧ Irreducible p ∧ p ∣ a := by
  obtain ⟨q, hq, hqa⟩ := WfDvdMonoid.exists_irreducible_factor ha ha0
  have hq0 : q ≠ 0 := hq.ne_zero
  refine ⟨q * C q.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hq0,
    irreducible_mul_leadingCoeff_inv.mpr hq, Dvd.dvd.trans ⟨C q.leadingCoeff, ?_⟩ hqa⟩
  rw [mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hq0), C_1, mul_one]

lemma eq_C_of_forall_monic_irreducible_not_dvd {a : F[X]} (ha0 : a ≠ 0)
    (h : ∀ p : F[X], p.Monic → Irreducible p → ¬p ∣ a) : ∃ e : F, e ≠ 0 ∧ a = C e := by
  by_cases ha : IsUnit a
  · obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp ha
    exact ⟨r, hr.ne_zero, rfl⟩
  · obtain ⟨p, hm, hp, hpa⟩ := exists_monic_irreducible_dvd ha ha0
    exact absurd hpa (h p hm hp)

/-- An element of `F(t)` with no poles at any monic irreducible polynomial is a polynomial. -/
theorem exists_polynomial_of_regularAt (v : K)
    (hv : ∀ (p : F[X]) (_ : p.Monic) (hp : Irreducible p), v ∈ regularAt K p hp.prime) :
    ∃ P : F[X], v = φ P := by
  obtain ⟨a, ⟨b, hb⟩, hrel, rfl⟩ := IsFractionRing.exists_reduced_fraction (A := F[X]) v
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hφb : φ b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr hb0
  rw [IsFractionRing.mk'_eq_div] at hv ⊢
  by_cases hbu : IsUnit b
  · obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hbu
    refine ⟨a * C r⁻¹, ?_⟩
    rw [map_mul, div_eq_iff hφb, mul_assoc, ← map_mul, ← C_mul, inv_mul_cancel₀ hr.ne_zero, C_1,
      map_one, mul_one]
  · exfalso
    obtain ⟨p, hm, hp, hpb⟩ := exists_monic_irreducible_dvd hbu hb0
    obtain ⟨c, d, hd, hcd⟩ := hv p hm hp
    have : φ (a * d) = φ (c * b) := by
      rw [map_mul, map_mul, ← hcd]
      simp only
      field_simp
    have h2 := IsFractionRing.injective F[X] K this
    have hpa : p ∣ a := (hp.prime.dvd_or_dvd (h2 ▸ Dvd.dvd.mul_left hpb c)).resolve_right hd
    exact hp.not_isUnit (hrel hpa hpb)

end Differential
