import RischTragerBronstein.Computable.RDEHexpF0
import RischTragerBronstein.Computable.RDEHexp2Complete

/-!
# A general hyperexponential and an exponential: uniqueness in `S(x)(t₁)`

`eq_zero_of_rde_homogeneous_hexp`: `y′ + g y = 0` has only the zero solution in
`K₂ = S(x)(t₁)` (`t₁′ = η t₁`) when `e′ + (g + z η) e = 0` has only the zero solution in
`S(x)` for every integer `z` — the hypothesis provided by the independence certificate
(`hexpExpIndep_hom`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [CPoly.HasRatRoots R] [HasNatTest R]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
  (Hn Hd : CPoly R)

include h0 hD in
/-- **Uniqueness** in `S(x)(t₁)`: `y′ + g y = 0` forces `y = 0` when `g + z η` is not a
logarithmic derivative for any integer `z`. -/
theorem eq_zero_of_rde_homogeneous_hexp
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (g : CPoly R)
    (hhom : ∀ z : ℤ, ∀ e : K₁,
      e′ + (φ ((CPoly.toPoly g).map ι) + (z : K₁) * ηh ι Hn Hd) * e = 0 → e = 0)
    (y : K₂) (hy : y′ + φ₂ (C (φ ((CPoly.toPoly g).map ι))) * y = 0) : y = 0 := by
  set gK : K₁ := φ ((CPoly.toPoly g).map ι) with hgK
  have hnorm : ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ :=
    fun p hm hp hpX hdvd ↦ hpX (by
      have hXp := dvd_X_of_irreducible_special (ηh ι Hn Hd) hD₂ hconst hp hdvd
      exact eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp))
  have hg : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ + (gK - r * ηh ι Hn Hd) * e ≠ 0 :=
    fun r _ e he h ↦ he (hhom (-(r : ℤ)) e (by
      simp only [Int.cast_neg, Int.cast_natCast]; linear_combination h))
  obtain ⟨Y, hY, hpoly⟩ := rde_denominator_exp (K := K₂) (ηh ι Hn Hd) hD₂ hnorm gK hg 0 1 0
    (by rw [X_dvd_iff]; simp) y (by rw [hy, map_zero, zero_div])
  simp only [pow_zero, map_one, mul_one] at hY
  by_cases hY0 : Y = 0
  · rw [hY, hY0, map_zero]
  exfalso
  have hgnl : ∀ e : K₁, e ≠ 0 →
      e′ + (gK + ((Y.natDegree : K₁) - (1 : K₁[X]).natDegree) * ηh ι Hn Hd) * e ≠ 0 :=
    fun e he h ↦ he (hhom ((Y.natDegree : ℤ) - (1 : K₁[X]).natDegree) e (by
      simp only [Int.cast_sub, Int.cast_natCast]; linear_combination h))
  obtain ⟨-, -, hne⟩ := rde_poly_top_exp (ηh ι Hn Hd) gK hD₂ 1 Y one_ne_zero hY0 hgnl
  rw [Nat.cast_zero, zero_mul, sub_zero] at hpoly
  exact hne (by simpa using hpoly)

include h0 hD in
/-- **Uniqueness** in `S(x)(t₁)` for a rational coefficient `g = Gn / Gd ∈ R(x)`. -/
theorem eq_zero_of_rde_homogeneous_hexp₂
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (Gn Gd : CPoly R)
    (hhom : ∀ z : ℤ, ∀ e : K₁,
      e′ + (CPoly.ev K₁ ι (Gn, Gd) + (z : K₁) * ηh ι Hn Hd) * e = 0 → e = 0)
    (y : K₂) (hy : y′ + φ₂ (C (CPoly.ev K₁ ι (Gn, Gd))) * y = 0) : y = 0 := by
  set gK : K₁ := CPoly.ev K₁ ι (Gn, Gd) with hgK
  have hnorm : ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ :=
    fun p hm hp hpX hdvd ↦ hpX (by
      have hXp := dvd_X_of_irreducible_special (ηh ι Hn Hd) hD₂ hconst hp hdvd
      exact eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp))
  have hg : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ + (gK - r * ηh ι Hn Hd) * e ≠ 0 :=
    fun r _ e he h ↦ he (hhom (-(r : ℤ)) e (by
      simp only [Int.cast_neg, Int.cast_natCast]; linear_combination h))
  obtain ⟨Y, hY, hpoly⟩ := rde_denominator_exp (K := K₂) (ηh ι Hn Hd) hD₂ hnorm gK hg 0 1 0
    (by rw [X_dvd_iff]; simp) y (by rw [hy, map_zero, zero_div])
  simp only [pow_zero, map_one, mul_one] at hY
  by_cases hY0 : Y = 0
  · rw [hY, hY0, map_zero]
  exfalso
  have hgnl : ∀ e : K₁, e ≠ 0 →
      e′ + (gK + ((Y.natDegree : K₁) - (1 : K₁[X]).natDegree) * ηh ι Hn Hd) * e ≠ 0 :=
    fun e he h ↦ he (hhom ((Y.natDegree : ℤ) - (1 : K₁[X]).natDegree) e (by
      simp only [Int.cast_sub, Int.cast_natCast]; linear_combination h))
  obtain ⟨-, -, hne⟩ := rde_poly_top_exp (ηh ι Hn Hd) gK hD₂ 1 Y one_ne_zero hY0 hgnl
  rw [Nat.cast_zero, zero_mul, sub_zero] at hpoly
  exact hne (by simpa using hpoly)

end Tower
