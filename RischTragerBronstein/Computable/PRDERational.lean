import RischTragerBronstein.Computable.PRDEPoly
import RischTragerBronstein.Computable.RDERationalG

/-!
# The parametric Risch differential equation `y′ + g y = A₀ / D - c A₁ / D` over `R(x)`

One unknown constant `c`. Same reduction as `rdeRationalG` (`y = Y / D`), then the parametric
polynomial solver `prdeSolveFull`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- Solve `y′ + (Gn / Gd) y = A₀ / D - c A₁ / D`; the solution is `(c, Y / D)`. -/
def prdeRationalG (Gn Gd A₀ A₁ D : CPoly R) : Option (R × CPoly R) :=
  prdeSolveFull (mul Gd D) (sub (mul Gn D) (mul Gd (deriv D))) (mul (mul A₀ D) Gd)
    (mul (mul A₁ D) Gd) ((trim D).length - 1)

variable {S K : Type*} [Field S] [DecidableEq S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

theorem prdeRationalG_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Gn Gd A₀ A₁ D : CPoly R} (hD0 : toPoly D ≠ 0) (hGd0 : toPoly Gd ≠ 0) {c : R} {Y : CPoly R}
    (h : prdeRationalG Gn Gd A₀ A₁ D = some (c, Y)) :
    (φ ((toPoly Y).map ι) / φ ((toPoly D).map ι))′ +
        φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) *
          (φ ((toPoly Y).map ι) / φ ((toPoly D).map ι)) =
      φ ((toPoly A₀).map ι) / φ ((toPoly D).map ι) -
        φ (C (ι c)) * (φ ((toPoly A₁).map ι) / φ ((toPoly D).map ι)) := by
  have hs := prdeSolveFull_sound h
  simp only [toPoly_mul, toPoly_sub, toPoly_deriv] at hs
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hφD : φ ((toPoly D).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hD0)
  have hφGd : φ ((toPoly Gd).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hGd0)
  have := congrArg (fun P : R[X] ↦ φ (P.map ι)) hs
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, map_add, map_mul,
    map_sub, ← derivative_map, map_C] at this
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
  simp only [smul_eq_mul]
  field_simp
  linear_combination this

/-- **Completeness**: if a solution `(c, y)` exists over an extension `S` of the constants (for
a coefficient `g = Gn / Gd` without simple poles and `deg Gn + 1 ≠ deg Gd`), the solver succeeds. -/
theorem prdeRationalG_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Gn Gd A₀ A₁ D G₁ : CPoly R} (hD0 : toPoly D ≠ 0) (hGn0 : toPoly Gn ≠ 0)
    (hGd0 : toPoly Gd ≠ 0) (hcop : IsCoprime (toPoly Gn) (toPoly Gd))
    (hr1 : toPoly G₁ ∣ toPoly Gd) (hr2 : toPoly G₁ ∣ derivative (toPoly Gd))
    (hr3 : toPoly Gd ∣ toPoly G₁ ^ 2)
    (hdeg : (toPoly Gn).natDegree + 1 ≠ (toPoly Gd).natDegree)
    (h : prdeRationalG Gn Gd A₀ A₁ D = none) (c : S) (y : K)
    (hy : y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y =
      φ ((toPoly A₀).map ι) / φ ((toPoly D).map ι) -
        φ (C c) * (φ ((toPoly A₁).map ι) / φ ((toPoly D).map ι))) : False := by
  have hDS : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hD0
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGd0
  have hsq := sq_dvd_of_repeated (Polynomial.map_dvd ι hr1)
    (by rw [derivative_map]; exact Polynomial.map_dvd ι hr2)
    (by rw [← Polynomial.map_pow]; exact Polynomial.map_dvd ι hr3)
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hφD : φ ((toPoly D).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDS
  have hy' : y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y =
      φ ((toPoly A₀).map ι - C c * (toPoly A₁).map ι) / φ ((toPoly D).map ι) := by
    rw [hy, map_sub, map_mul, sub_div, mul_div_assoc]
  obtain ⟨Ys, hYs⟩ := (rde_rationalG_iff (K := K) hD _ _ _ _ hDS hGdS (hcop.map (mapRingHom ι))
    hsq).mp ⟨y, hy'⟩
  -- the polynomial ODE, in the form of the solver
  set P₁ := mul Gd D with hP₁
  set P₀ := sub (mul Gn D) (mul Gd (deriv D)) with hP₀
  have hP₁poly : toPoly P₁ = toPoly Gd * toPoly D := by rw [hP₁, toPoly_mul]
  have hP₀poly : toPoly P₀ = toPoly Gn * toPoly D - toPoly Gd * derivative (toPoly D) := by
    rw [hP₀, toPoly_sub, toPoly_mul, toPoly_mul, toPoly_deriv]
  obtain ⟨hP₀ne, hpivot⟩ := rde_pivot (toPoly Gn) (toPoly Gd) (toPoly D) hGn0 hGd0 hD0 hdeg
  rw [← hP₀poly, ← hP₁poly] at hpivot
  rw [← hP₀poly] at hP₀ne
  have hP₁ne : toPoly P₁ ≠ 0 := by rw [hP₁poly]; exact mul_ne_zero hGd0 hD0
  have htP₀ : trim P₀ ≠ [] := fun h0 ↦ hP₀ne ((trim_eq_nil_iff _).mp h0)
  have htP₁ : trim P₁ ≠ [] := fun h0 ↦ hP₁ne ((trim_eq_nil_iff _).mp h0)
  have hd₀ := (natDegree_toPoly_of_trim_ne_nil htP₀).1
  have hd₁ := (natDegree_toPoly_of_trim_ne_nil htP₁).1
  have hdgeq : odeDg P₁ P₀ = max ((toPoly P₁).natDegree - 1) (toPoly P₀).natDegree := by
    rw [odeDg, hd₀, hd₁]
    congr 1
  have hDdeg : (toPoly D).natDegree ≤ (trim D).length - 1 := natDegree_toPoly_le D
  have hkb : ∀ k, odePiv P₁ P₀ k = 0 → k ≤ (trim D).length - 1 := fun k hk ↦ by
    rw [odePiv, ← coeff_toPoly, ← coeff_toPoly, hdgeq] at hk
    exact (hpivot k hk).trans hDdeg
  refine prdeSolveFull_complete_map ι htP₀ hkb h ⟨c, Ys, ?_⟩
  rw [hP₁poly, hP₀poly]
  simp only [toPoly_mul, Polynomial.map_mul, Polynomial.map_sub, ← derivative_map]
  simp only [coe_mapRingHom] at hYs
  rw [hYs]
  ring

end CPoly
