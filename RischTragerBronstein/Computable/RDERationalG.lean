import RischTragerBronstein.Computable.ODEPolyGen
import RischTragerBronstein.RDE.RationalCoeff

/-!
# The Risch differential equation over `R(x)` with a rational coefficient

`y′ + (Gn / Gd) y = A / D`, where `Gn / Gd` is in lowest terms, has no simple pole (every prime
factor of `Gd` is repeated) and `deg Gn + 1 ≠ deg Gd` — the coefficient `j η` for a hyperexponential
`t′ = η t`, e.g. `t = exp a(x)` with `a` a rational function.

`CPoly.rdeRationalG Gn Gd A D` solves `(Gd D) Y′ + (Gn D - Gd D′) Y = A D Gd` with the general
polynomial ODE solver and returns `y = Y / D`.

* `rdeRationalG_sound`: a returned `Y / D` solves the equation;
* `rdeRationalG_complete`: `none` means there is no solution in `S(x)` for any extension `S` of
  the constants.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R S K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

/-- Solve `y′ + (Gn / Gd) y = A / D`; the solution is `Y / D`. -/
def rdeRationalG (Gn Gd A D : CPoly R) : Option (CPoly R × CPoly R) :=
  (odeSolveFull (mul Gd D) (sub (mul Gn D) (mul Gd (deriv D))) (mul (mul A D) Gd)
    ((trim D).length - 1)).map fun Y ↦ (Y, D)

/-- If `Gd ∣ G₁ ^ 2` for a common divisor `G₁` of `Gd` and `Gd′`, every prime factor of `Gd` is
repeated. (This form of the hypothesis is stable under extension of the constants.) -/
lemma sq_dvd_of_repeated {F : Type*} [Field F] [CharZero F] {Gd G₁ : F[X]} (h1 : G₁ ∣ Gd)
    (h2 : G₁ ∣ derivative Gd) (h3 : Gd ∣ G₁ ^ 2) (p : F[X]) (hp : Irreducible p) (hpG : p ∣ Gd) :
    p ^ 2 ∣ Gd := by
  have hpG₁ : p ∣ G₁ := hp.prime.dvd_of_dvd_pow (hpG.trans h3)
  obtain ⟨c, hc⟩ := hpG
  have hd : p ∣ derivative Gd := hpG₁.trans h2
  rw [hc, derivative_mul] at hd
  have hd' : p ∣ derivative p * c := (dvd_add_left (dvd_mul_right p _)).mp hd
  have hnp : ¬p ∣ derivative p := fun hdvd ↦ by
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  obtain ⟨c', hc'⟩ := (hp.prime.dvd_or_dvd hd').resolve_left hnp
  exact ⟨c', by rw [hc, hc']; ring⟩

theorem rdeRationalG_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Gn Gd A D Y D' : CPoly R} (hD0 : toPoly D ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (h : rdeRationalG Gn Gd A D = some (Y, D')) :
    (φ ((toPoly Y).map ι) / φ ((toPoly D').map ι))′ +
        φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) *
          (φ ((toPoly Y).map ι) / φ ((toPoly D').map ι)) =
      φ ((toPoly A).map ι) / φ ((toPoly D).map ι) := by
  simp only [rdeRationalG, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨Y₀, hY₀, rfl, rfl⟩ := h
  have hs := odeSolveFull_sound hY₀
  simp only [toPoly_mul, toPoly_sub, toPoly_deriv] at hs
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hφD : φ ((toPoly D).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hD0)
  have hφGd : φ ((toPoly Gd).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hGd0)
  have := congrArg (fun P : R[X] ↦ φ (P.map ι)) hs
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, map_add, map_mul,
    map_sub, ← derivative_map] at this
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
  simp only [smul_eq_mul]
  field_simp
  linear_combination this

theorem rdeRationalG_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Gn Gd A D G₁ : CPoly R} (hD0 : toPoly D ≠ 0) (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (hcop : IsCoprime (toPoly Gn) (toPoly Gd))
    (hr1 : toPoly G₁ ∣ toPoly Gd) (hr2 : toPoly G₁ ∣ derivative (toPoly Gd))
    (hr3 : toPoly Gd ∣ toPoly G₁ ^ 2)
    (hdeg : (toPoly Gn).natDegree + 1 ≠ (toPoly Gd).natDegree)
    (h : rdeRationalG Gn Gd A D = none) (y : K) :
    y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y ≠
      φ ((toPoly A).map ι) / φ ((toPoly D).map ι) := by
  intro hy
  have hDS : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hD0
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGd0
  have hsq := sq_dvd_of_repeated (Polynomial.map_dvd ι hr1)
    (by rw [derivative_map]; exact Polynomial.map_dvd ι hr2)
    (by rw [← Polynomial.map_pow]; exact Polynomial.map_dvd ι hr3)
  obtain ⟨Ys, hYs⟩ := (rde_rationalG_iff (K := K) hD _ _ _ _ hDS hGdS (hcop.map (mapRingHom ι))
    hsq).mp ⟨y, hy⟩
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
  simp only [rdeRationalG, Option.map_eq_none_iff] at h
  refine odeSolveFull_complete_map ι htP₀ hkb h ⟨Ys, ?_⟩
  rw [hP₁poly, hP₀poly]
  simp only [toPoly_mul, Polynomial.map_mul, Polynomial.map_sub, ← derivative_map]
  simpa only [coe_mapRingHom] using hYs

-- `y′ - (1 / x²) y = -1 / x²` (from `∫ e^{1/x} / x² …`): `y = 1`
#eval rdeRationalG (R := ℚ) [-1] [0, 0, 1] [-1] [0, 0, 1]
-- `y′ - (1 / x²) y = 1` (from `∫ e^{1/x}`): no solution
#eval rdeRationalG (R := ℚ) [-1] [0, 0, 1] [1] [1]

end CPoly
