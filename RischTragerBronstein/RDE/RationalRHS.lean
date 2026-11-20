import RischTragerBronstein.RDE.NoSolution
import RischTragerBronstein.Rational.SquarefreePart

/-!
# The Risch differential equation over `C(x)` with a rational right-hand side

For `g, A, D ∈ C[x]`, `D = D* G` with `G` a gcd of `D` and `D′`, and `T G = D* G′`:

* `pow_dvd_derivative`: `p ^ (e + 1) ∣ D → p ^ e ∣ D′`, so `G` satisfies the hypothesis of
  `rde_denominator`;
* `rde_rational_iff`:  `(∃ y ∈ C(x), y′ + g y = A / D)  ↔  (∃ Y ∈ C[x], D* Y′ + (g D* - T) Y = A)`
  — the rational equation is equivalent to a polynomial ODE, via `y = Y / G`;
* `natDegree_le_of_T`: `deg D* ≤ deg (g D* - T)` for `g ≠ 0`, the condition under which
  `CPoly.odeSolve` decides that ODE.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

omit [CharZero C'] [Differential C'[X]] in
lemma pow_dvd_derivative {p D : C'[X]} {e : ℕ} (h : p ^ (e + 1) ∣ D) : p ^ e ∣ derivative D := by
  obtain ⟨q, rfl⟩ := h
  rw [derivative_mul, derivative_pow, Nat.add_sub_cancel, pow_succ]
  exact dvd_add (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _) _)
    (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _)

theorem rde_rational_iff (hD : ∀ P : C'[X], P′ = derivative P) (g A D Ds G T : C'[X])
    (hD0 : D ≠ 0) (hDG : D = Ds * G) (hGD' : G ∣ derivative D)
    (hgreatest : ∀ h : C'[X], h ∣ D → h ∣ derivative D → h ∣ G)
    (hT : T * G = Ds * derivative G) :
    (∃ y : K, y′ + φ g * y = φ A / φ D) ↔
      ∃ Y : C'[X], Ds * derivative Y + (g * Ds - T) * Y = A := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hG0 : G ≠ 0 := fun h0 ↦ hD0 (by rw [hDG, h0, mul_zero])
  have hDs0 : Ds ≠ 0 := fun h0 ↦ hD0 (by rw [hDG, h0, zero_mul])
  have hφG : φ G ≠ 0 := (map_ne_zero_iff _ hinj).mpr hG0
  have hφDs : φ Ds ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDs0
  have hφD : φ D = φ Ds * φ G := by rw [hDG, map_mul]
  have hT' : φ T * φ G = φ Ds * φ (derivative G) := by rw [← map_mul, hT, map_mul]
  -- the key identity: for `y = Y / G`
  have key : ∀ Y : C'[X], ((φ Y / φ G)′ + φ g * (φ Y / φ G)) * (φ Ds * φ G) =
      φ (Ds * derivative Y + (g * Ds - T) * Y) := by
    intro Y
    rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
    simp only [smul_eq_mul, map_add, map_mul, map_sub]
    field_simp
    linear_combination (φ Y) * hT'
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨Y, hY⟩ := rde_denominator hD g A D G hD0
      (fun p _ e hpe ↦ hgreatest _ ((pow_dvd_pow p (Nat.le_succ e)).trans hpe)
        (pow_dvd_derivative hpe)) y hy
    refine ⟨Y, hinj ?_⟩
    have hyY : y = φ Y / φ G := by rw [← hY]; field_simp
    rw [← key Y, ← hyY, hy, hφD]
    field_simp
  · rintro ⟨Y, hY⟩
    refine ⟨φ Y / φ G, ?_⟩
    have := key Y
    rw [hY] at this
    rw [hφD, eq_div_iff (mul_ne_zero hφDs hφG)]
    exact this

omit [Differential C'[X]] in
/-- `deg D* ≤ deg (g D* - T)` when `g ≠ 0` and `T G = D* G′`. -/
theorem natDegree_le_of_T {g Ds G T : C'[X]} (hg : g ≠ 0) (hDs0 : Ds ≠ 0) (hG0 : G ≠ 0)
    (hT : T * G = Ds * derivative G) : Ds.natDegree ≤ (g * Ds - T).natDegree := by
  have hTlt : T.degree < (g * Ds).degree := by
    have h1 : T.degree < Ds.degree := by
      by_cases hT0 : T = 0
      · rw [hT0, degree_zero]; exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hDs0)
      have hdeg := congrArg degree hT
      rw [degree_mul, degree_mul] at hdeg
      have hlt : Ds.degree + (derivative G).degree < Ds.degree + G.degree :=
        WithBot.add_lt_add_left (degree_ne_bot.mpr hDs0) (degree_derivative_lt hG0)
      rw [← hdeg] at hlt
      exact lt_of_add_lt_add_right hlt
    refine lt_of_lt_of_le h1 ?_
    rw [degree_mul]
    exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hg)
  by_cases hT0 : T = 0
  · rw [hT0, sub_zero, natDegree_mul hg hDs0]; omega
  · rw [natDegree_sub_eq_left_of_natDegree_lt (natDegree_lt_natDegree hT0 hTlt),
      natDegree_mul hg hDs0]
    omega

end Differential
