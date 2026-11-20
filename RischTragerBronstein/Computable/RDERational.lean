import RischTragerBronstein.Computable.ODEPoly
import RischTragerBronstein.Computable.SquarefreePart
import RischTragerBronstein.RDE.RationalRHS

/-!
# A verified decision procedure for `y′ + g y = A / D` over `R(x)`

`CPoly.rdeRational g A D` decides whether the Risch differential equation `y′ + g y = A / D`
(`g, A, D ∈ R[x]`, `g ≠ 0`, `D ≠ 0`) has a solution `y ∈ R(x)`, and returns it as `(Y, G)`, `y = Y / G`:
it computes `G = gcd (D, D′)`, `D* = D / G`, `T = D* G′ / G`, and calls `odeSolve` on
`D* Y′ + (g D* - T) Y = A`.

Both answers are proved, **over every characteristic-zero extension `S` of the coefficient field**
(`ι : R → S`) and in every fraction-field model `K` of `S[x]` with `d/dx`:

* `rdeRational_sound`:    `some (Y, G)` ⟹ `y = Y / G` solves the equation;
* `rdeRational_complete`: `none` ⟹ the equation has no solution in `K`.

Stability under `ι` holds because the gcd comes with its Bézout certificate and all divisions are
exact, and these facts are preserved by `Polynomial.map`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- Solve `y′ + g y = A / D` over `R(x)`; the solution is `Y / G`. -/
def rdeRational (g A D : CPoly R) : Option (CPoly R × CPoly R) :=
  let G := gcd D (deriv D)
  let Ds := div D G
  let T := div (mul Ds (deriv G)) G
  match odeSolve Ds (sub (mul g Ds) T) A with
  | some Y => some (Y, G)
  | none => none

variable {S K : Type*} [Field S] [CharZero S] [Differential S[X]] [Field K] [Algebra S[X] K]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

/-- The data computed by `rdeRational` satisfies the hypotheses of `rde_rational_iff`, after any
extension of the coefficient field. -/
lemma rdeData_map (ι : R →+* S) (D : CPoly R) (hD : toPoly D ≠ 0) :
    (toPoly D).map ι = (toPoly (div D (gcd D (deriv D)))).map ι * (toPoly (gcd D (deriv D))).map ι ∧
    (toPoly (gcd D (deriv D))).map ι ∣ derivative ((toPoly D).map ι) ∧
    (∀ h : S[X], h ∣ (toPoly D).map ι → h ∣ derivative ((toPoly D).map ι) →
      h ∣ (toPoly (gcd D (deriv D))).map ι) ∧
    (toPoly (div (mul (div D (gcd D (deriv D))) (deriv (gcd D (deriv D)))) (gcd D (deriv D)))).map ι *
        (toPoly (gcd D (deriv D))).map ι =
      (toPoly (div D (gcd D (deriv D)))).map ι * derivative ((toPoly (gcd D (deriv D))).map ι) ∧
    toPoly (div D (gcd D (deriv D))) ≠ 0 ∧ toPoly (gcd D (deriv D)) ≠ 0 := by
  have hGD : toPoly (gcd D (deriv D)) ∣ toPoly D := by
    rw [toPoly_gcd]; exact (egcd_dvd D (deriv D)).1
  have hGD' : toPoly (gcd D (deriv D)) ∣ derivative (toPoly D) := by
    rw [toPoly_gcd, ← toPoly_deriv]; exact (egcd_dvd D (deriv D)).2
  have hG0 : toPoly (gcd D (deriv D)) ≠ 0 := fun h0 ↦ hD (by simpa [h0] using hGD)
  have hmul := div_mul_of_dvd D (gcd D (deriv D)) hG0 hGD
  have hDs0 : toPoly (div D (gcd D (deriv D))) ≠ 0 := fun h0 ↦ hD (by rw [hmul, h0, zero_mul])
  -- exactness of the second division: `G ∣ D* G′`
  have hprimes : ∀ p : R[X], Irreducible p → p ∣ toPoly (gcd D (deriv D)) →
      p ∣ toPoly (div D (gcd D (deriv D))) := fun p hp hpG ↦
    irreducible_dvd_sqfreePart hD (hmul.trans (mul_comm _ _)) hGD' hp (hpG.trans hGD)
  have hF1 : toPoly (gcd D (deriv D)) ∣
      toPoly (mul (div D (gcd D (deriv D))) (deriv (gcd D (deriv D)))) := by
    rw [toPoly_mul, toPoly_deriv]; exact dvd_mul_derivative hG0 hprimes
  have hT := div_mul_of_dvd _ (gcd D (deriv D)) hG0 hF1
  rw [toPoly_mul, toPoly_deriv] at hT
  refine ⟨by rw [← Polynomial.map_mul, ← hmul], ?_, ?_, ?_, hDs0, hG0⟩
  · rw [derivative_map]; exact Polynomial.map_dvd ι hGD'
  · intro h h1 h2
    have hbez := congrArg (Polynomial.map ι) (egcd_spec D (deriv D))
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, toPoly_deriv,
      ← derivative_map] at hbez
    rw [toPoly_gcd, ← hbez]
    exact dvd_add (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
  · rw [derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, hT]

theorem rdeRational_sound (ι : R →+* S) (hDK : ∀ P : S[X], P′ = derivative P)
    {g A D : CPoly R} (hD : toPoly D ≠ 0) {Y G : CPoly R}
    (h : rdeRational g A D = some (Y, G)) :
    (algebraMap S[X] K ((toPoly Y).map ι) / algebraMap S[X] K ((toPoly G).map ι))′ +
        algebraMap S[X] K ((toPoly g).map ι) *
          (algebraMap S[X] K ((toPoly Y).map ι) / algebraMap S[X] K ((toPoly G).map ι)) =
      algebraMap S[X] K ((toPoly A).map ι) / algebraMap S[X] K ((toPoly D).map ι) := by
  obtain ⟨hDG, -, -, hT, hDs0, hG0⟩ := rdeData_map ι D hD
  simp only [rdeRational] at h
  split at h
  · rename_i Y' hode
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hsol := congrArg (Polynomial.map ι) (odeSolve_sound hode)
    simp only [toPoly_sub, toPoly_mul, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
      ← derivative_map] at hsol
    set φ := algebraMap S[X] K
    have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
    have hφG : φ ((toPoly (gcd D (deriv D))).map ι) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hG0)
    have hφDs : φ ((toPoly (div D (gcd D (deriv D)))).map ι) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hDs0)
    have hT' := congrArg φ hT
    have hsol' := congrArg φ hsol
    simp only [map_mul, map_add, map_sub] at hT' hsol'
    rw [hDG, map_mul, Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hDK, hDK]
    simp only [smul_eq_mul]
    rw [eq_div_iff (mul_ne_zero hφDs hφG), ← hsol']
    field_simp
    linear_combination (φ ((toPoly Y').map ι)) * hT'
  · exact absurd h (by simp)

theorem rdeRational_complete (ι : R →+* S) (hDK : ∀ P : S[X], P′ = derivative P)
    {g A D : CPoly R} (hD : toPoly D ≠ 0) (hg : toPoly g ≠ 0)
    (h : rdeRational g A D = none) (y : K) :
    y′ + algebraMap S[X] K ((toPoly g).map ι) * y ≠
      algebraMap S[X] K ((toPoly A).map ι) / algebraMap S[X] K ((toPoly D).map ι) := by
  intro hy
  obtain ⟨hDG, hGD', hgr, hT, hDs0, hG0⟩ := rdeData_map ι D hD
  have hDS0 : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hD
  obtain ⟨Ys, hYs⟩ := (rde_rational_iff hDK _ _ _ _ _ _ hDS0 hDG hGD' hgr hT).mp ⟨y, hy⟩
  -- the solver found no solution, over `S` either
  simp only [rdeRational] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hode
    have hT₀ : toPoly (div (mul (div D (gcd D (deriv D))) (deriv (gcd D (deriv D))))
        (gcd D (deriv D))) * toPoly (gcd D (deriv D)) =
        toPoly (div D (gcd D (deriv D))) * derivative (toPoly (gcd D (deriv D))) := by
      apply Polynomial.map_injective ι ι.injective
      rw [Polynomial.map_mul, Polynomial.map_mul, ← derivative_map]
      exact hT
    have hdeg := natDegree_le_of_T hg hDs0 hG0 hT₀
    have hP₀ : toPoly (sub (mul g (div D (gcd D (deriv D))))
        (div (mul (div D (gcd D (deriv D))) (deriv (gcd D (deriv D)))) (gcd D (deriv D)))) ≠ 0 := by
      rw [toPoly_sub, toPoly_mul]
      intro h0
      rw [h0, natDegree_zero] at hdeg
      -- then `deg D* = 0` and `g D* = T`, impossible since `deg T < deg (g D*)`
      have hT0 : toPoly (div (mul (div D (gcd D (deriv D))) (deriv (gcd D (deriv D))))
          (gcd D (deriv D))) = toPoly g * toPoly (div D (gcd D (deriv D))) :=
        (sub_eq_zero.mp h0).symm
      have hGd : derivative (toPoly (gcd D (deriv D))) ≠ 0 ∨
          derivative (toPoly (gcd D (deriv D))) = 0 := (em _).symm
      rcases hGd with hGd | hGd
      · have h1 := congrArg degree hT₀
        rw [hT0, degree_mul, degree_mul, degree_mul] at h1
        have h2 := degree_derivative_lt hG0
        have h3 : (toPoly (div D (gcd D (deriv D)))).degree +
            (derivative (toPoly (gcd D (deriv D)))).degree <
            (toPoly g).degree + (toPoly (div D (gcd D (deriv D)))).degree +
              (toPoly (gcd D (deriv D))).degree := by
          calc _ < (toPoly (div D (gcd D (deriv D)))).degree +
                (toPoly (gcd D (deriv D))).degree :=
                WithBot.add_lt_add_left (degree_ne_bot.mpr hDs0) h2
            _ ≤ _ := by
                rw [add_assoc]
                exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hg)
        rw [h1] at h3
        exact lt_irrefl _ h3
      · rw [hGd, mul_zero] at hT₀
        rcases mul_eq_zero.mp hT₀ with h1 | h1
        · rw [hT0] at h1
          exact mul_ne_zero hg hDs0 h1
        · exact hG0 h1
    have hdeg' : (toPoly (div D (gcd D (deriv D)))).natDegree ≤
        (toPoly (sub (mul g (div D (gcd D (deriv D))))
          (div (mul (div D (gcd D (deriv D))) (deriv (gcd D (deriv D))))
            (gcd D (deriv D))))).natDegree := by
      rw [toPoly_sub, toPoly_mul]; exact hdeg
    refine odeSolve_complete_map (S := S) ι
      (P₁ := div D (gcd D (deriv D)))
      (P₀ := sub (mul g (div D (gcd D (deriv D))))
        (div (mul (div D (gcd D (deriv D))) (deriv (gcd D (deriv D)))) (gcd D (deriv D))))
      (A := A) (fun h0 ↦ hP₀ ((trim_eq_nil_iff _).mp h0)) hdeg' hode ⟨Ys, ?_⟩
    simp only [toPoly_sub, toPoly_mul, Polynomial.map_sub, Polynomial.map_mul]
    exact hYs

end CPoly

-- y′ + 2x y = (2x² - 1)/x²  has the solution y = 1/x  (so ∫ ((2x²-1)/x²) e^{x²} = e^{x²}/x)
#eval CPoly.rdeRational ([0, 2] : CPoly ℚ) [-1, 0, 2] [0, 0, 1]
-- y′ + y = 1/x has none (so ∫ eˣ/x is not elementary)
#eval CPoly.rdeRational ([1] : CPoly ℚ) [1] [0, 1]
