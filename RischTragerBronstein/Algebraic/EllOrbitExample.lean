import RischTragerBronstein.Algebraic.EllOrbit

/-!
# Poles over a Galois orbit: `y² = x³ + x − 1`

The poles `x = ±i` of `∫ −2 dx / ((x² + 1) √(x³ + x − 1))` lie under the points `(±i, ±i)`
(`p(i) = −1 = i²`), a Galois orbit with rational residue. One Cantor step (`g = x`,
`p − g² = (x² + 1)(x − 1)`) moves the residues to the rational point `(1, 1)`, of infinite order:
**not elementary**. `∫ (x³ − x + 2) dx / ((x² + 1)(x − 1) √(x³ + x − 1))` reduces to `0`:
**elementary** (it is `d log((y − x)/(y + x))`).
-/

open Polynomial Differential

namespace EllAlgo.OrbitExample

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma sq_p : Squarefree (X ^ 3 + C ((0 : ℤ) : ℚ) * X ^ 2 + C ((1 : ℤ) : ℚ) * X + C ((-1 : ℤ) : ℚ)) := by
  have h := CPoly.squarefreeCheck_sound (s := pOf 0 1 (-1)) (by decide +kernel)
  rwa [toPoly_pOf] at h

/-- **`∫ −2 dx / ((x² + 1) √(x³ + x − 1))` is not elementary.** -/
theorem ex_orbit_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + x - 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (-2 / ((x ^ 2 + 1) * y)) := by
  have h := ellDecideOrbit_spec hC hCall x y hx 0 1 (-1) sq_p
    (by rw [hy]; push_cast; ring) hgen [-2] [1, 0, 1] 30 false (by decide +kernel)
  rw [show aeval x (CPoly.toPoly ([-2] : CPoly ℚ)) = -2 by simp [CPoly.toPoly],
    show aeval x (CPoly.toPoly ([1, 0, 1] : CPoly ℚ)) = x ^ 2 + 1 by
      simp [CPoly.toPoly]; ring] at h
  intro h'
  exact Bool.false_ne_true (h.mpr h')

/-- **`∫ (x³ − x + 2) dx / ((x² + 1)(x − 1) √(x³ + x − 1))` is elementary.** -/
theorem ex_orbit_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + x - 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral ((x ^ 3 - x + 2) / ((x ^ 3 - x ^ 2 + x - 1) * y)) := by
  have h := ellDecideOrbit_spec hC hCall x y hx 0 1 (-1) sq_p
    (by rw [hy]; push_cast; ring) hgen [2, -1, 0, 1] [-1, 1, -1, 1] 30 true (by decide +kernel)
  rw [show aeval x (CPoly.toPoly ([2, -1, 0, 1] : CPoly ℚ)) = x ^ 3 - x + 2 by
      simp [CPoly.toPoly]; ring,
    show aeval x (CPoly.toPoly ([-1, 1, -1, 1] : CPoly ℚ)) = x ^ 3 - x ^ 2 + x - 1 by
      simp [CPoly.toPoly]; ring] at h
  exact h.mp rfl

end EllAlgo.OrbitExample
