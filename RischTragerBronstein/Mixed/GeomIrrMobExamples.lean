import RischTragerBronstein.Mixed.GeomIrrMob

/-!
# Example: geometric irreducibility from a totally ramified finite point

`Y³ = x² (x − 1)² (x − 2)²`: every root of the right-hand side is double (no Eisenstein criterion at
a rational point) and its degree `6` is divisible by `3` (no single place at infinity), but above
`x = 0` there is a single place (`ord₀ = 2`, `gcd(3, 2) = 1`): the inverted curve
`Y′³ = (1 − x′)² (1 − 2x′)²` has a single place at infinity (`wtC`), so the curve is geometrically
irreducible (`geomIrr_of_wt_mob`).
-/

namespace Curves.MT.GeomIrrMobEx

open Curves Curves.MT CPoly Sup Polynomial

/-- `Y³ − x² (x − 1)² (x − 2)²`. -/
def Fq : BPoly ℚ := [[0, 0, -4, 12, -13, 6, -1], [], [], [1]]

lemma Fq_eq : toB Fq = X ^ 3 + C (toPoly [0, 0, -4, 12, -13, 6, -1]) := by
  simp only [Fq, toB_cons, toB_nil, toPoly_nil, map_zero, toPoly_cons, map_one, mul_zero,
    add_zero, mul_one]; ring

lemma Fq_mon : (toB Fq).Monic := by rw [Fq_eq]; monicity!

lemma Fq_deg : (toB Fq).natDegree = 3 := by rw [Fq_eq]; compute_degree!

/-- The inverted curve `Y′³ − (1 − x′)² (1 − 2x′)²`. -/
def Fq' : BPoly ℚ := invB (shiftB Fq 0) 2 6

lemma Fq'_lit : Fq' = [[-1, 6, -13, 12, -4, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0], [1]] := by
  decide +kernel

lemma Fq'_eq : toB Fq' = X ^ 3 + C (toPoly [-1, 6, -13, 12, -4, 0, 0]) := by
  rw [Fq'_lit]
  simp only [toB_cons, toB_nil, toPoly_nil, map_zero, toPoly_cons, map_one, mul_zero, add_zero,
    mul_one]; ring

lemma Fq'_mon : (toB Fq').Monic := by rw [Fq'_eq]; monicity!

lemma Fq'_deg : (toB Fq').natDegree = 3 := by rw [Fq'_eq]; compute_degree!

-- no Eisenstein criterion at `0, 1, 2`, no single place at infinity
#guard !eisC Fq 0 && !eisC Fq 1 && !eisC Fq 2 && !wtC Fq

/-- **`Y³ = x² (x − 1)² (x − 2)²` is geometrically irreducible.** -/
theorem geomIrr : GeomIrr.{0} Fq :=
  geomIrr_of_wt_mob Fq Fq_mon (by rw [Fq_deg]; norm_num) 0 2 6 (invOKb_spec (by decide +kernel))
    Fq'_mon (by show (toB Fq').natDegree = _; rw [Fq'_deg, Fq_deg])
    (by show (toB Fq').natDegree = Fq'.length - 1; rw [Fq'_deg, Fq'_lit]; rfl)
    (by decide +kernel)

end Curves.MT.GeomIrrMobEx
