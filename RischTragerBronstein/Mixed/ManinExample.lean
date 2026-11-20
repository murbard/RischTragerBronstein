import RischTragerBronstein.Mixed.ManinCompute

/-!
# A kernel-checked Manin-map independence certificate

`y² = x³ − x + X²` over `ℚ(X)` (non-constant `j`), `P = (0, X)`, `Q = (1, X)`:
`mu P = −8 / (X(27X⁴ − 4))`, `mu Q = 4(1 − 3X²) / (X(27X⁴ − 4))` (`decide +kernel` on codes), the
Wronskian is non-zero, so `indep_e`: no relation `m P = n Q + T` with `T` torsion, `(m, n) ≠ 0`.
(The height certificate `EllCertExample` proves the same with `k = 3` doublings in about 2 minutes;
this one takes seconds.)
-/

open Polynomial FFHeight FFHeight.Fr WeierstrassCurve WeierstrassCurve.Affine

namespace Manin

/-- `A = −1`. -/
def Ae : CPoly ℚ := [-1]
/-- `B = X²`. -/
def Be : CPoly ℚ := [0, 0, 1]
/-- `P = (0, X)`. -/
def uPe : Fr ℚ := ([], [1])
/-- `y(P) = X`. -/
def vPe : Fr ℚ := ([0, 1], [1])
/-- `Q = (1, X)`. -/
def uQe : Fr ℚ := ([1], [1])

/-- `mu P = −8 / (X (27X⁴ − 4))`. -/
example : muC Ae Be uPe vPe = ([1], [0, 1 / 2, 0, 0, 0, -27 / 8]) := by decide +kernel
/-- `mu Q = 4 (1 − 3X²) / (X (27X⁴ − 4))`. -/
example : muC Ae Be uQe vPe = ([1, 0, -3], [0, -1, 0, 0, 0, 27 / 4]) := by decide +kernel

/-- The Manin certificate is accepted (kernel-checked). -/
theorem cert_e : manCert Ae Be uPe vPe uQe vPe = true := by decide +kernel

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

open scoped Classical in
/-- **On `y² = x³ − x + X²` over `ℚ(X)`, the points `(0, X)` and `(1, X)` are independent modulo
torsion**: no relation `m P = n Q + T` with `T` torsion and `(m, n) ≠ (0, 0)`. -/
theorem indep_e
    (hP : (sW (ι (CPoly.toPoly Ae)) (ι (CPoly.toPoly Be))).toAffine.Nonsingular (val uPe) (val vPe))
    (hQ : (sW (ι (CPoly.toPoly Ae)) (ι (CPoly.toPoly Be))).toAffine.Nonsingular (val uQe) (val vPe))
    (m n : ℤ) (T : (sW (ι (CPoly.toPoly Ae)) (ι (CPoly.toPoly Be))).toAffine.Point) (k : ℕ)
    (hk : k ≠ 0) (hT : k • T = 0) (hrel : m • Point.some _ _ hP = n • Point.some _ _ hQ + T) :
    m = 0 ∧ n = 0 :=
  indep_of_manCert cert_e hP hQ m n T k hk hT hrel

end Manin

