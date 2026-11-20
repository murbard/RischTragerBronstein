import RischTragerBronstein.Mixed.EllPar
import RischTragerBronstein.Mixed.MWPair

/-!
# The Néron–Tate height pairing on an elliptic curve over `K(X)`

For `E : y² = x³ + A x + B` over `K(X)` (`char K = 0`, `4A³ + 27B² ≠ 0`) and the naive height
`hN P = ht (x P)`:

* `hR_double`: `|hN (2P) − 4 hN P| ≤ 11 D` (`D = max (deg A) (deg B)`);
* `hR_par`: `|hN (P + Q) + hN (P − Q) − 2 hN P − 2 hN Q| ≤ 12 D` (the lower bound from the upper one
  applied to `P + Q, P − Q`, plus doubling);
* hence (`MWTate`, `MWPair`) the canonical height `ĥ = lim hN (2ⁿ P) / 4ⁿ` and the symmetric
  `ℤ`-bilinear Néron–Tate pairing on the Mordell–Weil group `E(K(X))`, and the checkable
  **independence certificate** `ell_indep`: if the approximations `hN (2ᵏ ·) / 4ᵏ` of `ĥ P, ĥ Q,
  ĥ (P + Q)` give a Gram value above the explicit error bound, then `m • P = n • Q` forces
  `m = n = 0`. This is the certificate needed by the Mordell–Weil exception of the mixed deciders,
  for genus-one curves.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

/-- The naive height as a real function. -/
noncomputable def hR (A B : K[X]) (P : (shortW A B).toAffine.Point) : ℝ := (hN A B P : ℝ)

theorem hR_double (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (P : (shortW A B).toAffine.Point) :
    |hR A B (MWPair.dbl P) - 4 * hR A B P| ≤ 11 * (max A.natDegree B.natDegree : ℕ) := by
  obtain ⟨h1, h2⟩ := hN_double A B hΔ P
  unfold hR MWPair.dbl
  rw [abs_le]
  constructor
  · have : (4 * hN A B P : ℝ) ≤ hN A B (P + P) + 11 * (max A.natDegree B.natDegree : ℕ) := by
      exact_mod_cast h1
    linarith
  · have : (hN A B (P + P) : ℝ) ≤ 4 * hN A B P + 2 * (max A.natDegree B.natDegree : ℕ) := by
      exact_mod_cast h2
    have : (0 : ℝ) ≤ (max A.natDegree B.natDegree : ℕ) := Nat.cast_nonneg _
    linarith

theorem hR_par (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (P Q : (shortW A B).toAffine.Point) :
    |hR A B (P + Q) + hR A B (P - Q) - 2 * hR A B P - 2 * hR A B Q| ≤
      12 * (max A.natDegree B.natDegree : ℕ) := by
  set D : ℝ := ((max A.natDegree B.natDegree : ℕ) : ℝ)
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have up : ∀ P Q : (shortW A B).toAffine.Point,
      hR A B (P + Q) + hR A B (P - Q) ≤ 2 * hR A B P + 2 * hR A B Q + 2 * D := fun P Q ↦ by
    unfold hR; simp only [D]; exact_mod_cast hN_par_upper A B hΔ P Q
  have lo : ∀ P : (shortW A B).toAffine.Point, 4 * hR A B P ≤ hR A B (P + P) + 11 * D := fun P ↦ by
    unfold hR; simp only [D]; exact_mod_cast (hN_double A B hΔ P).1
  have u2 := up (P + Q) (P - Q)
  have e1 : P + Q + (P - Q) = P + P := by abel
  have e2 : P + Q - (P - Q) = Q + Q := by abel
  rw [e1, e2] at u2
  have lP := lo P
  have lQ := lo Q
  have u1 := up P Q
  rw [abs_le]; constructor <;> linarith

/-- The Néron–Tate canonical height. -/
noncomputable def canonH (A B : K[X]) : (shortW A B).toAffine.Point → ℝ :=
  MWTate.canon MWPair.dbl (hR A B)

/-- **The Néron–Tate pairing** on `E(K(X))`: symmetric and `ℤ`-bilinear. -/
noncomputable def ntPairing (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    (shortW A B).toAffine.Point →+ (shortW A B).toAffine.Point →+ ℝ :=
  MWPair.pairing (canonH A B) (MWPair.canon_parallelogram (hR_double A B hΔ) (hR_par A B hΔ))

theorem ntPairing_self (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (P : (shortW A B).toAffine.Point) : ntPairing A B hΔ P P = canonH A B P :=
  MWPair.pairing_self _ _ P

/-- `|ĥ P − hN P| ≤ 11 D / 3`. -/
theorem canonH_close (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (P : (shortW A B).toAffine.Point) :
    |canonH A B P - hR A B P| ≤ 11 * (max A.natDegree B.natDegree : ℕ) / 3 :=
  MWTate.abs_canon_sub_le (hR_double A B hΔ) P

/-- **Independence certificate on an elliptic curve over `K(X)`.** With `D = max (deg A) (deg B)`,
`C = 11 D` and the level-`k` approximations of the canonical heights read off from naive heights of
multiples, a Gram value above the error bound rules out every relation `m • P = n • Q`. -/
theorem ell_indep (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (P Q : (shortW A B).toAffine.Point) (k : ℕ)
    (hgap : let C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
      let h := hR A B
      let d := MWPair.dbl (G := (shortW A B).toAffine.Point)
      C / 3 / 4 ^ k * (|h (d^[k] P) / 4 ^ k| + |h (d^[k] Q) / 4 ^ k| + C / 3 / 4 ^ k) +
        3 * (C / 3 / 4 ^ k) / 2 * (|h (d^[k] (P + Q)) / 4 ^ k - h (d^[k] P) / 4 ^ k -
          h (d^[k] Q) / 4 ^ k| + 3 * (C / 3 / 4 ^ k) / 2) <
      |h (d^[k] P) / 4 ^ k * (h (d^[k] Q) / 4 ^ k) - ((h (d^[k] (P + Q)) / 4 ^ k -
          h (d^[k] P) / 4 ^ k - h (d^[k] Q) / 4 ^ k) / 2) ^ 2|)
    (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 :=
  MWPair.indep_of_approx (hR_double A B hΔ) (hR_par A B hΔ) P Q k hgap m n hrel

end FFHeight
