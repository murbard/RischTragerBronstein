import RischTragerBronstein.Algebraic.SupRedOracle
import RischTragerBronstein.Algebraic.SupLogExample

/-!
# A non-torsion logarithmic part, decided by the kernel

On `y² = x³ − 2` (the point `(3, 5)` has infinite order), with the two-prime torsion oracle
`torsOracle` over `ℚ`:

* `∫ (1/2 + y/10)/(x − 3) dx` is **not** elementary (its only residue is at `(3, 5)`, and
  `(3, 5) − ∞` is not torsion).
-/

open Polynomial Differential CPoly IntermediateField

namespace Sup

namespace RedExample

/-- `x³ − 2`. -/
def fM : CPoly ℚ := [-2, 0, 0, 1]

lemma toPoly_fM : CPoly.toPoly fM = X ^ 3 - 2 := by
  simp [fM, CPoly.toPoly]
  rw [show (Polynomial.C (2 : ℚ)) = (2 : ℚ[X]) from map_ofNat _ 2]; ring

lemma natDegree_fM : (CPoly.toPoly fM).natDegree = fM.length - 1 := by
  rw [toPoly_fM]; simp [fM]; compute_degree!

lemma squarefree_fM : Squarefree (CPoly.toPoly fM) := by
  rw [toPoly_fM]
  refine Polynomial.Separable.squarefree ⟨-(Polynomial.C (1 / 2 : ℚ)), Polynomial.C (1 / 6 : ℚ) * X, ?_⟩
  refine Polynomial.funext fun r ↦ ?_
  simp [derivative_X_pow]
  ring

/-- The reductions of `ℚ`. -/
def redQ : (p : ℕ) → Option (RedFns p ℚ) := fun p ↦ some (ratFns p)

/-- The candidate primes. -/
def primes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

/-- The torsion oracle. -/
def torsM : List (ℚ × ℚ × ℕ) → Option (Option ℕ) := torsOracle redQ primes 40 fM 2

lemma torsM_spec : TorsSpecN fM 2 torsM :=
  torsOracle_spec redQ (fun p _ R h ↦ by
    simp only [redQ, Option.some.injEq] at h; subst h
    exact ⟨_, ratFns_valid p⟩) primes 40 squarefree_fM (by decide)

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ (1/2 + y/10)/(x − 3) dx` is not elementary** on `y² = x³ − 2`. -/
theorem nontorsion_not_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 - 2) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    ¬HasElementaryIntegral ((1 / 2 + y / 10) / (x - 3)) := by
  have hy' : y ^ 2 = aeval x ((CPoly.toPoly fM).map (algebraMap ℚ Kc)) := by
    rw [toPoly_fM]; simp [hy, map_ofNat]
  have := superLogDecide_spec hC x y hx (algebraMap ℚ Kc) fM (by norm_num) squarefree_fM
    natDegree_fM (by decide) (by decide) hy' hgen LogExample.zeta_E torsM torsM_spec [] []
    (by decide) (by decide) (by simp) ![3] ![5] ![[[1/2], [1/10]]]
    (fun i ↦ by fin_cases i; decide) (fun i j _ ↦ Subsingleton.elim i j)
    (fun i ↦ by fin_cases i; norm_num) (fun i ↦ by fin_cases i; simp [toPoly_fM]; norm_num) false
    (by decide +kernel)
  simp only [Bool.false_eq_true, false_iff] at this
  convert this using 2
  simp [integrandE, exC, evalE_cons, evalE_X, evalE_C, CPoly.toPoly]
  ring_nf
  simp [map_ofNat]
  ring

end RedExample

end Sup
