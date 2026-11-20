import Mathlib.FieldTheory.Differential.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Hermite reduction step

Hermite reduction lowers the order of a pole by integrating by parts. One step of it is an
identity valid in an arbitrary differential field `K` (Bronstein, §2.2 and §5.3): if

  `-n * (B * u * v′ + C * v) = A`        (a Bézout relation, solvable when `gcd(u v′, v) = 1`),

then

  `A / (u * v ^ (n + 1)) = (B / v ^ n)′ + (-n * C - u * B′) / (u * v ^ n)`.

The algorithm is the iteration of this step; here we prove the step itself, once, in the generality
needed both for `K(x)` and for monomial extensions `F(t)`.
-/

namespace Differential

variable {K : Type*} [Field K] [Differential K]

/-- The derivative of a power, `(v ^ n)′ = n * v ^ (n - 1) * v′`, in successor form. -/
lemma deriv_pow_succ (v : K) (n : ℕ) : (v ^ (n + 1))′ = (n + 1 : K) * v ^ n * v′ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Derivation.leibniz, ih]
    simp only [smul_eq_mul]
    push_cast
    ring

/-- **The Hermite step.** Integration by parts lowers the pole order at `v` from `n + 1` to `n`. -/
theorem hermite_step (A B C u v : K) (n : ℕ) (hn : n ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : -(n : K) * (B * u * v′ + C * v) = A) :
    A / (u * v ^ (n + 1)) = (B / v ^ n)′ + (-(n : K) * C - u * B′) / (u * v ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hvm : v ^ (m + 1) ≠ 0 := pow_ne_zero _ hv
  rw [Derivation.leibniz_div, deriv_pow_succ, ← h]
  simp only [smul_eq_mul]
  field_simp
  push_cast
  ring

end Differential
