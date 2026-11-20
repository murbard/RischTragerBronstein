import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Rat

/-!
# Independence certificates from a height pairing

The Mordell–Weil exception of the mixed deciders asks whether `m • D = n • Z` for some
`(m, n) ≠ (0, 0)` in a group of divisor classes. A relation is found by search; its absence is
certified by a symmetric `ℤ`-bilinear pairing (a height pairing) whose Gram determinant on `D, Z` is
non-zero: `gram_ne_zero_indep`. This is the algebraic layer of the plan; the pairing itself (the
canonical height on Jacobians over function fields) is the remaining analytic/geometric part.
-/

namespace MW

variable {G : Type*} [AddCommGroup G]

/-- The Gram determinant of `P, Q` for a pairing `B`. -/
def gram (B : G →+ G →+ ℚ) (P Q : G) : ℚ := B P P * B Q Q - B P Q * B Q P

/-- **A non-zero Gram determinant certifies independence**: no relation `m • P = n • Q` with
`(m, n) ≠ (0, 0)` holds, for any symmetric `ℤ`-bilinear pairing. -/
theorem gram_ne_zero_indep (B : G →+ G →+ ℚ) (hsym : ∀ P Q, B P Q = B Q P) (P Q : G)
    (hg : gram B P Q ≠ 0) (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 := by
  have h1 : (m : ℚ) * B P P = n * B Q P := by
    have := congrArg (fun x ↦ B x P) hrel
    simpa [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul] using this
  have h2 : (m : ℚ) * B P Q = n * B Q Q := by
    have := congrArg (fun x ↦ B x Q) hrel
    simpa [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul] using this
  have h3 : (m : ℚ) * B Q P = n * B Q Q := by rw [← hsym P Q]; exact h2
  have h4 : (n : ℚ) * B P Q = m * B P P := by
    -- from h1 and symmetry
    rw [hsym P Q]; exact h1.symm
  unfold gram at hg
  by_contra hne
  rcases not_and_or.mp hne with hm | hn
  · -- m ≠ 0
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    apply hg
    have e1 : B P P = n / m * B Q P := by field_simp; linarith
    have e2 : B P Q = n / m * B Q Q := by field_simp; linarith
    rw [e1, e2, hsym Q P, e2]; ring
  · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    apply hg
    have e1 : B Q Q = m / n * B P Q := by field_simp; linarith
    have e2 : B Q P = m / n * B P P := by field_simp; linarith
    rw [e1, e2, hsym P Q, e2]; ring

/-- Conversely, a relation forces the Gram determinant to vanish. -/
theorem gram_eq_zero_of_rel (B : G →+ G →+ ℚ) (hsym : ∀ P Q, B P Q = B Q P) (P Q : G)
    (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) (hrel : m • P = n • Q) : gram B P Q = 0 := by
  by_contra hg
  have := gram_ne_zero_indep B hsym P Q hg m n hrel
  rcases hmn with h | h
  · exact h this.1
  · exact h this.2

end MW
