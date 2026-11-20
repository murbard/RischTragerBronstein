import RischTragerBronstein.Computable.GBezout
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Splitting off the special prime `t` (exponential steps)

In an exponential extension the prime `t` is special and Hermite reduction cannot lower its
multiplicity. The executable `GPoly.expSplit O A D` writes the denominator as `D = t ^ k * d₁` with
`t ∤ d₁` and splits the fraction by a Bézout relation:

  `A = u * t ^ k + v * d₁`,   i.e.   `A / D = u / d₁ + v / t ^ k`      (`expSplit_spec`).

`u / d₁` then goes to Hermite reduction (all irreducible factors of `d₁` are normal, so
`hermiteCheck_hermite` applies), and `v / t ^ k` is the Laurent part treated by Risch differential
equations.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

section Ops

variable (O : COps α)

/-- Strip the factor `t ^ k`: returns `(k, d₁)` with `D = t ^ k * d₁`. -/
def splitX : GPoly α → ℕ × GPoly α
  | [] => (0, [])
  | a :: p => if O.isZero a then ((splitX p).1 + 1, (splitX p).2) else (0, a :: p)

/-- `A / D = u / d₁ + v / t ^ k`: returns `(u, v, k, d₁)`. -/
def expSplit (A D : GPoly α) : GPoly α × GPoly α × ℕ × GPoly α :=
  let kd := splitX O D
  let uv := solveBezout O (monomial O kd.1 O.one) kd.2 A
  (uv.1, uv.2, kd.1, kd.2)

end Ops

variable {O : COps α} (M : CField α K O)

theorem toPoly_splitX (D : GPoly α) :
    toPoly M D = X ^ (splitX O D).1 * toPoly M (splitX O D).2 := by
  induction D with
  | nil => simp [splitX]
  | cons a p ih =>
    simp only [splitX]
    split_ifs with h
    · have h0 := (M.isZero_iff a).mp h
      simp only [toPoly_cons, h0, C_0, zero_add]
      rw [ih]; ring
    · simp

theorem not_X_dvd_splitX (D : GPoly α) (hD : toPoly M D ≠ 0) :
    ¬X ∣ toPoly M (splitX O D).2 := by
  induction D with
  | nil => simp at hD
  | cons a p ih =>
    simp only [splitX]
    split_ifs with h
    · have h0 := (M.isZero_iff a).mp h
      refine ih fun hp ↦ hD ?_
      simp [h0, hp]
    · intro hdvd
      have hc := X_dvd_iff.mp hdvd
      simp only [toPoly_cons, coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul,
        add_zero] at hc
      rw [(M.isZero_iff a).mpr hc] at h
      exact h rfl

/-- **Correctness of the split**: `A = u * t ^ k + v * d₁`. -/
theorem expSplit_spec (A D : GPoly α) (hD : toPoly M D ≠ 0) :
    toPoly M (expSplit O A D).1 * X ^ (expSplit O A D).2.2.1 +
        toPoly M (expSplit O A D).2.1 * toPoly M (expSplit O A D).2.2.2 = toPoly M A ∧
      toPoly M D = X ^ (expSplit O A D).2.2.1 * toPoly M (expSplit O A D).2.2.2 ∧
      ¬X ∣ toPoly M (expSplit O A D).2.2.2 := by
  have hnX := not_X_dvd_splitX M D hD
  have hsplit := toPoly_splitX M D
  have hd₁ : toPoly M (splitX O D).2 ≠ 0 := fun h ↦ hD (by rw [hsplit, h, mul_zero])
  have hcop : IsCoprime (toPoly M (monomial O (splitX O D).1 O.one)) (toPoly M (splitX O D).2) := by
    rw [toPoly_monomial, M.sem_one, C_1, one_mul]
    exact IsCoprime.pow_left ((irreducible_X.coprime_iff_not_dvd).mpr hnX)
  have hbez := solveBezout_spec M (monomial O (splitX O D).1 O.one) (splitX O D).2 A hd₁ hcop
  rw [toPoly_monomial, M.sem_one, C_1, one_mul] at hbez
  exact ⟨hbez, hsplit, hnX⟩

end GPoly
