import RischTragerBronstein.Liouville.ExponentialPoly
import RischTragerBronstein.Liouville.PrimitivePoly
import RischTragerBronstein.Elementary.Algebraic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Transcendence criteria from the derivation

* `transcendental_of_deriv_ne_zero`: over a field of constants, an element with nonzero derivative
  is transcendental (an algebraic element over constants is a constant).
* `transcendental_exponential`: a nonzero `t` with `t′ = η t` is transcendental over `F` as soon as
  no equation `b′ = n η b` (`n ≥ 1`) has a nonzero solution in `F`. (If `t` were algebraic, the
  constant term `b₀` of its minimal polynomial of degree `n` would satisfy `b₀′ = n η b₀`.)
-/

open Polynomial

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

theorem transcendental_of_deriv_ne_zero (hF : ∀ a : F, a′ = 0) {x : E} (hx : x′ ≠ 0) :
    Transcendental F x := by
  intro halg
  have hint : IsIntegral F x := halg.isIntegral
  have hsep : (minpoly F x).Separable := (minpoly.irreducible hint).separable
  exact hx (deriv_eq_zero_of_aeval_eq_zero (minpoly F x) (fun i ↦ hF _) x (minpoly.aeval F x)
    (hsep.aeval_derivative_ne_zero (minpoly.aeval F x)))

/-- For monic `P` of degree `n`, `P′ - n η P` has smaller degree (derivation with `t′ = η t`). -/
lemma degree_implicitDeriv_sub_lt (η : F) {P : F[X]} (hm : P.Monic) :
    (implicitDeriv (C η * X) P - C (P.natDegree * η) * P).degree < P.degree := by
  rw [degree_eq_natDegree hm.ne_zero, degree_lt_iff_coeff_zero]
  intro m hm'
  have hm'' : P.natDegree ≤ m := by exact_mod_cast hm'
  rw [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul]
  rcases hm''.eq_or_lt with h | h
  · rw [← h, hm.coeff_natDegree]; simp; ring
  · rw [coeff_eq_zero_of_natDegree_lt h]; simp

theorem transcendental_exponential (η : F) {t : E} (ht0 : t ≠ 0)
    (ht : t′ = algebraMap F E η * t)
    (hhom : ∀ n : ℕ, n ≠ 0 → ∀ b : F, b′ = n * η * b → b = 0) : Transcendental F t := by
  intro halg
  have hint : IsIntegral F t := halg.isIntegral
  set P := minpoly F t with hP
  have hmonic : P.Monic := minpoly.monic hint
  have hn : P.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht]
  -- `P′(t) = 0`, for the derivation of `F[X]` with `X′ = η X`
  have h1 : aeval t (implicitDeriv (C η * X) P) = 0 := by
    rw [← deriv_aeval_eq_implicitDeriv t (C η * X) hw P, hP, minpoly.aeval, map_zero]
  have hQ : implicitDeriv (C η * X) P - C (P.natDegree * η) * P = 0 := by
    by_contra hne
    have haev : aeval t (implicitDeriv (C η * X) P - C (P.natDegree * η) * P) = 0 := by
      rw [map_sub, h1, map_mul, hP, minpoly.aeval, mul_zero, sub_zero]
    exact absurd (minpoly.degree_le_of_ne_zero F t hne haev)
      (not_le.mpr (degree_implicitDeriv_sub_lt η hmonic))
  -- the constant term solves `b′ = n η b`
  have hc := congrArg (fun Q : F[X] ↦ Q.coeff 0) hQ
  simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, Nat.cast_zero, zero_mul,
    mul_zero, add_zero, coeff_zero] at hc
  have hb0 : P.coeff 0 = 0 := hhom P.natDegree hn _ (sub_eq_zero.mp hc)
  exact ht0 ((minpoly.coeff_zero_eq_zero hint).mp hb0)

/-- For monic `P`, `P′` has smaller degree (derivation with `t′ = η ∈ F`). -/
lemma degree_implicitDeriv_C_lt (η : F) {P : F[X]} (hm : P.Monic) :
    (implicitDeriv (C η) P).degree < P.degree := by
  rw [degree_eq_natDegree hm.ne_zero, degree_lt_iff_coeff_zero]
  intro m hm'
  have hm'' : P.natDegree ≤ m := by exact_mod_cast hm'
  rw [coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < m + 1)]
  rcases hm''.eq_or_lt with h | h
  · rw [← h, hm.coeff_natDegree]; simp
  · rw [coeff_eq_zero_of_natDegree_lt h]; simp

/-- A primitive `t` (`t′ = η ∈ F`) is transcendental over `F` unless `η` is a derivative in `F`.
(If `t` were algebraic of degree `n`, with minimal polynomial `Xⁿ + b Xⁿ⁻¹ + …`, then
`(-b / n)′ = η`.) -/
theorem transcendental_primitive (η : F) {t : E} (ht : t′ = algebraMap F E η)
    (hη : ∀ b : F, b′ ≠ η) : Transcendental F t := by
  intro halg
  have hint : IsIntegral F t := halg.isIntegral
  set P := minpoly F t with hP
  have hmonic : P.Monic := minpoly.monic hint
  have hpos : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht]
  have h1 : aeval t (implicitDeriv (C η) P) = 0 := by
    rw [← deriv_aeval_eq_implicitDeriv t (C η) hw P, hP, minpoly.aeval, map_zero]
  have hQ : implicitDeriv (C η) P = 0 := by
    by_contra hne
    exact absurd (minpoly.degree_le_of_ne_zero F t hne h1)
      (not_le.mpr (degree_implicitDeriv_C_lt η hmonic))
  obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  have hc := congrArg (fun Q : F[X] ↦ Q.coeff n) hQ
  simp only [coeff_implicitDeriv_C, coeff_zero] at hc
  have hlead : P.coeff (n + 1) = 1 := by rw [← hn]; exact hmonic.coeff_natDegree
  rw [hlead, one_mul] at hc
  have hn0 : ((n : F) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  refine hη (-(P.coeff n) / ((n : F) + 1)) ?_
  have hconst : (((n : F) + 1))′ = 0 := by
    rw [← Nat.cast_succ]; exact Derivation.map_natCast _ _
  have hdiv := Derivation.leibniz_div_const (Differential.deriv (R := F)) (-(P.coeff n))
    ((n : F) + 1) hconst
  rw [map_neg, smul_eq_mul] at hdiv
  rw [hdiv]
  field_simp
  linear_combination -hc

end Differential
