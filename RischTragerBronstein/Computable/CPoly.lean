import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Computable polynomials

Mathlib's `Polynomial` is noncomputable. The executable part of this development works with
coefficient lists (`CPoly R = List R`, constant coefficient first), and every operation is proved to
agree with the corresponding operation on `R[X]` through `CPoly.toPoly`. Algorithms are *run* on
`CPoly`; theorems about their output are *stated* in `R[X]` and `RatFunc R`.

Lists are not required to be normalised (trailing zeros are allowed); `CPoly.isZero` and
`CPoly.beq` decide equality of the denoted polynomials.
-/

open Polynomial

/-- Computable polynomials: coefficient lists, constant coefficient first. -/
abbrev CPoly (R : Type*) := List R

namespace CPoly

variable {R : Type*}

section Semantics

variable [CommRing R]

/-- The polynomial denoted by a coefficient list. -/
noncomputable def toPoly : CPoly R → R[X]
  | [] => 0
  | a :: p => C a + X * toPoly p

@[simp] lemma toPoly_nil : toPoly ([] : CPoly R) = 0 := rfl

@[simp] lemma toPoly_cons (a : R) (p : CPoly R) : toPoly (a :: p) = C a + X * toPoly p := rfl

lemma coeff_toPoly (p : CPoly R) (n : ℕ) : (toPoly p).coeff n = p.getD n 0 := by
  induction p generalizing n with
  | nil => simp
  | cons a p ih =>
    cases n with
    | zero => simp
    | succ n => simp [ih, coeff_X_mul]

end Semantics

section Ops

variable [CommRing R]

/-- Addition. -/
def add : CPoly R → CPoly R → CPoly R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Scalar multiplication. -/
def smul (c : R) (p : CPoly R) : CPoly R := p.map (c * ·)

/-- Negation. -/
def neg (p : CPoly R) : CPoly R := smul (-1) p

/-- Subtraction. -/
def sub (p q : CPoly R) : CPoly R := add p (neg q)

/-- Multiplication. -/
def mul : CPoly R → CPoly R → CPoly R
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- Auxiliary function for `deriv`: `derivAux n p` denotes `n p + X p′`. -/
def derivAux : ℕ → CPoly R → CPoly R
  | _, [] => []
  | n, a :: p => (n * a) :: derivAux (n + 1) p

/-- Formal derivative. -/
def deriv : CPoly R → CPoly R
  | [] => []
  | _ :: p => derivAux 1 p

@[simp] lemma toPoly_add (p q : CPoly R) : toPoly (add p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add, toPoly_cons, ih, C_add]; ring

@[simp] lemma toPoly_smul (c : R) (p : CPoly R) : toPoly (smul c p) = C c * toPoly p := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, toPoly_cons, C_mul] at ih ⊢
    rw [ih]; ring

@[simp] lemma toPoly_neg (p : CPoly R) : toPoly (neg p) = -toPoly p := by
  simp [neg]

@[simp] lemma toPoly_sub (p q : CPoly R) : toPoly (sub p q) = toPoly p - toPoly q := by
  simp [sub, sub_eq_add_neg]

@[simp] lemma toPoly_mul (p q : CPoly R) : toPoly (mul p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp only [mul, toPoly_add, toPoly_smul, toPoly_cons, ih, C_0]; ring

lemma toPoly_derivAux (n : ℕ) (p : CPoly R) :
    toPoly (derivAux n p) = C (n : R) * toPoly p + X * derivative (toPoly p) := by
  induction p generalizing n with
  | nil => simp [derivAux]
  | cons a p ih =>
    simp only [derivAux, toPoly_cons, ih, derivative_add, derivative_C, derivative_mul,
      derivative_X, C_mul, Nat.cast_add, Nat.cast_one, C_add, C_1]
    ring

@[simp] lemma toPoly_deriv (p : CPoly R) : toPoly (deriv p) = derivative (toPoly p) := by
  cases p with
  | nil => simp [deriv]
  | cons a p =>
    simp only [deriv, toPoly_derivAux, toPoly_cons, derivative_add, derivative_C, derivative_mul,
      derivative_X, Nat.cast_one, C_1]
    ring

end Ops

section Decide

variable [CommRing R] [DecidableEq R]

/-- Does the list denote the zero polynomial? -/
def isZero (p : CPoly R) : Bool := p.all (· = 0)

lemma isZero_iff (p : CPoly R) : isZero p = true ↔ toPoly p = 0 := by
  induction p with
  | nil => simp [isZero]
  | cons a p ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
    rw [ih, toPoly_cons]
    constructor
    · rintro ⟨rfl, h⟩; simp [h]
    · intro h
      have h0 := congrArg (fun q : R[X] ↦ q.coeff 0) h
      simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
        coeff_zero] at h0
      refine ⟨h0, ?_⟩
      rw [h0, C_0, zero_add] at h
      ext n
      have hn := congrArg (fun q : R[X] ↦ q.coeff (n + 1)) h
      simpa [coeff_X_mul] using hn

/-- Decidable equality of denoted polynomials. -/
def beq (p q : CPoly R) : Bool := isZero (sub p q)

lemma beq_iff (p q : CPoly R) : beq p q = true ↔ toPoly p = toPoly q := by
  rw [beq, isZero_iff, toPoly_sub, sub_eq_zero]

end Decide

end CPoly
