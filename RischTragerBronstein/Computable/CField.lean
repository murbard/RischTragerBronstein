import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic.Ring

/-!
# Computable models of differential fields, and polynomials over them

Towers of extensions need coefficients that are themselves computed objects (elements of `C(x)`,
of `C(x)(t₁)`, …), not elements of a field with decidable equality given in advance. A
`CField α K` is a **computable model**: a type `α` of codes with executable operations, and a
semantics `sem : α → K` into a genuine differential field `K` that every operation respects,
together with a correct zero test. Different codes may denote the same element.

`GPoly α := List α` are polynomials with coefficients in the model; `GPoly.toPoly` interprets them
in `K[X]`, and the arithmetic (`add`, `smul`, `mul`, `neg`, `sub`), the formal derivative
`derivX`, and the coefficientwise derivation `mapD` are proved correct. With
`Differential.implicitDeriv` this gives the derivation of `K[t]`, `t′ = w`:
`D P = mapD P + w * derivX P`.

The base instance `CField.ofDecidableField` (codes = elements) shows that everything built so far
is the height-zero case of this interface.
-/

open Polynomial Differential

/-- The executable operations of a computable field: pure data, no semantics. Keeping them
separate from the (noncomputable) semantics is what lets everything built on them be evaluated. -/
structure COps (α : Type*) where
  zero : α
  one : α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α
  /-- the derivation -/
  deriv : α → α
  /-- zero test -/
  isZero : α → Bool
  natCast : ℕ → α

/-- A computable model: the operations `O` on codes `α` are interpreted in the differential field
`K` by `sem`, which every operation respects. Different codes may denote the same element. -/
structure CField (α : Type*) (K : Type*) [Field K] [Differential K] (O : COps α) where
  /-- semantics -/
  sem : α → K
  sem_zero : sem O.zero = 0
  sem_one : sem O.one = 1
  sem_add : ∀ a b, sem (O.add a b) = sem a + sem b
  sem_neg : ∀ a, sem (O.neg a) = -sem a
  sem_mul : ∀ a b, sem (O.mul a b) = sem a * sem b
  sem_inv : ∀ a, sem (O.inv a) = (sem a)⁻¹
  sem_deriv : ∀ a, sem (O.deriv a) = (sem a)′
  sem_natCast : ∀ n : ℕ, sem (O.natCast n) = (n : K)
  isZero_iff : ∀ a, O.isZero a = true ↔ sem a = 0

namespace COps

/-- Operations of a field with decidable equality and the trivial derivation. -/
def ofDecidableField (R : Type*) [Field R] [DecidableEq R] : COps R where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (-·)
  mul := (· * ·)
  inv := (·⁻¹)
  deriv := fun _ ↦ 0
  isZero := fun a ↦ decide (a = 0)
  natCast := fun n ↦ (n : R)

/-- Post-compose every operation with a normalisation `f` (which must preserve the value). -/
def normalizeBy (O : COps α) (f : α → α) : COps α where
  zero := O.zero
  one := O.one
  add a b := f (O.add a b)
  neg a := f (O.neg a)
  mul a b := f (O.mul a b)
  inv a := f (O.inv a)
  deriv a := f (O.deriv a)
  isZero := O.isZero
  natCast := O.natCast

end COps

namespace CField

/-- A field with decidable equality and the trivial derivation is its own computable model. -/
def ofDecidableField (R : Type*) [Field R] [DecidableEq R] [Differential R]
    (h0 : ∀ r : R, r′ = 0) : CField R R (COps.ofDecidableField R) where
  sem := id
  sem_zero := rfl
  sem_one := rfl
  sem_add := fun _ _ ↦ rfl
  sem_neg := fun _ ↦ rfl
  sem_mul := fun _ _ ↦ rfl
  sem_inv := fun _ ↦ rfl
  sem_deriv := fun a ↦ (h0 a).symm
  sem_natCast := fun _ ↦ rfl
  isZero_iff := fun a ↦ by simp [COps.ofDecidableField]

/-- A model of `O` is a model of `O.normalizeBy f` when `f` preserves the value. -/
def normalizeBy {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)
    (f : α → α) (hf : ∀ a, M.sem (f a) = M.sem a) : CField α K (O.normalizeBy f) where
  sem := M.sem
  sem_zero := M.sem_zero
  sem_one := M.sem_one
  sem_add a b := by simp only [COps.normalizeBy, hf, M.sem_add]
  sem_neg a := by simp only [COps.normalizeBy, hf, M.sem_neg]
  sem_mul a b := by simp only [COps.normalizeBy, hf, M.sem_mul]
  sem_inv a := by simp only [COps.normalizeBy, hf, M.sem_inv]
  sem_deriv a := by simp only [COps.normalizeBy, hf, M.sem_deriv]
  sem_natCast := M.sem_natCast
  isZero_iff := M.isZero_iff

@[simp] lemma sem_normalizeBy {α K : Type*} [Field K] [Differential K] {O : COps α}
    (M : CField α K O) (f : α → α) (hf : ∀ a, M.sem (f a) = M.sem a) (a : α) :
    (M.normalizeBy f hf).sem a = M.sem a := rfl

end CField

/-- Polynomials with coefficients in a computable model: coefficient lists, constant term first. -/
abbrev GPoly (α : Type*) := List α

namespace GPoly

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- The polynomial over `K` denoted by a list of codes. -/
noncomputable def toPoly : GPoly α → K[X]
  | [] => 0
  | a :: p => C (M.sem a) + X * toPoly p

@[simp] lemma toPoly_nil : toPoly M ([] : GPoly α) = 0 := rfl

@[simp] lemma toPoly_cons (a : α) (p : GPoly α) :
    toPoly M (a :: p) = C (M.sem a) + X * toPoly M p := rfl

section Ops

variable (O)

def add : GPoly α → GPoly α → GPoly α
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => O.add a b :: add p q

def smul (c : α) (p : GPoly α) : GPoly α := p.map (O.mul c)

def neg (p : GPoly α) : GPoly α := p.map O.neg

def sub (p q : GPoly α) : GPoly α := add O p (neg O q)

def mul : GPoly α → GPoly α → GPoly α
  | [], _ => []
  | a :: p, q => add O (smul O a q) (O.zero :: mul p q)

/-- Coefficientwise derivation. -/
def mapD (p : GPoly α) : GPoly α := p.map O.deriv

def derivXAux : ℕ → GPoly α → GPoly α
  | _, [] => []
  | n, a :: p => O.mul (O.natCast n) a :: derivXAux (n + 1) p

/-- Formal derivative with respect to the variable. -/
def derivX : GPoly α → GPoly α
  | [] => []
  | _ :: p => derivXAux O 1 p

/-- Does the list denote the zero polynomial? -/
def isZero (p : GPoly α) : Bool := p.all O.isZero

end Ops

@[simp] lemma toPoly_add (p q : GPoly α) :
    toPoly M (add O p q) = toPoly M p + toPoly M q := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add, toPoly_cons, ih, M.sem_add, C_add]; ring

@[simp] lemma toPoly_smul (c : α) (p : GPoly α) :
    toPoly M (smul O c p) = C (M.sem c) * toPoly M p := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, toPoly_cons, M.sem_mul, C_mul] at ih ⊢
    rw [ih]; ring

@[simp] lemma toPoly_neg (p : GPoly α) : toPoly M (neg O p) = -toPoly M p := by
  induction p with
  | nil => simp [neg]
  | cons a p ih =>
    simp only [neg, List.map_cons, toPoly_cons, M.sem_neg, C_neg] at ih ⊢
    rw [ih]; ring

@[simp] lemma toPoly_sub (p q : GPoly α) :
    toPoly M (sub O p q) = toPoly M p - toPoly M q := by
  simp [sub, sub_eq_add_neg]

@[simp] lemma toPoly_mul (p q : GPoly α) :
    toPoly M (mul O p q) = toPoly M p * toPoly M q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul, toPoly_add, toPoly_smul, toPoly_cons, ih, M.sem_zero, C_0]; ring

@[simp] lemma toPoly_mapD (p : GPoly α) :
    toPoly M (mapD O p) = Differential.mapCoeffs (toPoly M p) := by
  induction p with
  | nil => simp [mapD]
  | cons a p ih =>
    simp only [mapD, List.map_cons, toPoly_cons, M.sem_deriv] at ih ⊢
    rw [ih, map_add, Differential.mapCoeffs_C, Derivation.leibniz, Differential.mapCoeffs_X]
    simp only [smul_eq_mul, mul_zero, add_zero]

lemma toPoly_derivXAux (n : ℕ) (p : GPoly α) :
    toPoly M (derivXAux O n p) = C (n : K) * toPoly M p + X * derivative (toPoly M p) := by
  induction p generalizing n with
  | nil => simp [derivXAux]
  | cons a p ih =>
    simp only [derivXAux, toPoly_cons, ih, M.sem_mul, M.sem_natCast, derivative_add, derivative_C,
      derivative_mul, derivative_X, C_mul, Nat.cast_add, Nat.cast_one, C_add, C_1]
    ring

@[simp] lemma toPoly_derivX (p : GPoly α) :
    toPoly M (derivX O p) = derivative (toPoly M p) := by
  cases p with
  | nil => simp [derivX]
  | cons a p =>
    simp only [derivX, toPoly_derivXAux, toPoly_cons, derivative_add, derivative_C,
      derivative_mul, derivative_X, Nat.cast_one, C_1]
    ring

lemma isZero_iff (p : GPoly α) : isZero O p = true ↔ toPoly M p = 0 := by
  induction p with
  | nil => simp [isZero]
  | cons a p ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true] at ih ⊢
    rw [ih, M.isZero_iff, toPoly_cons]
    constructor
    · rintro ⟨h1, h2⟩; simp [h1, h2]
    · intro h
      have h0 := congrArg (fun q : K[X] ↦ q.coeff 0) h
      simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
        coeff_zero] at h0
      refine ⟨h0, ?_⟩
      rw [h0, C_0, zero_add] at h
      ext n
      have hn := congrArg (fun q : K[X] ↦ q.coeff (n + 1)) h
      simpa [coeff_X_mul] using hn

variable (O) in
/-- The derivation of `K[t]` with `t′ = w`, on codes: `D P = mapD P + w * derivX P`. -/
def derivT (w p : GPoly α) : GPoly α := add O (mapD O p) (mul O w (derivX O p))

theorem toPoly_derivT (w p : GPoly α) :
    toPoly M (derivT O w p) = Differential.implicitDeriv (toPoly M w) (toPoly M p) := by
  simp [derivT, Differential.implicitDeriv]

end GPoly
