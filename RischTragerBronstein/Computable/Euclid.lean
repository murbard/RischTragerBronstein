import RischTragerBronstein.Computable.CPoly

/-!
# Executable division and extended Euclidean algorithm

`CPoly.divMod` and `CPoly.egcd` over a field with decidable equality, together with the algebraic
invariants that downstream *soundness* proofs need:

* `divMod_spec`: `p = q * d + r`;
* `egcd_spec`:   `s * p + t * q = g`.

Both are fuel-bounded loops; the invariants hold for any amount of fuel, so soundness never depends
on a termination argument. (Degree bounds and `g ∣ p`, needed for *completeness*, are separate.)
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- Remove trailing zero coefficients. -/
def trim (p : CPoly R) : CPoly R := (p.reverse.dropWhile (· = 0)).reverse

/-- The monomial `c X ^ k`. -/
def monomial (k : ℕ) (c : R) : CPoly R := List.replicate k 0 ++ [c]

/-- Leading coefficient of a trimmed list (`0` for the empty list). -/
def lead (p : CPoly R) : R := p.getLastD 0

@[simp] lemma toPoly_monomial (k : ℕ) (c : R) : toPoly (monomial k c) = C c * X ^ k := by
  induction k with
  | zero => simp [monomial]
  | succ k ih =>
    simp only [monomial, List.replicate_succ, List.cons_append, toPoly_cons, C_0, zero_add] at ih ⊢
    rw [ih]; ring

lemma toPoly_append (p q : CPoly R) :
    toPoly (p ++ q) = toPoly p + X ^ p.length * toPoly q := by
  induction p with
  | nil => simp
  | cons a p ih => simp only [List.cons_append, toPoly_cons, ih, List.length_cons]; ring

lemma toPoly_dropWhile_reverse (l : List R) :
    toPoly (l.dropWhile (· = 0)).reverse = toPoly l.reverse := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = 0
    · subst h
      simp only [List.dropWhile_cons_of_pos, decide_true, List.reverse_cons, toPoly_append, ih,
        toPoly_cons, C_0, toPoly_nil]
      ring
    · simp [List.dropWhile_cons_of_neg, h]

@[simp] lemma toPoly_trim (p : CPoly R) : toPoly (trim p) = toPoly p := by
  rw [trim, toPoly_dropWhile_reverse, List.reverse_reverse]

/-- Division loop: invariant `acc * d + p` is constant. -/
def divModAux (d : CPoly R) : ℕ → CPoly R → CPoly R → CPoly R × CPoly R
  | 0, acc, p => (acc, p)
  | fuel + 1, acc, p =>
    let p := trim p
    if p.length < d.length ∨ p.length = 0 then (acc, p)
    else
      let m := monomial (p.length - d.length) (lead p / lead d)
      divModAux d fuel (add acc m) (sub p (mul m d))

/-- Division with remainder by `d` (`d` should be trimmed and nonzero). -/
def divMod (p d : CPoly R) : CPoly R × CPoly R :=
  let d := trim d
  divModAux d (p.length + 1) [] p

lemma divModAux_spec (d : CPoly R) (fuel : ℕ) (acc p : CPoly R) :
    toPoly (divModAux d fuel acc p).1 * toPoly d + toPoly (divModAux d fuel acc p).2 =
      toPoly acc * toPoly d + toPoly p := by
  induction fuel generalizing acc p with
  | zero => rfl
  | succ fuel ih =>
    simp only [divModAux]
    split_ifs with h
    · simp
    · rw [ih]; simp; ring

theorem divMod_spec (p d : CPoly R) :
    toPoly p = toPoly (divMod p d).1 * toPoly d + toPoly (divMod p d).2 := by
  have := divModAux_spec (trim d) (p.length + 1) [] p
  simp only [toPoly_trim, toPoly_nil, zero_mul, zero_add] at this
  rw [divMod, this]

/-- Extended Euclid loop on `(r₀, s₀, t₀), (r₁, s₁, t₁)`. -/
def egcdAux : ℕ → (CPoly R × CPoly R × CPoly R) → (CPoly R × CPoly R × CPoly R) →
    CPoly R × CPoly R × CPoly R
  | 0, x, _ => x
  | fuel + 1, (r₀, s₀, t₀), (r₁, s₁, t₁) =>
    if isZero r₁ then (r₀, s₀, t₀)
    else
      let qr := divMod r₀ r₁
      egcdAux fuel (r₁, s₁, t₁) (qr.2, sub s₀ (mul qr.1 s₁), sub t₀ (mul qr.1 t₁))

/-- Extended Euclidean algorithm: returns `(g, s, t)` with `s * p + t * q = g`. -/
def egcd (p q : CPoly R) : CPoly R × CPoly R × CPoly R :=
  egcdAux (p.length + q.length + 2) (p, [1], []) (q, [], [1])

lemma egcdAux_spec (P Q : R[X]) (fuel : ℕ) (x y : CPoly R × CPoly R × CPoly R)
    (hx : toPoly x.2.1 * P + toPoly x.2.2 * Q = toPoly x.1)
    (hy : toPoly y.2.1 * P + toPoly y.2.2 * Q = toPoly y.1) :
    toPoly (egcdAux fuel x y).2.1 * P + toPoly (egcdAux fuel x y).2.2 * Q =
      toPoly (egcdAux fuel x y).1 := by
  induction fuel generalizing x y with
  | zero => exact hx
  | succ fuel ih =>
    obtain ⟨r₀, s₀, t₀⟩ := x
    obtain ⟨r₁, s₁, t₁⟩ := y
    simp only [egcdAux]
    split_ifs with h
    · exact hx
    · refine ih _ _ hy ?_
      have hd := divMod_spec r₀ r₁
      simp only [toPoly_sub, toPoly_mul] at hx hy ⊢
      linear_combination hx - toPoly (divMod r₀ r₁).1 * hy + hd

theorem egcd_spec (p q : CPoly R) :
    toPoly (egcd p q).2.1 * toPoly p + toPoly (egcd p q).2.2 * toPoly q =
      toPoly (egcd p q).1 :=
  egcdAux_spec _ _ _ _ _ (by simp) (by simp)

end CPoly

-- Smoke tests over `ℚ`: (x² - 1) / (x - 1), and gcd(x² - 1, x² - 2x + 1) ~ (x - 1).
#eval CPoly.divMod ([-1, 0, 1] : CPoly ℚ) [-1, 1]
#eval CPoly.trim (CPoly.egcd ([-1, 0, 1] : CPoly ℚ) [1, -2, 1]).1
