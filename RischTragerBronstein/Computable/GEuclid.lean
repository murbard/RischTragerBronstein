import RischTragerBronstein.Computable.CFrac

/-!
# Division and extended gcd over a computable model

The executable Euclidean algorithms of `Computable/Euclid.lean`, generalised from a field with
decidable equality to polynomials `GPoly α` over an arbitrary computable model
(`COps α` / `CField α K O`). They therefore run at every level of a computable tower, e.g. on
polynomials in `t = log x` with coefficients in `ℚ(x)`.

* `GPoly.divMod_spec`: `p = q * d + r`;
* `GPoly.egcd_spec`:   `s * p + t * q = g`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

section Ops

variable (O : COps α)

/-- Remove trailing coefficients that test as zero. -/
def trim (p : GPoly α) : GPoly α := (p.reverse.dropWhile O.isZero).reverse

/-- The monomial `c X ^ k`. -/
def monomial (k : ℕ) (c : α) : GPoly α := List.replicate k O.zero ++ [c]

/-- Leading coefficient of a trimmed list. -/
def lead (p : GPoly α) : α := p.getLastD O.zero

/-- Division loop. -/
def divModAux (d : GPoly α) : ℕ → GPoly α → GPoly α → GPoly α × GPoly α
  | 0, acc, p => (acc, p)
  | fuel + 1, acc, p =>
    let p := trim O p
    if p.length < d.length ∨ p.length = 0 then (acc, p)
    else
      let m := monomial O (p.length - d.length) (O.mul (lead O p) (O.inv (lead O d)))
      divModAux d fuel (add O acc m) (sub O p (mul O m d))

/-- Division with remainder. -/
def divMod (p d : GPoly α) : GPoly α × GPoly α :=
  divModAux O (trim O d) (p.length + 1) [] p

/-- Extended Euclid loop. -/
def egcdAux : ℕ → (GPoly α × GPoly α × GPoly α) → (GPoly α × GPoly α × GPoly α) →
    GPoly α × GPoly α × GPoly α
  | 0, x, _ => x
  | fuel + 1, (r₀, s₀, t₀), (r₁, s₁, t₁) =>
    if isZero O r₁ then (r₀, s₀, t₀)
    else
      let qr := divMod O r₀ r₁
      egcdAux fuel (r₁, s₁, t₁) (qr.2, sub O s₀ (mul O qr.1 s₁), sub O t₀ (mul O qr.1 t₁))

/-- Extended Euclidean algorithm. -/
def egcd (p q : GPoly α) : GPoly α × GPoly α × GPoly α :=
  egcdAux O (p.length + q.length + 2) (p, [O.one], []) (q, [], [O.one])

end Ops

variable {O : COps α} (M : CField α K O)

@[simp] lemma toPoly_monomial (k : ℕ) (c : α) :
    toPoly M (monomial O k c) = C (M.sem c) * X ^ k := by
  induction k with
  | zero => simp [monomial]
  | succ k ih =>
    simp only [monomial, List.replicate_succ, List.cons_append, toPoly_cons, M.sem_zero, C_0,
      zero_add] at ih ⊢
    rw [ih]; ring

lemma toPoly_append (p q : GPoly α) :
    toPoly M (p ++ q) = toPoly M p + X ^ p.length * toPoly M q := by
  induction p with
  | nil => simp
  | cons a p ih => simp only [List.cons_append, toPoly_cons, ih, List.length_cons]; ring

lemma toPoly_dropWhile_reverse (l : List α) :
    toPoly M (l.dropWhile O.isZero).reverse = toPoly M l.reverse := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : O.isZero a = true
    · have h0 := (M.isZero_iff a).mp h
      simp only [List.dropWhile_cons_of_pos h, List.reverse_cons, toPoly_append, ih, toPoly_cons,
        h0, C_0, toPoly_nil]
      ring
    · simp [List.dropWhile_cons_of_neg h]

@[simp] lemma toPoly_trim (p : GPoly α) : toPoly M (trim O p) = toPoly M p := by
  rw [trim, toPoly_dropWhile_reverse, List.reverse_reverse]

lemma divModAux_spec (d : GPoly α) (fuel : ℕ) (acc p : GPoly α) :
    toPoly M (divModAux O d fuel acc p).1 * toPoly M d + toPoly M (divModAux O d fuel acc p).2 =
      toPoly M acc * toPoly M d + toPoly M p := by
  induction fuel generalizing acc p with
  | zero => rfl
  | succ fuel ih =>
    simp only [divModAux]
    split_ifs with h
    · simp
    · rw [ih]; simp; ring

theorem divMod_spec (p d : GPoly α) :
    toPoly M p = toPoly M (divMod O p d).1 * toPoly M d + toPoly M (divMod O p d).2 := by
  have := divModAux_spec M (trim O d) (p.length + 1) [] p
  simp only [toPoly_trim, toPoly_nil, zero_mul, zero_add] at this
  rw [divMod, this]

lemma egcdAux_spec (P Q : K[X]) (fuel : ℕ) (x y : GPoly α × GPoly α × GPoly α)
    (hx : toPoly M x.2.1 * P + toPoly M x.2.2 * Q = toPoly M x.1)
    (hy : toPoly M y.2.1 * P + toPoly M y.2.2 * Q = toPoly M y.1) :
    toPoly M (egcdAux O fuel x y).2.1 * P + toPoly M (egcdAux O fuel x y).2.2 * Q =
      toPoly M (egcdAux O fuel x y).1 := by
  induction fuel generalizing x y with
  | zero => exact hx
  | succ fuel ih =>
    obtain ⟨r₀, s₀, t₀⟩ := x
    obtain ⟨r₁, s₁, t₁⟩ := y
    simp only [egcdAux]
    split_ifs with h
    · exact hx
    · refine ih _ _ hy ?_
      have hd := divMod_spec M r₀ r₁
      simp only [toPoly_sub, toPoly_mul] at hx hy ⊢
      linear_combination hx - toPoly M (divMod O r₀ r₁).1 * hy + hd

theorem egcd_spec (p q : GPoly α) :
    toPoly M (egcd O p q).2.1 * toPoly M p + toPoly M (egcd O p q).2.2 * toPoly M q =
      toPoly M (egcd O p q).1 :=
  egcdAux_spec M _ _ _ _ _ (by simp [M.sem_one]) (by simp [M.sem_one])

end GPoly
