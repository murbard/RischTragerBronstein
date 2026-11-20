import RischTragerBronstein.Computable.HexpHexpIndep2
import RischTragerBronstein.Computable.KronHead

/-!
# Two hyperexponentials with only simple poles: the independence certificate

`ηᵢ = rᵢ / sᵢ` proper with `sᵢ` squarefree (after removing the Hermite parts, which are handled by
`hexpHexpComb`). Over a common squarefree denominator `s`, `ηᵢ = Nᵢ / s`, with residue polynomials
`ρᵢ` (`s ∣ ρᵢ s′ - Nᵢ`). If `z η₁ + c η₂ = e′ / e` (`c ≠ 0`), then at every prime `p ∣ s` over any
constant field, `z ρ₁ + c ρ₂ ≡ n_p (mod p)` with `n_p ∈ ℤ`; so `a = λ ρ₁ + ρ₂` (`λ = z / c`) takes
only rational values modulo the primes of `s`.

The certificate `hexpDegen`:
* `ρ₁` takes a non-rational value (`nonRatVals s ρ₁`);
* a polynomial identity `D(Λ) ρ₁ ≡ ∑ⱼ gⱼ(Λ) (Λ ρ₁ + ρ₂)ʲ (mod s)` with `D ≠ 0` (found by
  fraction-free elimination, then checked coefficientwise in `Λ`). For `D(λ) ≠ 0`, `ρ₁` is then a
  polynomial in `a` with rational coefficients, hence takes only rational values modulo the primes of
  `s`: impossible. So `λ` is a rational root of `D`;
* at every rational root `λ` of `D`, `λ ρ₁ + ρ₂` takes a non-rational value.

This is complete in principle: if `ρ₁` is not rational-valued, the identity exists (`Λ ρ₁ + ρ₂`
separates the points where `(ρ₁, ρ₂)` differs, `Λ` transcendental), and at most one `λ` makes
`λ ρ₁ + ρ₂` rational-valued (otherwise `ρ₁` would be).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

section Defs

/-- Evaluation of a rational polynomial. -/
def evalQ (P : CPoly ℚ) (q : ℚ) : ℚ := P.foldr (fun a acc ↦ a + q * acc) 0

/-- The rational roots of `P ≠ 0` (candidates filtered by evaluation). -/
def ratRootsF (P : CPoly ℚ) : List ℚ := ((ratRootsQ P).filter fun q ↦ evalQ P q == 0).dedup

/-- `a` takes a non-rational value modulo some prime factor of `s`. -/
def nonRatVals (s a : CPoly ℚ) : Bool :=
  !isZero (divMod (ratShiftProd a (ratRootsF (findMu s a))) s).2

variable {R : Type*} [CommRing R] [DecidableEq R]

/-! Polynomials in `Λ` with coefficients in `R[x]`: lists of `CPoly R`, constant term first. -/

/-- Addition. -/
def addL : List (CPoly R) → List (CPoly R) → List (CPoly R)
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => add a b :: addL p q

/-- Multiplication by a polynomial `g(Λ) ∈ R[Λ]`. -/
def mulScal : CPoly R → List (CPoly R) → List (CPoly R)
  | [], _ => []
  | a :: g, P => addL (P.map (smul a)) ([] :: mulScal g P)

/-- `(Λ ρ₁ + ρ₂) ^ j`. -/
def powL (ρ₁ ρ₂ : CPoly R) : ℕ → List (CPoly R)
  | 0 => [[1]]
  | j + 1 => let P := powL ρ₁ ρ₂ j; addL ([] :: P.map (mul ρ₁)) (P.map (mul ρ₂))

/-- `∑ᵢ gᵢ(Λ) (Λ ρ₁ + ρ₂) ^ (j + i)`. -/
def combL (ρ₁ ρ₂ : CPoly R) : List (CPoly R) → ℕ → List (CPoly R)
  | [], _ => []
  | g :: gs, j => addL (mulScal g (powL ρ₁ ρ₂ j)) (combL ρ₁ ρ₂ gs (j + 1))

end Defs

section DefsQ

/-- The check of `D(Λ) ρ₁ ≡ ∑ⱼ gⱼ(Λ) (Λ ρ₁ + ρ₂)ʲ (mod s)`, coefficientwise in `Λ`. -/
def identCheck (s ρ₁ ρ₂ D : CPoly ℚ) (gs : List (CPoly ℚ)) : Bool :=
  (addL (mulScal D [ρ₁]) ((combL ρ₁ ρ₂ gs 0).map neg)).all fun e ↦ isZero (divMod e s).2

/-! The (untrusted) search for the identity: fraction-free Gauss–Jordan elimination over `ℚ[Λ]`. -/

/-- Normalise a row by its rational content (keeps the entries small). -/
def rowNorm (row : List (CPoly ℚ)) : List (CPoly ℚ) :=
  let cs := row.flatten
  let L := cs.foldr (fun a acc ↦ Nat.lcm a.den acc) 1
  let G := cs.foldr (fun a acc ↦ Nat.gcd ((L : ℚ) * a).num.natAbs acc) 0
  if G = 0 then row else row.map (smul ((L : ℚ) / G))

/-- Eliminate column `c` of `row` using the pivot row `P`. -/
def elimRow (c : ℕ) (P row : List (CPoly ℚ)) : List (CPoly ℚ) :=
  rowNorm (List.zipWith (fun a b ↦ sub (mul (P.getD c []) a) (mul (row.getD c []) b)) row P)

/-- Gauss–Jordan: returns the pivots `(column, row)` and the remaining rows. -/
def gaussJordan : List ℕ → List (ℕ × List (CPoly ℚ)) → List (List (CPoly ℚ)) →
    List (ℕ × List (CPoly ℚ)) × List (List (CPoly ℚ))
  | [], piv, rows => (piv, rows)
  | c :: cs, piv, rows =>
    match rows.find? (fun r ↦ !isZero (r.getD c [])) with
    | none => gaussJordan cs piv rows
    | some P =>
      let rows' := (rows.filter fun r ↦ !(r == P)).map (elimRow c P)
      let piv' := piv.map fun (c', r) ↦ (c', elimRow c P r)
      gaussJordan cs (piv' ++ [(c, P)]) rows'

/-- Solve `D ρ₁ ≡ ∑ gⱼ aʲ (mod s)` over `ℚ(Λ)`, `a = Λ ρ₁ + ρ₂`; returns the factors of `D`
(the pivots) and `g`. -/
def krylovSolve (s ρ₁ ρ₂ : CPoly ℚ) : Option (List (CPoly ℚ) × List (CPoly ℚ)) :=
  let n := (trim s).length - 1
  let cols := (List.range n).map fun j ↦ (powL ρ₁ ρ₂ j).map fun e ↦ (divMod e s).2
  let ρr := (divMod ρ₁ s).2
  let rows := (List.range n).map fun i ↦ rowNorm
    ((cols.map fun col ↦ col.map fun e ↦ e.getD i 0) ++ [[ρr.getD i 0]])
  let res := gaussJordan (List.range n) [] rows
  if res.2.all (fun r ↦ isZero (r.getD n [])) then
    let Ds := res.1.map fun (c, r) ↦ r.getD c []
    let gs := (List.range n).map fun j ↦
      match res.1.find? (fun (c, _) ↦ c == j) with
      | none => []
      | some (_, r) => res.1.foldr (fun (c', r') acc ↦
          if c' == j then acc else mul (r'.getD c' []) acc) (r.getD n [])
    some (Ds, gs)
  else none

/-- **The certificate over `ℚ`** for residue polynomials `ρ₁`, `ρ₂` modulo `s`: no `λ ∈ ℚ` makes
`λ ρ₁ + ρ₂` rational-valued modulo the primes of `s`, and neither is `ρ₁`. -/
def degenCertQ (s ρ₁ ρ₂ : CPoly ℚ) : Bool :=
  !isZero s && squarefreeCheck s && nonRatVals s ρ₁ &&
  match krylovSolve s ρ₁ ρ₂ with
  | none => false
  | some (Ds, gs) => Ds.all (fun D ↦ !isZero D) && identCheck s ρ₁ ρ₂ (Ds.foldr mul [1]) gs &&
      Ds.all fun D ↦ (ratRootsF D).all fun l ↦ nonRatVals s (add (smul l ρ₁) ρ₂)

end DefsQ

section DefsR

variable {R : Type*} [Field R] [DecidableEq R] [HasRatRoots R]

/-- The rational coefficients of `p`, if they all are rational. -/
def toRatL (p : CPoly R) : Option (CPoly ℚ) :=
  p.mapM fun r ↦ (HasRatRoots.ratRoots ([-r, 1] : CPoly R)).find? fun q ↦ (q : R) == r

/-- The residue polynomial `N (s′)⁻¹ mod s` (untrusted; checked by `hexpDegen`). -/
def resPoly (s N : CPoly R) : CPoly R :=
  let e := egcd s (deriv s)
  (divMod (mul N (smul (lead (trim e.1))⁻¹ e.2.2)) s).2

/-- A common squarefree multiple of `s₁`, `s₂` (untrusted; checked by `hexpDegen`). -/
def lcmSq (s₁ s₂ : CPoly R) : CPoly R := mul s₁ (divMod s₂ (egcd s₁ s₂).1).1

/-- **The degenerate-pair certificate** for `t₁′ = (Hn₁ / Hd₁) t₁`, `t₂′ = (Hn₂ / Hd₂) t₂`:
over the common squarefree multiple `s` of the simple-pole denominators, the residue polynomials
`ρᵢ` (`s ∣ ρᵢ s′ - rᵢ (s / sᵢ)`) are rational and satisfy `degenCertQ`, or the complete head
certificate `Kron.genResCertHead s [ρ₂, ρ₁]` (no combination `ρ₂ + λ ρ₁` is rational-valued). -/
def hexpDegen (Hn₁ Hd₁ Hn₂ Hd₂ : CPoly R) : Bool :=
  let I₁ := integrateRational Hn₁ Hd₁
  let I₂ := integrateRational Hn₂ Hd₂
  let s := lcmSq I₁.s I₂.s
  let N₁ := mul I₁.r (divMod s I₁.s).1
  let N₂ := mul I₂.r (divMod s I₂.s).1
  let ρ₁ := resPoly s N₁
  let ρ₂ := resPoly s N₂
  isZero (divMod s I₁.s).2 && isZero (divMod s I₂.s).2 &&
  isZero (divMod (sub (mul ρ₁ (deriv s)) N₁) s).2 &&
  isZero (divMod (sub (mul ρ₂ (deriv s)) N₂) s).2 &&
  match toRatL s, toRatL ρ₁, toRatL ρ₂ with
  | some sQ, some q₁, some q₂ =>
    degenCertQ sQ q₁ q₂ || (!isZero sQ && squarefreeCheck sQ && Kron.genResCertHead sQ [q₂, q₁])
  | _, _, _ => false

end DefsR


end CPoly
