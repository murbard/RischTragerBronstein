import RischTragerBronstein.Algebraic.HermiteSupK
import RischTragerBronstein.Algebraic.SupRedOracle
import RischTragerBronstein.Jacobian.HypDecideAll

/-!
# The superelliptic front end

`superFront f n ζ tors A D a b` decides `∫ ∑_{j<n} (Aⱼ(x)/D(x)) yʲ dx` on `yⁿ = f(x)`:

1. the rational part `A₀/D` always has an elementary integral;
2. for `1 ≤ j < n`, Hermite reduction by linear algebra (`colsS`, `μ = j/n`):
   `Aⱼ yʲ/D = (Wⱼ yʲ/D)′ + Tⱼ yʲ/(f S)`;
3. partial fractions `Tⱼ/(f S) = Bⱼ + B₁ⱼ/f + ∑ᵢ cᵢⱼ/(x − aᵢ)` at the given roots `aᵢ` of `S`
   (re-checked by exact division, `pfSplit`);
4. `superLogDecide` on the result.

`superFront_spec`: every answer is correct.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac

namespace Sup

section Comp

variable {F : Type*} [Field F] [DecidableEq F]

/-- The residue of `T/(f S)` at `aᵢ`. -/
def pfRes (f S T : CPoly F) {m : ℕ} (a : Fin m → F) (i : Fin m) : F :=
  evalC T (a i) / (evalC f (a i) * evalC (divMod S (linC (a i))).1 (a i))

/-- Partial fractions of `T/(f S)` at the points `aᵢ` (checked by exact division): the residues
`cᵢ`, the polynomial part `B` and the part `B₁/f`. -/
def pfSplit (f S : CPoly F) {m : ℕ} (a : Fin m → F) (T : CPoly F) :
    Option (List F × CPoly F × CPoly F) :=
  if (List.finRange m).all fun i ↦ isZero (divMod S (linC (a i))).2 then
    let R := sub T (mul f (((List.finRange m).map fun i ↦
      smul (pfRes f S T a i) (divMod S (linC (a i))).1).foldr add []))
    let QR := divMod R S
    if isZero QR.2 then some (List.ofFn (pfRes f S T a), (divMod QR.1 f).1, (divMod QR.1 f).2)
    else none
  else none

/-- One component `j ≥ 1`: the Hermite solution `(W, T)` and its partial fractions. -/
def compData (f D S : CPoly F) (n j : ℕ) (Aj : CPoly F) {m : ℕ} (a : Fin m → F) :
    Option (CPoly F × List F × CPoly F × CPoly F) :=
  let nT := (mul f Aj).length + D.length + S.length + f.length + 3
  match linSolve (colsS ((j : F) / n) f D S D.length nT) (mul (mul (mul f Aj) D) S) with
  | some cs =>
    (pfSplit f S a (cs.drop D.length)).map fun r ↦ (cs.take D.length, r.1, r.2.1, r.2.2)
  | none => none

variable [CharZero F] [EllQuad.QCoords F]

/-- The data of component `k + 1`. -/
def frontDat (f : CPoly F) (n : ℕ) (A : List (CPoly F)) (D : CPoly F) {m : ℕ} (a : Fin m → F)
    (k : ℕ) : CPoly F × List F × CPoly F × CPoly F :=
  (compData f D (nbPartK f D) n (k + 1) (A.getD (k + 1) []) a).getD ([], [], [], [])

/-- **The front end.** -/
def superFront (f : CPoly F) (n : ℕ) (ζ : F) (tors : List (F × F × ℕ) → Option (Option ℕ))
    (A : List (CPoly F)) (D : CPoly F) {m : ℕ} (a b : Fin m → F) : Option Bool :=
  if (List.range (n - 1)).all fun k ↦
      (compData f D (nbPartK f D) n (k + 1) (A.getD (k + 1) []) a).isSome then
    let B : BPoly F := [] :: (List.range (n - 1)).map fun k ↦ (frontDat f n A D a k).2.2.1
    let B₁ : BPoly F := [] :: (List.range (n - 1)).map fun k ↦ (frontDat f n A D a k).2.2.2
    let G : Fin m → BPoly F := fun i ↦
      [] :: (List.range (n - 1)).map fun k ↦ [(frontDat f n A D a k).2.1.getD i 0]
    superLogDecide f n ζ tors B B₁ a b G
  else none

end Comp

end Sup
