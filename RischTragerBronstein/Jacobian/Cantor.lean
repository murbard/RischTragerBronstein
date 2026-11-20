import RischTragerBronstein.Jacobian.PrincipalTest

/-!
# Cantor's algorithm (untrusted)

Mumford representation `(u, v)` of reduced divisor classes on `y² = f(x)` (`deg f = 2g + 1`),
composition and reduction (Cantor), and an order search by repeated addition. Used only to
*propose* orders, which are then verified by `principalC` (see `TorsionDecide.lean`).
-/

namespace Jac.Cantor

open CPoly

variable {F : Type*} [Field F] [DecidableEq F]

/-- Monic normalisation. -/
def monic (u : CPoly F) : CPoly F := let u := trim u; smul (lead u)⁻¹ u

/-- `a mod u`. -/
def cmod (a u : CPoly F) : CPoly F := trim (divMod a u).2

/-- `a div u`. -/
def cdiv (a u : CPoly F) : CPoly F := trim (divMod a u).1

/-- Degree of a trimmed polynomial (`0` for `0`). -/
def deg (u : CPoly F) : ℕ := (trim u).length - 1

/-- Composition of `(u₁, v₁)` and `(u₂, v₂)`. -/
def compose (f : CPoly F) (D₁ D₂ : CPoly F × CPoly F) : CPoly F × CPoly F :=
  let (u₁, v₁) := D₁
  let (u₂, v₂) := D₂
  let (d₀, e₁, e₂) := egcd u₁ u₂
  let (d, c₁, c₂) := egcd d₀ (add v₁ v₂)
  let s₁ := mul c₁ e₁
  let s₂ := mul c₁ e₂
  let s₃ := c₂
  let u := monic (cdiv (mul u₁ u₂) (mul d d))
  let v := cmod (cdiv (add (add (mul (mul s₁ u₁) v₂) (mul (mul s₂ u₂) v₁))
    (mul s₃ (add (mul v₁ v₂) f))) d) u
  (u, v)

/-- Reduction to degree `≤ g`. -/
def reduce (f : CPoly F) (g : ℕ) : ℕ → CPoly F × CPoly F → CPoly F × CPoly F
  | 0, D => D
  | fuel + 1, (u, v) =>
    if deg u ≤ g then (u, v)
    else
      let u' := monic (cdiv (sub f (mul v v)) u)
      reduce f g fuel (u', cmod (neg v) u')

/-- Addition in the Jacobian. -/
def addJ (f : CPoly F) (g : ℕ) (D₁ D₂ : CPoly F × CPoly F) : CPoly F × CPoly F :=
  let D := compose f D₁ D₂
  reduce f g (deg D.1 + 1) D

/-- The zero class. -/
def zeroJ : CPoly F × CPoly F := ([1], [])

/-- Is the class zero? -/
def isZeroJ (D : CPoly F × CPoly F) : Bool := deg D.1 == 0

/-- `n · D`. -/
def nsmulJ (f : CPoly F) (g : ℕ) (D : CPoly F × CPoly F) : ℕ → CPoly F × CPoly F
  | 0 => zeroJ
  | n + 1 => addJ f g (nsmulJ f g D n) D

/-- The class of `∑ kᵢ (xᵢ, yᵢ) − (∑ kᵢ) ∞`. -/
def classOf (f : CPoly F) (g : ℕ) (Γ : EDiv F) : CPoly F × CPoly F :=
  Γ.foldr (fun q acc ↦ addJ f g acc (nsmulJ f g ([-q.1, 1], [q.2.1]) q.2.2)) zeroJ

/-- The order of `D` (searching `1, …, bound`). -/
def orderJ (f : CPoly F) (g : ℕ) (D : CPoly F × CPoly F) (bound : ℕ) : Option ℕ :=
  let rec go : ℕ → ℕ → CPoly F × CPoly F → Option ℕ
    | 0, _, _ => none
    | fuel + 1, k, acc => if isZeroJ acc then some k else go fuel (k + 1) (addJ f g acc D)
  go bound 1 D

end Jac.Cantor
