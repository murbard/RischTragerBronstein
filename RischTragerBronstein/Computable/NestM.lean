import RischTragerBronstein.Computable.NestP

/-!
# Mixed towers with nested data: the algorithm

`K₀ = ℚ(x)`, `Kₘ₊₁ = Kₘ(tₘ)` where each level is

* a primitive `tₘ′ = ηₘ`, `ηₘ ∈ Kₘ` (`KindN.prim`), or
* an exponential `tₘ = exp aₘ`, `tₘ′ = aₘ′ tₘ`, `aₘ ∈ Kₘ` (`KindN.exp`): `exp (eˣ)`,
  `exp (x + eˣ)`, `exp (log x · eˣ)`, …

The derivation of `Kₘ[tₘ]` is given by the polynomial `wK` (`[ηₘ]` or `[0, aₘ′]`); the operations
of every level are built from it, and the constant systems are solved as for primitive towers.
-/

namespace Tower.NestM

open CPoly Tower.PrimN Tower.NestP

/-- The kind of the level-`m` generator, with its data in `Kₘ`. -/
inductive KindN (m : ℕ) where
  | prim (η : Code (m + 1))
  | exp (a : Code (m + 1))

/-- The derivative of `tₘ`, as a polynomial in `tₘ`. -/
def wK {m : ℕ} (O : COps (Code (m + 1))) : KindN m → GPoly (Code (m + 1))
  | .prim η => [η]
  | .exp a => [O.zero, O.deriv a]

/-- The operations of `Kₘ`. -/
def opsM (ks : (m : ℕ) → KindN m) : (m : ℕ) → COps (Code (m + 1))
  | 0 => ops₁g ℚ
  | m + 1 => (opsM ks m).monomial (wK (opsM ks m) (ks m))

/-- **Columns of the constant system** `∑ cⱼ vⱼ = 0` over `ℚ`. -/
def colsOf (ks : (m : ℕ) → KindN m) : (m : ℕ) → List (Code (m + 1)) → List (CPoly ℚ)
  | 0, vs =>
    cross CPoly.mul [1] (vs.map fun v ↦
      if CPoly.isZero (v : GFrac ℚ).2 then (([] : CPoly ℚ), ([1] : CPoly ℚ)) else v)
  | m + 1, vs =>
    let O := opsM ks m
    let N := cross (GPoly.mul O) [O.one] (vs.map fun v ↦
      if GPoly.isZero O v.2 then (([] : GPoly (Code (m + 1))), [O.one]) else v)
    let K := (N.map List.length).foldr max 0
    let blocks := (List.range K).map fun k ↦ colsOf ks m (N.map fun p ↦ p.getD k O.zero)
    glueU vs.length (maxLen blocks) blocks

/-- **A basis of the constant solutions** of `∑ cⱼ vⱼ = 0`, `vⱼ ∈ Kₘ`. -/
def consys (ks : (m : ℕ) → KindN m) (m : ℕ) (vs : List (Code (m + 1))) : List (CPoly ℚ) :=
  nullBasis (colsOf ks m vs)

end Tower.NestM
