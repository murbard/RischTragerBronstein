import RischTragerBronstein.Computable.MixN
import RischTragerBronstein.Computable.NullSpace

/-!
# Towers of primitives with nested data: the algorithm

`K₀ = ℚ(x)`, `Kₘ₊₁ = Kₘ(tₘ)` with `tₘ′ = ηₘ ∈ Kₘ` (**any** element of the level below, given by a
code `ηs m : Code (m + 1)`): `log (log x)`, `li x = ∫ 1/log x`, … The parametric problems are
solved at every level:

* `colsOf ηs m vs` / `consys`: the **constant linear system** `∑ cⱼ vⱼ = 0`, `vⱼ ∈ Kₘ`, reduced to
  a system over `ℚ` by clearing denominators and comparing coefficients level by level; its
  solutions (over any field of constants) are the `nullBasis` combinations.
* `paramLim ηs m W`: **parametric limited integration**: a basis of the pairs `(c, y)`,
  `y′ = ∑ cᵢ wᵢ` (up to constants in `y`). At the base: rational integration and a constant
  system on the logarithmic parts. At level `m + 1`: Hermite reduction of every `wᵢ`, a constant
  system on the simple parts, then `paramPoly`: the polynomial problem `Q′ = ∑ cᵢ Pᵢ`, top-down,
  each coefficient equation `Yⱼ′ + (j+1) Yⱼ₊₁ η = ∑ cᵢ Pᵢⱼ` being a parametric limited
  integration one level down.
-/

namespace Tower.NestP

open CPoly Tower.PrimN

/-- The operations of `Kₘ` (`tₘ′ = ηs m`). -/
def opsQ (ηs : (m : ℕ) → Code (m + 1)) : (m : ℕ) → COps (Code (m + 1))
  | 0 => ops₁g ℚ
  | m + 1 => (opsQ ηs m).monomial [ηs m]

/-- Pad (or cut) a coefficient list to length `L`. -/
def padL (L : ℕ) (p : CPoly ℚ) : CPoly ℚ := p.take L ++ List.replicate (L - p.length) 0

/-- The product of the second components. -/
def prodD {β : Type} (mul : β → β → β) (one : β) (l : List (β × β)) : β :=
  l.foldr (fun p acc ↦ mul p.2 acc) one

/-- The cleared numerators `nⱼ ∏_{k ≠ j} dₖ`. -/
def cross {β : Type} (mul : β → β → β) (one : β) : List (β × β) → List β
  | [] => []
  | (n, d) :: rest => mul n (prodD mul one rest) :: (cross mul one rest).map fun y ↦ mul y d

/-- Glue column blocks of uniform length `L`: column `j` is the concatenation of the padded
`j`-th columns of the blocks. -/
def glueU (n L : ℕ) : List (List (CPoly ℚ)) → List (CPoly ℚ)
  | [] => List.replicate n []
  | B :: Bs => List.zipWith (fun a r ↦ padL L a ++ r) B (glueU n L Bs)

/-- The maximal length of the columns of the blocks. -/
def maxLen (blocks : List (List (CPoly ℚ))) : ℕ :=
  (blocks.map fun B ↦ (B.map List.length).foldr max 0).foldr max 0

/-- **Columns of the constant system** `∑ cⱼ vⱼ = 0` over `ℚ`. -/
def colsOf (ηs : (m : ℕ) → Code (m + 1)) : (m : ℕ) → List (Code (m + 1)) → List (CPoly ℚ)
  | 0, vs =>
    cross CPoly.mul [1] (vs.map fun v ↦
      if CPoly.isZero (v : GFrac ℚ).2 then (([] : CPoly ℚ), ([1] : CPoly ℚ)) else v)
  | m + 1, vs =>
    let O := opsQ ηs m
    let N := cross (GPoly.mul O) [O.one] (vs.map fun v ↦
      if GPoly.isZero O v.2 then (([] : GPoly (Code (m + 1))), [O.one]) else v)
    let K := (N.map List.length).foldr max 0
    let blocks := (List.range K).map fun k ↦ colsOf ηs m (N.map fun p ↦ p.getD k O.zero)
    glueU vs.length (maxLen blocks) blocks

/-- **A basis of the constant solutions** of `∑ cⱼ vⱼ = 0`, `vⱼ ∈ Kₘ`. -/
def consys (ηs : (m : ℕ) → Code (m + 1)) (m : ℕ) (vs : List (Code (m + 1))) : List (CPoly ℚ) :=
  nullBasis (colsOf ηs m vs)

/-! ### Parametric limited integration -/

/-- `∑ eᵢ aᵢ` for codes, `eᵢ ∈ ℚ`. -/
def lcombCode {α : Type} (O : COps α) (cst : ℚ → α) (e : List ℚ) (as : List α) : α :=
  (List.zipWith (fun q a ↦ O.mul (cst q) a) e as).foldr O.add O.zero

/-- `∑ eᵢ pᵢ` for polynomials over codes. -/
def lcombGP {α : Type} (O : COps α) (cst : ℚ → α) (e : List ℚ) (ps : List (GPoly α)) : GPoly α :=
  (List.zipWith (fun q p ↦ GPoly.smul O (cst q) p) e ps).foldr (GPoly.add O) []

/-- `∑ₖ δₖ γₖ` for vectors of length `n`. -/
def vcomb (n : ℕ) (δ : List ℚ) (γs : List (List ℚ)) : List ℚ :=
  (List.range n).map fun i ↦ (List.zipWith (fun d γ ↦ d * γ.getD i 0) δ γs).sum

/-- The unit vector `eᵢ` of length `n`. -/
def unitV (n i : ℕ) : List ℚ := (List.range n).map fun j ↦ if j = i then 1 else 0

/-- One step of the polynomial problem: from a basis of the solutions of the equations of
degree `≥ j + 1` to one of degree `≥ j` (equation `j`: `Yⱼ′ = ∑ cᵢ Pᵢⱼ - (j+1) Yⱼ₊₁ η`). -/
def polyStep {α : Type} (O : COps α) (cst : ℚ → α) (η : α)
    (lim : List α → List (List ℚ × α)) (n : ℕ) (Ps : List (GPoly α)) (j : ℕ)
    (B : List (List ℚ × GPoly α)) : List (List ℚ × GPoly α) :=
  let ws := B.map fun b ↦ O.add (lcombCode O cst b.1 (Ps.map fun P ↦ P.getD j O.zero))
    (O.neg (O.mul (cst ((j : ℚ) + 1)) (O.mul (b.2.getD (j + 1) O.zero) η)))
  ((lim ws).map fun r ↦ (vcomb n r.1 (B.map Prod.fst),
    GPoly.add O (lcombGP O cst r.1 (B.map Prod.snd)) (GPoly.monomial O j r.2))) ++
    [(List.replicate n 0, GPoly.monomial O j O.one)]

/-- The degree loop of the polynomial problem, `j = L - 1, …, 0`. -/
def polyLoop {α : Type} (O : COps α) (cst : ℚ → α) (η : α)
    (lim : List α → List (List ℚ × α)) (n : ℕ) (Ps : List (GPoly α)) :
    ℕ → List (List ℚ × GPoly α) → List (List ℚ × GPoly α)
  | 0, B => B
  | j + 1, B => polyLoop O cst η lim n Ps j (polyStep O cst η lim n Ps j B)

/-- **The parametric polynomial problem** `Q′ = ∑ cᵢ Pᵢ` over a primitive `t′ = η`. -/
def paramPoly {α : Type} (O : COps α) (cst : ℚ → α) (η : α)
    (lim : List α → List (List ℚ × α)) (Ps : List (GPoly α)) : List (List ℚ × GPoly α) :=
  let n := Ps.length
  let L := (Ps.map List.length).foldr max 0
  polyLoop O cst η lim n Ps L
    (((List.range n).map fun i ↦ (unitV n i, ([] : GPoly α))) ++
      [(List.replicate n 0, GPoly.monomial O L O.one)])

/-- The initial basis of the degree loop. -/
def baseB' {α : Type} (O : COps α) (n L : ℕ) : List (List ℚ × GPoly α) :=
  ((List.range n).map fun i ↦ (unitV n i, ([] : GPoly α))) ++
    [(List.replicate n 0, GPoly.monomial O L O.one)]

/-- The constant `q` at level `m`. -/
def cstN (m : ℕ) (q : ℚ) : Code (m + 1) := constC (m + 1) q

/-- The logarithmic part `r / s` of the rational integral. -/
def logPart (w : Code 1) : Code 1 := ((ratInt w).r, (ratInt w).s)

/-- **Parametric limited integration** in `Kₘ`. -/
def paramLim (ηs : (m : ℕ) → Code (m + 1)) : (m : ℕ) → List (Code (m + 1)) →
    List (List ℚ × Code (m + 1))
  | 0, W =>
    (consys ηs 0 (W.map logPart)).map fun u ↦
      let e := (List.range W.length).map fun i ↦ u.getD i 0
      (e, lcombCode (ops₁g ℚ) (cstN 0) e (W.map fun w ↦ ratPart (ratInt w)))
  | m + 1, W =>
    let O := opsQ ηs m
    let O' := opsQ ηs (m + 1)
    let n := W.length
    let H := W.map fun w ↦
      let w' := if GPoly.isZero O w.2 then (([] : GPoly (Code (m + 1))), [O.one]) else w
      GPoly.hermite O [ηs m] w'.1 w'.2
    let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
    let U := consys ηs (m + 1)
      ((List.zip QR H).map fun p ↦ ((p.1.2, p.2.s) : Code (m + 2)))
    let E := U.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
    let Pu := E.map fun e ↦ lcombGP O (cstN m) e (QR.map Prod.fst)
    let Gu := E.map fun e ↦ lcombCode O' (cstN (m + 1)) e
      (H.map fun h ↦ ((h.gn, h.gd) : Code (m + 2)))
    (paramPoly O (cstN m) (ηs m) (paramLim ηs m) Pu).map fun r ↦
      (vcomb n r.1 E, O'.add (lcombCode O' (cstN (m + 1)) r.1 Gu) ((r.2, [O.one]) : Code (m + 2)))

/-! ### Parametric elementary integration -/

/-- A common multiple of `a` and `b` (the least one when the model's gcd is exact). -/
def lcmG {α : Type} (O : COps α) (a b : GPoly α) : GPoly α :=
  GPoly.mul O a (GPoly.divMod O b (GPoly.egcd O a b).1).1

/-- A common multiple of a list of polynomials. -/
def lcmList {α : Type} (O : COps α) (l : List (GPoly α)) : GPoly α := l.foldr (lcmG O) [O.one]

/-- The residue test polynomial `r^κ ∂ₜ s - ∂ₜ r s^κ` (linear in `r`). -/
def residueTestCode {α : Type} (O : COps α) (r s : GPoly α) : GPoly α :=
  GPoly.sub O (GPoly.mul O (GPoly.mapD O r) (GPoly.derivX O s))
    (GPoly.mul O (GPoly.derivX O r) (GPoly.mapD O s))

/-- The degree loop from stage `k + 1` down to stage `1`. -/
def polyDown1 {α : Type} (O : COps α) (cst : ℚ → α) (η : α)
    (lim : List α → List (List ℚ × α)) (n : ℕ) (Ps : List (GPoly α)) :
    ℕ → List (List ℚ × GPoly α) → List (List ℚ × GPoly α)
  | 0, B => B
  | k + 1, B => polyDown1 O cst η lim n Ps k (polyStep O cst η lim n Ps (k + 1) B)

/-- **The parametric elementary polynomial problem** over a primitive `t′ = η`: a basis of the
parameters `c` for which `∑ cᵢ Pᵢ = Q′ + b` with `b - e η` elementary one level down. -/
def polyElem {α : Type} (O : COps α) (cst : ℚ → α) (η : α)
    (lim : List α → List (List ℚ × α)) (elem : List α → List (List ℚ)) (Ps : List (GPoly α)) :
    List (List ℚ) :=
  let n := Ps.length
  let L := max 1 ((Ps.map List.length).foldr max 0)
  let B1 := polyDown1 O cst η lim n Ps (L - 1) (baseB' O n L)
  let ws := B1.map fun b ↦ O.add (lcombCode O cst b.1 (Ps.map fun P ↦ P.getD 0 O.zero))
    (O.neg (O.mul (b.2.getD 1 O.zero) η))
  (elem ws).map fun β ↦ vcomb n β (B1.map Prod.fst)

/-- **Parametric elementary integration** in `Kₘ`: a basis of the `c ∈ ℚⁿ` (complete over the
constants) for which `∑ cᵢ wᵢ` has an elementary integral. -/
def paramElem (ηs : (m : ℕ) → Code (m + 1)) : (m : ℕ) → List (Code (m + 1)) → List (List ℚ)
  | 0, W => (List.range W.length).map (unitV W.length)
  | m + 1, W =>
    let O := opsQ ηs m
    let n := W.length
    let H := W.map fun w ↦
      let w' := if GPoly.isZero O w.2 then (([] : GPoly (Code (m + 1))), [O.one]) else w
      GPoly.hermite O [ηs m] w'.1 w'.2
    let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
    let S := lcmList O (H.map fun h ↦ h.s)
    if GPoly.squarefreeCheck O S && H.all (fun h ↦ GPoly.isZero O (GPoly.divMod O S h.s).2) then
      let N := (List.zip QR H).map fun p ↦ GPoly.mul O p.1.2 (GPoly.divMod O S p.2.s).1
      let Tt := N.map fun Ni ↦
        (GPoly.divMod O (residueTestCode O (GPoly.residuePoly O [ηs m] Ni S) S) S).2
      let U1 := consys ηs (m + 1) (Tt.map fun T ↦ ((T, [O.one]) : Code (m + 2)))
      let E1 := U1.map fun u ↦ (List.range n).map fun i ↦ u.getD i 0
      let Pu := E1.map fun e ↦ lcombGP O (cstN m) e (QR.map Prod.fst)
      (polyElem O (cstN m) (ηs m) (paramLim ηs m) (paramElem ηs m) Pu).map fun δ ↦
        vcomb n δ E1
    else []

/-- **Independence certificate** for the nested tower of height `n`: for each `m < n`, `ηₘ` has no
antiderivative in `Kₘ` (every basis vector of the parametric problem `y′ = c ηₘ` has `c = 0`). -/
def nestCert (ηs : (m : ℕ) → Code (m + 1)) (n : ℕ) : Bool :=
  (List.range n).all fun m ↦ (paramLim ηs m [ηs m]).all fun r ↦ r.1.getD 0 0 == 0

/-- **Does `A ∈ Kₘ` have an elementary integral?** (`[1]` is in the span of the basis for `[A]`.) -/
def elemN (ηs : (m : ℕ) → Code (m + 1)) (m : ℕ) (A : Code (m + 1)) : Bool :=
  (paramElem ηs m [A]).any fun e ↦ e.getD 0 0 ≠ 0

end Tower.NestP

