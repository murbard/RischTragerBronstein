import RischTragerBronstein.Mixed.CurveFrac
import RischTragerBronstein.Curves.DiscC
import RischTragerBronstein.Computable.NullSpace

/-!
# The parametric Risch equation on a curve: the algorithm

`curveRde Fc h ws`: for the curve `F(x, y) = 0` (`Fc` over `ℚ`, monic in `y`), a potential `h`
and right-hand sides `ws` (curve codes), a basis of the pairs `(β, z)` with
`z′ + h′ z = ∑ βⱼ wⱼ`, `z` in the function field of the curve.

The ansatz (`rde_ansatz`): `z = ∑_{i<n, e≤E} λᵢₑ xᵉ yⁱ / (discR · Q)`, with `Q` the common
denominator of the `wⱼ`. The operator `z ↦ z′ + h′ z` is applied to each basis element with the
computable model (`curveModel`), every result is reduced modulo `F` and written as a fraction
`W(x, y)/Q(x)` (`codeW`, `codeQ`), the fractions are brought to a common denominator, and the
numerators (flattened by a Kronecker substitution) are the columns of a linear system over `ℚ`,
solved by `nullBasis`.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Alg

/-- The operations of `ℚ(x)`. -/
abbrev xOps : COps (GFrac ℚ) := xOpsR ℚ

/-- The operations of the function field of the curve `Fc`. -/
abbrev curveOps (Fc : BPoly ℚ) : COps (GPoly (GFrac ℚ)) := xOps.algExt (curveCodes Fc)

variable (Fc : BPoly ℚ)

/-- `deg_y F`. -/
def cvN : ℕ := Fc.length - 1

/-- A bound on the degrees in `x` of the coefficients of `F`. -/
def cvK : ℕ := (Fc.map fun c ↦ c.length - 1).foldr max 0

/-- A bound on `∑ᵢ deg_x Fᵢ`. -/
def cvDegB : ℕ := (Fc.map fun c ↦ c.length - 1).sum

/-- Reduction modulo `F`, trimmed: at most `n` coefficients. -/
def cvRed (a : GPoly (GFrac ℚ)) : GPoly (GFrac ℚ) :=
  GPoly.trim xOps (GPoly.algRed xOps (curveCodes Fc) a)

/-- A curve code as a fraction `(W, Q)`. -/
def fracOf (a : GPoly (GFrac ℚ)) : BPoly ℚ × CPoly ℚ := (codeW a, codeQ a)

/-- The product of the denominators of a list of fractions. -/
def prodQs : List (BPoly ℚ × CPoly ℚ) → CPoly ℚ
  | [] => [1]
  | p :: L => mul p.2 (prodQs L)

/-- The numerators over the common denominator `prodQs`. -/
def scaledWs : List (BPoly ℚ × CPoly ℚ) → List (BPoly ℚ)
  | [] => []
  | p :: L => p.1.map (mul (prodQs L)) :: (scaledWs L).map fun W ↦ W.map (mul p.2)

/-- The largest coefficient length. -/
def maxLenB (Vs : List (BPoly ℚ)) : ℕ := (Vs.map fun V ↦ (V.map List.length).foldr max 0).foldr max 0

/-- Padding to length `b`. -/
def padTo (p : CPoly ℚ) (b : ℕ) : CPoly ℚ := p ++ List.replicate (b - p.length) 0

/-- Kronecker flattening of a bivariate list with blocks of length `b`. -/
def flatV (V : BPoly ℚ) (b : ℕ) : CPoly ℚ := (V.map fun p ↦ padTo p b).flatten

/-- The bound `deg Wᵢ + k i` for a numerator. -/
def boundDW (k : ℕ) (W : BPoly ℚ) : ℕ :=
  ((List.range W.length).map fun i ↦ (W.getD i []).length - 1 + k * i).foldr max 0

/-- The data of the ansatz for right-hand sides `ws`: the denominator `discR · Q` and the degree
bound `E`. -/
def rdeDen (ws : List (GPoly (GFrac ℚ))) : CPoly ℚ :=
  mul (discRC Fc (cvN Fc) (cvK Fc)) (prodQs (ws.map fun w ↦ fracOf (cvRed Fc w)))

def rdeE (ws : List (GPoly (GFrac ℚ))) : ℕ :=
  let Qw := prodQs (ws.map fun w ↦ fracOf (cvRed Fc w))
  let DW := ((scaledWs (ws.map fun w ↦ fracOf (cvRed Fc w))).map (boundDW (cvK Fc))).foldr max 0
  (Qw.length - 1) + (DW + 1 - (Qw.length - 1)) +
    ((cvN Fc - 1) * (cvN Fc - 1) + (cvN Fc - 1)) * cvDegB Fc

/-- The basis element `xᵉ yⁱ / den`. -/
def bcode (den : CPoly ℚ) (i e : ℕ) : GPoly (GFrac ℚ) :=
  List.replicate i ([], [1]) ++ [(xPowC e, den)]

/-- All basis elements, index `i (E + 1) + e`. -/
def bcodes (den : CPoly ℚ) (n E : ℕ) : List (GPoly (GFrac ℚ)) :=
  (List.range n).flatMap fun i ↦ (List.range (E + 1)).map fun e ↦ bcode den i e

/-- The operator `z ↦ z′ + h′ z` on codes. -/
def rdeOp (h z : GPoly (GFrac ℚ)) : GPoly (GFrac ℚ) :=
  (curveOps Fc).add ((curveOps Fc).deriv z) ((curveOps Fc).mul ((curveOps Fc).deriv h) z)

/-- The columns of the linear system. -/
def rdeCols (h : GPoly (GFrac ℚ)) (ws : List (GPoly (GFrac ℚ))) : List (CPoly ℚ) :=
  let bs := bcodes (rdeDen Fc ws) (cvN Fc) (rdeE Fc ws)
  let fr := ((bs.map (rdeOp Fc h)) ++ ws.map (GPoly.neg xOps)).map fun a ↦ fracOf (cvRed Fc a)
  let Vs := scaledWs fr
  Vs.map fun V ↦ flatV V (maxLenB Vs)

/-- The solution attached to a relation `u`. -/
def rdeOut (ws : List (GPoly (GFrac ℚ))) (u : CPoly ℚ) : List ℚ × GPoly (GFrac ℚ) :=
  let n := cvN Fc
  let E := rdeE Fc ws
  ((List.range ws.length).map fun j ↦ u.getD (n * (E + 1) + j) 0,
    (List.range n).map fun i ↦ ((List.range (E + 1)).map fun e ↦ u.getD (i * (E + 1) + e) 0,
      rdeDen Fc ws))

/-- **The parametric Risch equation on the curve.** -/
def curveRde (h : GPoly (GFrac ℚ)) (ws : List (GPoly (GFrac ℚ))) :
    List (List ℚ × GPoly (GFrac ℚ)) :=
  (nullBasis (rdeCols Fc h ws)).map (rdeOut Fc ws)

end Alg

end Curves
