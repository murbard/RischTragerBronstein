import RischTragerBronstein.Computable.LinSolve
import RischTragerBronstein.Computable.NullSpace
import RischTragerBronstein.Computable.HexpDegenerate

/-!
# Triangularizing a rational matrix (untrusted search)

`triQ n A`: a basis `b₁, …, bₙ` of `ℚⁿ` with `A bₖ ∈ span(b₁, …, bₖ)` (an invariant flag), found
from rational eigenvalues (characteristic polynomial by Faddeev–LeVerrier, rational roots) and
nullspaces; `triCQ` returns `(C, C⁻¹)` with `C A C⁻¹` upper triangular. Nothing here is trusted: the
result is checked where it is used (`zeroOK`).
-/

namespace Tower.Sys

open CPoly

/-- Matrices as functions `ℕ → ℕ → ℚ` (size `n`). -/
abbrev QMat := ℕ → ℕ → ℚ

def qmul (n : ℕ) (A B : QMat) : QMat := fun i j ↦ ((List.range n).map fun k ↦ A i k * B k j).sum

def qtr (n : ℕ) (A : QMat) : ℚ := ((List.range n).map fun i ↦ A i i).sum

/-- **The characteristic polynomial** `det(X − A)` (Faddeev–LeVerrier), constant term first. -/
def charPolyQ (n : ℕ) (A : QMat) : CPoly ℚ :=
  let step : (QMat × List ℚ) → ℕ → (QMat × List ℚ) := fun st k ↦
    -- `st.2` = coefficients `c_n, c_{n-1}, …, c_{n-k+1}` (highest first)
    let c := st.2.getLast?.getD 1
    let M : QMat := fun i j ↦ qmul n A st.1 i j + if i = j then c else 0
    let ck := -(qtr n (qmul n A M)) / (k : ℚ)
    (M, st.2 ++ [ck])
  let res := (List.range n).foldl (fun st k ↦ step st (k + 1)) ((fun _ _ ↦ 0), [1])
  res.2.reverse

/-- The column `j` of `A`, as a coefficient list. -/
def qcol (n : ℕ) (A : QMat) (j : ℕ) : CPoly ℚ := (List.range n).map fun i ↦ A i j

/-- An eigenvector of `A` for a rational eigenvalue, if any. -/
def eigvecQ (n : ℕ) (A : QMat) : Option (List ℚ) :=
  (ratRootsF (charPolyQ n A)).findSome? fun lam ↦
    let B : QMat := fun i j ↦ A i j - if i = j then lam else 0
    match nullBasis ((List.range n).map (qcol n B)) with
    | u :: _ => some ((List.range n).map fun j ↦ u.getD j 0)
    | [] => none

/-- `e_i` in `ℚⁿ`. -/
def unitV (n i : ℕ) : List ℚ := (List.range n).map fun k ↦ if k = i then 1 else 0

/-- Extend independent vectors `B` by unit vectors to a basis. -/
def extendBasis (n : ℕ) (B : List (List ℚ)) : List (List ℚ) :=
  (List.range n).foldl (fun P i ↦
    if P.length < n && (nullBasis (P ++ [unitV n i])).isEmpty then P ++ [unitV n i] else P) B

/-- The inverse of the matrix with columns `P` (columns of the inverse by `linSolve`). -/
def invCols (n : ℕ) (P : List (List ℚ)) : Option QMat :=
  ((List.range n).mapM fun i ↦ linSolve P (unitV n i)).map fun cols i j ↦
    (cols.getD j []).getD i 0

/-- **An invariant flag** of `A`: columns `b₁, …, bₙ`. -/
def triQ (n : ℕ) (A : QMat) : Option (List (List ℚ)) :=
  (List.range n).foldlM (fun B k ↦ do
    let P := extendBasis n B
    let Pinv ← invCols n P
    let Pm : QMat := fun i j ↦ (P.getD j []).getD i 0
    let A' := qmul n Pinv (qmul n A Pm)
    let m := n - k
    let u ← eigvecQ m fun i j ↦ A' (k + i) (k + j)
    let v := (List.range n).map fun r ↦ ((List.range m).map fun j ↦ u.getD j 0 * Pm r (k + j)).sum
    pure (B ++ [v])) []

/-- `(C, C⁻¹)` with `C A C⁻¹` upper triangular (rows of `C⁻¹`… as functions). -/
def triCQ (n : ℕ) (A : QMat) : Option (QMat × QMat) := do
  let B ← triQ n A
  let Ci : QMat := fun i j ↦ (B.getD j []).getD i 0
  let C ← invCols n B
  pure (C, Ci)

end Tower.Sys
