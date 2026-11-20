import RischTragerBronstein.Torsion.AutoPrime
import RischTragerBronstein.Curves.AutoPuiseux

/-!
# Computing integral bases

`autoIntBasis Fc n k pts inf`: an integral-basis certificate for the curve `Fc`, computed from
branch certificates at the special points (`pts`) and above infinity (`inf`, for the model
`invB Fc k (k n)`):

* at each special point `a` (branches `x = a + Tᴺ`), while some constant combination
  `∑ cⱼ Bⱼ / (D (x − a))` is integral along all the branches (a linear system on the first
  `N (μ + 1)` coefficients, `nullBasis`), replace `B_{j*}` (the top index of the relation) by
  `∑ cⱼ Bⱼ` and multiply `D` and the other `Bᵢ` by `x − a`;
* above infinity, compute `δⱼ` and normalize (Trager): while the leading coefficients of the
  `Bⱼ / (D xᵟʲ)` are dependent, replace the element of largest `δ` in a relation by
  `∑ cⱼ x^{d − δⱼ} Bⱼ`;
* put the element with `δ = 0` first as `B₀ = D`, and compute the left inverses of the
  certificates.

The output is checked by `ibCheck` (which allows non-triangular bases, `CertBasisDet`); nothing
here needs a proof for soundness.
-/

namespace Curves

open CPoly Sup

section IB

variable {F : Type*} [Field F] [DecidableEq F]

/-- `c · W` for a constant `c`. -/
def scaleB (c : F) (W : BPoly F) : BPoly F := W.map (smul c)

/-- `∑ cⱼ Wⱼ`. -/
def lcombB (cs : List F) (Ws : List (BPoly F)) : BPoly F :=
  (List.zipWith scaleB cs Ws).foldr addB []

/-- One local step at `a`: a combination integral after division by `x − a`, if any. -/
def ibStepAt (n : ℕ) (Bs : List (BPoly F)) (D : CPoly F) (a : F) (c : BranchCert F) :
    Option (List (BPoly F) × CPoly F) :=
  let μ := muD D a c.N
  let R := c.N * (μ + 1)
  if c.prec < R then none else
  let cols := (List.range n).map fun j ↦ (List.range n).flatMap fun k ↦
    (List.range R).map fun t ↦ (bivEval (Bs.getD j []) (shiftC a c.N) (c.ys.getD k [])).getD t 0
  match (nullBasis cols).head? with
  | none => none
  | some w =>
    let js := (List.range n).filter fun j ↦ w.getD j 0 ≠ 0
    match js.getLast? with
    | none => none
    | some jt =>
      let comb := scaleB (w.getD jt 0)⁻¹ (lcombB w Bs)
      some ((List.range n).map (fun j ↦ if j = jt then comb else smulB [-a, 1] (Bs.getD j [])),
        mul D [-a, 1])

/-- The local loop at `a` (fuel `m`). -/
def ibLoopAt (n : ℕ) (a : F) (c : BranchCert F) : ℕ → List (BPoly F) × CPoly F →
    List (BPoly F) × CPoly F
  | 0, st => st
  | m + 1, st =>
    match ibStepAt n st.1 st.2 a c with
    | none => st
    | some st' => ibLoopAt n a c m st'

/-- The expansion of `x^{−δ} B / D` above infinity along `wt`. -/
def serInfB (k : ℕ) (B : BPoly F) (D : CPoly F) (δ N prec : ℕ) (wt : CPoly F) : CPoly F :=
  serInf B D k δ N prec wt

/-- The true pole order `δ` of `B/D` above infinity (seen on the certified branches): the
syntactic order minus the number of vanishing blocks of `N` coefficients. -/
def deltaOf (k : ℕ) (B : BPoly F) (D : CPoly F) (c : BranchCert F) : ℕ :=
  let sy := synDelta k D B
  let ords := c.ys.map fun wt ↦ ordC ((serInf B D k sy c.N c.prec wt).take (c.N * sy))
  sy - (ords.foldr min (c.N * sy)) / c.N

/-- The leading matrix above infinity (columns `j`, rows `r = k N + t`). -/
def leadInf (n k : ℕ) (Bs : List (BPoly F)) (D : CPoly F) (δs : List ℕ) (c : BranchCert F) :
    List (List F) :=
  (List.range n).map fun j ↦ (List.range (n * c.N)).map fun r ↦ matInfS Bs D k δs c r j

/-- `xᵉ`. -/
def xPow (e : ℕ) : CPoly F := List.replicate e 0 ++ [1]

/-- One normalization step above infinity. -/
def normStep (n k : ℕ) (Bs : List (BPoly F)) (D : CPoly F) (c : BranchCert F) :
    Option (List (BPoly F)) :=
  let δs := (List.range n).map fun j ↦ deltaOf k (Bs.getD j []) D c
  match (nullBasis (leadInf n k Bs D δs c)).head? with
  | none => none
  | some w =>
    let js := (List.range n).filter fun j ↦ w.getD j 0 ≠ 0
    let d := (js.map fun j ↦ δs.getD j 0).foldr max 0
    match js.find? fun j ↦ δs.getD j 0 = d with
    | none => none
    | some i =>
      let comb := (List.range n).foldr (fun j acc ↦
        if w.getD j 0 = 0 then acc else
          addB (smulB (smul (w.getD j 0 / w.getD i 0) (xPow (d - δs.getD j 0))) (Bs.getD j [])) acc) []
      some ((List.range n).map fun j ↦ if j = i then comb else Bs.getD j [])

/-- The normalization loop (fuel `m`). -/
def normLoop (n k : ℕ) (D : CPoly F) (c : BranchCert F) :
    ℕ → List (BPoly F) → List (BPoly F)
  | 0, Bs => Bs
  | m + 1, Bs =>
    match normStep n k Bs D c with
    | none => Bs
    | some Bs' => normLoop n k D c m Bs'

/-- The left inverse of the certificate matrix at a special point. -/
def ibLmAt (n : ℕ) (Bs : List (BPoly F)) (D : CPoly F) (a : F) (c : BranchCert F) :
    Option (List (List F)) :=
  leftInvL ((List.range (n * c.N)).map fun r ↦ (List.range n).map fun j ↦ matEntry Bs D a c r j) n

/-- **The integral-basis certificate** (`fuel` for the loops). -/
def autoIntBasis (Fc : BPoly F) (n k : ℕ) (pts : List (F × BranchCert F)) (inf : BranchCert F)
    (fuel : ℕ) : Option (IntBasisCert F) :=
  let B0 : List (BPoly F) := (List.range n).map fun j ↦ List.replicate j [] ++ [[1]]
  let st := pts.foldl (fun st p ↦ ibLoopAt n p.1 p.2 fuel st) (B0, [1])
  let D := st.2
  let Bs := normLoop n k D inf fuel st.1
  let δs := (List.range n).map fun j ↦ deltaOf k (Bs.getD j []) D inf
  -- the element with `δ = 0` first, normalized to `B₀ = D`
  match (List.range n).find? fun j ↦ δs.getD j 0 = 0 with
  | none => none
  | some i0 =>
    let order := i0 :: (List.range n).filter (· ≠ i0)
    let Bs' := order.map fun j ↦ if j = i0 then [D] else Bs.getD j []
    let δs' := order.map fun j ↦ δs.getD j 0
    let ptsC := pts.filterMap fun p ↦ (ibLmAt n Bs' D p.1 p.2).map fun L ↦ (p.1, p.2, L)
    (leftInvL ((List.range (n * inf.N)).map fun r ↦ (List.range n).map fun j ↦
        matInfS Bs' D k δs' inf r j) n).map fun Linf ↦
      ⟨Bs', D, δs', ptsC, inf, Linf⟩

end IB

end Curves
