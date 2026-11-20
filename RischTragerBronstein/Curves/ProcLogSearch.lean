import RischTragerBronstein.Curves.ProcLogDecide

/-!
# Searching for log witnesses (untrusted)

For the component `j` of the residue divisor (`coord_j` of the residues along the certified
branches) and a multiplier `M`, `findWitM` looks for `u = W(x, y)/Q(x)` with
`ord u = M L coord_j(res)` along the certified branches (`L` clears the denominators): `Q` is a
product of `(x − a)^{e_a}` making all required orders of `W` nonnegative, and `W` (in the monomial
basis `xᵉ yⁱ`, `e ≤ Ew`) solves the homogeneous linear conditions "no coefficient below the
target" along the certified branches (finite and above infinity). Candidates are *checked* by
`witOK`; `decideAuto P B Ew := decideLog P (findWits P B Ew)` is therefore covered by
`decideLog_spec` (`decideAuto_spec`), whatever the search returns.
-/

open Polynomial EllQuad.QCoords

namespace Curves

open CPoly Sup

section Search

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

namespace CurveProb

variable (P : CurveProb F)

/-- Powers of a polynomial. -/
def powL (p : CPoly F) : ℕ → CPoly F
  | 0 => [1]
  | k + 1 => mul p (powL p k)

/-- The finite certified branches `(a, c, yt)`. -/
def finBranches : List (F × BranchCert F × CPoly F) :=
  P.pts.flatMap fun ac ↦ ac.2.ys.map fun yt ↦ (ac.1, ac.2, yt)

/-- `lcm` of the denominators of the `j`-th coordinates of all residues. -/
def denL (j : Fin (dim F)) : ℕ :=
  (P.finBranches.map (fun b ↦ (coord j (P.resFin b.1 b.2.1 b.2.2)).den) ++
    P.inf.ys.map (fun wt ↦ (coord j (P.resInf wt)).den)).foldr Nat.lcm 1

/-- The integer target `m · coord_j(r)`. -/
def tgt (m : ℕ) (j : Fin (dim F)) (r : F) : ℤ := ((m : ℚ) * coord j r).floor

/-- The exponent of `x − a` in `Q`. -/
def expAt (m : ℕ) (j : Fin (dim F)) (a : F) (c : BranchCert F) : ℕ :=
  ((c.ys.map fun yt ↦ (-(tgt m j (P.resFin a c yt))).toNat).foldr max 0 + c.N - 1) / c.N

/-- `Q = ∏ (x − a)^{e_a}`. -/
def qWit (m : ℕ) (j : Fin (dim F)) : CPoly F :=
  P.pts.foldr (fun ac acc ↦ mul (powL [-ac.1, 1] (P.expAt m j ac.1 ac.2)) acc) [1]

/-- The monomial basis `xᵉ yⁱ`, `i < n`, `e ≤ Ew`. -/
def wBasis (Ew : ℕ) : List (ℕ × ℕ) :=
  (List.range P.n).flatMap fun i ↦ (List.range (Ew + 1)).map fun e ↦ (i, e)

/-- Rows along a finite certified branch: coefficients `t < ord_target` of `W` vanish. -/
def wRowsFin (Ew m : ℕ) (j : Fin (dim F)) (Q : CPoly F) (b : F × BranchCert F × CPoly F) :
    List (List F) :=
  let o := tgt m j (P.resFin b.1 b.2.1 b.2.2) + (ordQFin Q b.1 b.2.1.N : ℤ)
  (List.range o.toNat).map fun t ↦
    (P.wBasis Ew).map fun ie ↦ (bivEval (basisB ie.1 ie.2) (shiftC b.1 b.2.1.N) b.2.2).getD t 0

/-- Rows above infinity. -/
def wRowsInf (Ew m : ℕ) (j : Fin (dim F)) (Q : CPoly F) (wt : CPoly F) : List (List F) :=
  let DW := Ew + P.k * (P.n - 1)
  let o := tgt m j (P.resInf wt) - ((P.inf.N * degT Q : ℕ) : ℤ) + ((P.inf.N * DW : ℕ) : ℤ)
  (List.range o.toNat).map fun t ↦
    (P.wBasis Ew).map fun ie ↦
      (bivEval (invB (basisB ie.1 ie.2) P.k DW) (shiftC 0 P.inf.N) wt).getD t 0

/-- A nonzero solution of the homogeneous system with the coefficient `r` set to `1`. -/
def homSolveAt (rows : List (List F)) (nb r : ℕ) : Option (List F) :=
  let cols := (List.range nb).map fun b ↦ rows.map fun row ↦ row.getD b 0
  match linSolve (cols.eraseIdx r) (neg (cols.getD r [])) with
  | none => none
  | some cs => some (cs.take r ++ [1] ++ cs.drop r)

/-- The first nonzero solution found. -/
def homSolve (rows : List (List F)) (nb : ℕ) : Option (List F) :=
  (List.range nb).foldr (fun r acc ↦ match homSolveAt rows nb r with
    | some cs => some cs
    | none => acc) none

/-- The combination `∑ c_b xᵉ yⁱ`. -/
def combW (Ew : ℕ) (cs : List F) : BPoly F :=
  (List.range (P.wBasis Ew).length).foldr (fun b acc ↦
    addB (smulB [cs.getD b 0] (basisB ((P.wBasis Ew).getD b (0, 0)).1
      ((P.wBasis Ew).getD b (0, 0)).2)) acc) []

/-- A candidate witness for the component `j` with multiplier `M`. -/
def findWitM (Ew M : ℕ) (j : Fin (dim F)) : Option (LogWit F) :=
  let m := M * P.denL j
  let Q := P.qWit m j
  let rows := (P.finBranches.flatMap fun b ↦ P.wRowsFin Ew m j Q b) ++
    P.inf.ys.flatMap fun wt ↦ P.wRowsInf Ew m j Q wt
  match homSolve rows (P.wBasis Ew).length with
  | none => none
  | some cs =>
    let w : LogWit F := ⟨m, P.combW Ew cs, Q⟩
    if P.witOK w j then some w else none

/-- The first multiplier `M ≤ B` with a checked witness (the trivial witness if none). -/
def findWit (B Ew : ℕ) (j : Fin (dim F)) : LogWit F :=
  (List.range B).foldr (fun M acc ↦ match P.findWitM Ew (M + 1) j with
    | some w => w
    | none => acc) ⟨1, [[1]], [1]⟩

/-- Witnesses for all components. -/
def findWits (B Ew : ℕ) : List (LogWit F) :=
  (List.finRange (dim F)).map fun j ↦ P.findWit B Ew j

/-- **The automatic decision** (witnesses searched up to multiplier `B`, `x`-degree `Ew`). -/
def decideAuto (B Ew : ℕ) : Option Bool := P.decideLog (P.findWits B Ew)

end CurveProb

end Search

section Spec

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

open Differential IntermediateField in
/-- **Correctness of the automatic decision.** -/
theorem decideAuto_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    [EllQuad.QCoords F] (P : CurveProb F) (ι : F →+* Kc)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ι)) (B Ew : ℕ) (b : Bool)
    (h : P.decideAuto B Ew = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true :=
  decideLog_spec hC S hx hgen P ι hSF _ b h

end Spec

end Curves
