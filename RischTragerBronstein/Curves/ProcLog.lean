import RischTragerBronstein.Curves.NormC
import RischTragerBronstein.Algebraic.SupLogSem
import RischTragerBronstein.Algebraic.EllDecideK

/-!
# The logarithmic part on a general curve: witnesses and the decision

After the exact part `v` (`linSolve` on the rows), `g = f − v′` has at most simple poles, with
residues `r_β` along the certified branches (`allRes`, elements of `F`). With `ℚ`-coordinates
`coord_j` on `F` (basis `b_j`), a **log witness** for the component `j` is `(m_j, W_j, Q_j)` with
`u_j = W_j(x, y)/Q_j(x)`; `witCheck` verifies, along every certified branch,
`ord u_j = m_j · coord_j(r_β)` (orders read off truncated expansions), and that `u_j` has no zeros or
poles elsewhere (`coverCheck` of `Res_Y(F, W_j) · Q_j`). Then
`h = g − ∑_j (b_j/m_j) u_j′/u_j` has no residues at all, and `logNum` is the bivariate numerator of
`h · R0² F_Y ∏ W_j Q_j`.

`decideLog P ws`: `some false` if there is no exact part; if all residues vanish, the residue-free
zero test; otherwise, if the witnesses `ws` pass `witCheck`, the zero test for `h`; else `none`.
-/

open Polynomial EllQuad

namespace Curves

open CPoly Sup EllQuad.QCoords

/-- A logarithm witness `u = W(x, y)/Q(x)` with multiplier `m`. -/
structure LogWit (F : Type*) where
  m : ℕ
  W : BPoly F
  Q : CPoly F

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- The smallest `D` with `InvOK k D 0 W`. -/
def invDeg (W : BPoly F) (k : ℕ) : ℕ :=
  (List.range W.length).foldr (fun j m ↦ max m ((W.getD j []).length + k * j - 1)) 0

/-- The order of `W(x, y)` along a certified finite branch (if visible below the precision). -/
def ordWFin (W : BPoly F) (a : F) (c : BranchCert F) (yt : CPoly F) : Option ℕ :=
  let V := bivEval W (shiftC a c.N) yt
  if ordC V < c.prec ∧ ordC V < V.length then some (ordC V) else none

/-- The order of `Q(x)` along a finite branch with `x = a + Tᴺ`. -/
def ordQFin (Q : CPoly F) (a : F) (N : ℕ) : ℕ := ordC (compC Q (shiftC a N))

/-- The order of `W(x, y)` along a certified branch above infinity (`y = T^{−kN} w`). -/
def ordWInf (W : BPoly F) (k : ℕ) (c : BranchCert F) (wt : CPoly F) : Option ℤ :=
  let V := bivEval (invB W k (invDeg W k)) (shiftC 0 c.N) wt
  if ordC V < c.prec ∧ ordC V < V.length then
    some (-((c.N * invDeg W k : ℕ) : ℤ) + ordC V) else none

variable [CharZero F] [QCoords F]

namespace CurveProb

variable (P : CurveProb F)

/-- The witness for the component `j`. -/
def witAt (ws : List (LogWit F)) (j : Fin (dim F)) : LogWit F := ws.getD j ⟨1, [[1]], [1]⟩

/-- The divisor condition along a certified finite branch. -/
def witFinOK (w : LogWit F) (j : Fin (dim F)) (a : F) (c : BranchCert F) (yt : CPoly F) : Bool :=
  match ordWFin w.W a c yt with
  | none => false
  | some o => decide (((o : ℤ) - ordQFin w.Q a c.N : ℚ) = w.m * coord j (P.resFin a c yt))

/-- The divisor condition along a certified branch above infinity. -/
def witInfOK (w : LogWit F) (j : Fin (dim F)) (wt : CPoly F) : Bool :=
  match ordWInf w.W P.k P.inf wt with
  | none => false
  | some o => decide ((o + ((P.inf.N * degT w.Q : ℕ) : ℤ) : ℚ) = w.m * coord j (P.resInf wt))

/-- **The witness check** for the component `j`. -/
def witOK (w : LogWit F) (j : Fin (dim F)) : Bool :=
  decide (0 < w.m) && !isZero w.Q &&
  P.pts.all (fun ac ↦ ac.2.ys.all fun yt ↦ P.witFinOK w j ac.1 ac.2 yt) &&
  P.inf.ys.all (fun wt ↦ P.witInfOK w j wt) &&
  coverCheck (mul (normRC P.Fc w.W P.n P.k) w.Q) (P.pts.map Prod.fst)

/-- All witnesses. -/
def witCheck (ws : List (LogWit F)) : Bool :=
  (List.finRange (dim F)).all fun j ↦ P.witOK (witAt ws j) j

/-- `(W_x F_Y − W_Y F_x) Q − W Q′ F_Y` (`= (u′/u) · W Q F_Y` for `u = W/Q`). -/
def logNumW (w : LogWit F) : BPoly F :=
  addB (smulB w.Q (addB (mulB (dXB w.W) (derivYB P.Fc))
      (smulB [-1] (mulB (derivYB w.W) (dXB P.Fc)))))
    (smulB [-1] (mulB (smulB (CPoly.deriv w.Q) w.W) (derivYB P.Fc)))

/-- `W Q` as a bivariate polynomial. -/
def wqB (w : LogWit F) : BPoly F := smulB w.Q w.W

/-- The coefficient `b_j / m_j`. -/
def cLog (w : LogWit F) (j : Fin (dim F)) : F := bvec j / (w.m : F)

/-- **The numerator** of `(f − v′ − ∑ c_j u_j′/u_j) · R0² F_Y ∏ W_j Q_j`. -/
def logNum (cs : List F) (ws : List (LogWit F)) : BPoly F :=
  let js := List.finRange (dim F)
  let wq := js.map fun (j : Fin (dim F)) ↦ wqB (witAt ws j)
  addB (mulB (P.Pg (P.Wsol cs)) (prodB wq))
    (smulB [-1] (smulB (mul P.R0 P.R0) (sumB (js.map fun (j : Fin (dim F)) ↦
      smulB [cLog (witAt ws j) j]
        (mulB (P.logNumW (witAt ws j)) (prodB (((List.finRange (dim F)).filter
          (fun i ↦ decide (i ≠ j))).map fun i ↦ wqB (witAt ws i))))))))

/-- **The decision with logarithmic part** (relative to the witnesses `ws`). -/
def decideLog (ws : List (LogWit F)) : Option Bool :=
  if P.valid then
    match linSolve P.cols P.rhs with
    | none => some false
    | some cs =>
      if P.allRes.all (· = 0) then some (isZeroB (modF P.Fc P.n (P.Pg (P.Wsol cs))))
      else if P.witCheck ws then some (isZeroB (modF P.Fc P.n (P.logNum cs ws)))
      else none
  else none

end CurveProb

end Defs

end Curves
