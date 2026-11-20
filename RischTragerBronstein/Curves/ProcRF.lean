import RischTragerBronstein.Curves.Cover
import RischTragerBronstein.Computable.LinSolve

/-!
# The decision procedure for general curves: exact part, residues, residue-free case

Input (`CurveProb`): a monic `F(x, Y)` of degree `n` with coefficient degrees `≤ k`, the integrand
`A(x, y)/D(x)`, the special points (all roots of `D · Res(F, F_Y)`) with branch certificates, and a
branch certificate above infinity.

* `ansatz` space: `W(x, y)/(discR·D)`, `deg_x W ≤ E` (`ansatz` theorem);
* linear conditions: `f − v′` has at most simple poles along the certified branches;
* residues of `f dx` along the certified branches;
* zero test for `f − v′`.

`decideRF`: `some false` if no exact part exists; if all residues vanish, `some (f − v′ = 0)`;
otherwise `none` (the logarithmic part is handled later).
-/

open Polynomial

namespace Curves

open CPoly Sup Differential

/-- A general-curve integration problem. -/
structure CurveProb (F : Type*) where
  Fc : BPoly F
  n : ℕ
  k : ℕ
  A : BPoly F
  D : CPoly F
  pts : List (F × BranchCert F)
  inf : BranchCert F

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- Coefficient access with an integer index. -/
def gi (V : CPoly F) (j : ℤ) : F := if j < 0 then 0 else V.getD j.toNat 0

/-- `xᵉ Yⁱ`. -/
def basisB (i e : ℕ) : BPoly F := List.replicate i [] ++ [xPowC e]

namespace CurveProb

variable (P : CurveProb F)

/-- The ansatz denominator `discR · D`. -/
def R0 : CPoly F := trim (mul (discRC P.Fc P.n P.k) P.D)

/-- A bound for `deg Aᵢ + k i`. -/
def DA : ℕ := (List.range P.A.length).foldr (fun i m ↦ max m (degT (P.A.getD i []) + P.k * i)) 0

/-- The pole bound at infinity for the exact part. -/
def Binf : ℕ := P.DA + 1 - degT P.D

/-- `∑ deg Fᵢ`. -/
def degBC : ℕ := (List.range (P.n + 1)).foldr (fun i m ↦ m + degT (P.Fc.getD i [])) 0

/-- The ansatz degree bound. -/
def E : ℕ := degT P.D + P.Binf + ((P.n - 1) * (P.n - 1) + (P.n - 1)) * P.degBC

/-- The ansatz basis indices `(i, e)`. -/
def basisIdx : List (ℕ × ℕ) :=
  (List.range P.n).flatMap fun i ↦ (List.range (P.E + 1)).map fun e ↦ (i, e)

/-- `R0(a + Tᴺ)`, its order `μ` and unit part. -/
def QFin (a : F) (N : ℕ) : CPoly F := compC P.R0 (shiftC a N)
def muFin (a : F) (N : ℕ) : ℕ := ordC (P.QFin a N)
def UFin (a : F) (N : ℕ) : CPoly F := (P.QFin a N).drop (P.muFin a N)

/-- `D(a + Tᴺ)`, its order `μ_f` and unit part. -/
def QfFin (a : F) (N : ℕ) : CPoly F := compC P.D (shiftC a N)
def mufFin (a : F) (N : ℕ) : ℕ := ordC (P.QfFin a N)
def UfFin (a : F) (N : ℕ) : CPoly F := (P.QfFin a N).drop (P.mufFin a N)

/-- The truncated expansion of `f` (times `T^{μ_f}`). -/
def VfFin (a : F) (c : BranchCert F) (yt : CPoly F) : CPoly F :=
  divTrunc (bivEval P.A (shiftC a c.N) yt) (P.UfFin a c.N) c.prec

/-- The truncated expansion of the basis element `b` (times `T^μ`). -/
def VbFin (a : F) (c : BranchCert F) (yt : CPoly F) (ie : ℕ × ℕ) : CPoly F :=
  divTrunc (bivEval (basisB ie.1 ie.2) (shiftC a c.N) yt) (P.UFin a c.N) c.prec

/-- The smallest relevant index. -/
def jminFin (a : F) (c : BranchCert F) : ℤ :=
  min (-(P.muFin a c.N : ℤ) - 1) ((c.N : ℤ) - 1 - P.mufFin a c.N)

/-- The row for the coefficient of `T^j`. -/
def rowFinAt (a : F) (c : BranchCert F) (yt : CPoly F) (j : ℤ) : List F × F :=
  (P.basisIdx.map fun ie ↦ ((j + 1 : ℤ) : F) * gi (P.VbFin a c yt ie) (j + 1 + P.muFin a c.N),
    (c.N : F) * gi (P.VfFin a c yt) (j - c.N + 1 + P.mufFin a c.N))

/-- Rows at a finite certified branch: `j ∈ [jmin, −2]`. -/
def rowsFin (a : F) (c : BranchCert F) (yt : CPoly F) : List (List F × F) :=
  (List.range (-1 - P.jminFin a c).toNat).map fun t ↦ P.rowFinAt a c yt (P.jminFin a c + t)

/-- The residue of `f dx` along a finite certified branch. -/
def resFin (a : F) (c : BranchCert F) (yt : CPoly F) : F :=
  (c.N : F) * gi (P.VfFin a c yt) ((P.mufFin a c.N : ℤ) - c.N)

/-- Degree bound used for the basis at infinity. -/
def DWb : ℕ := P.E + P.k * (P.n - 1)

/-- The exponents at infinity. -/
def sbInf : ℤ := -((P.inf.N * P.DWb : ℕ) : ℤ) + ((P.inf.N * degT P.R0 : ℕ) : ℤ)
def sfInf : ℤ := -((P.inf.N * P.DA : ℕ) : ℤ) + ((P.inf.N * degT P.D : ℕ) : ℤ)

def VfInf (wt : CPoly F) : CPoly F :=
  divTrunc (bivEval (invB P.A P.k P.DA) (shiftC 0 P.inf.N) wt)
    (compC (reflectC (degT P.D) (trim P.D)) (shiftC 0 P.inf.N)) P.inf.prec

def VbInf (wt : CPoly F) (ie : ℕ × ℕ) : CPoly F :=
  divTrunc (bivEval (invB (basisB ie.1 ie.2) P.k P.DWb) (shiftC 0 P.inf.N) wt)
    (compC (reflectC (degT P.R0) (trim P.R0)) (shiftC 0 P.inf.N)) P.inf.prec

def jminInf : ℤ := min (P.sbInf - 1) (P.sfInf - P.inf.N - 1)

def rowInfAt (wt : CPoly F) (j : ℤ) : List F × F :=
  (P.basisIdx.map fun ie ↦ ((j + 1 : ℤ) : F) * gi (P.VbInf wt ie) (j + 1 - P.sbInf),
    -(P.inf.N : F) * gi (P.VfInf wt) (j + P.inf.N + 1 - P.sfInf))

/-- Rows at a certified branch above infinity. -/
def rowsInf (wt : CPoly F) : List (List F × F) :=
  (List.range (-1 - P.jminInf).toNat).map fun t ↦ P.rowInfAt wt (P.jminInf + t)

/-- The residue of `f dx` along a certified branch above infinity. -/
def resInf (wt : CPoly F) : F := -(P.inf.N : F) * gi (P.VfInf wt) ((P.inf.N : ℤ) - P.sfInf)

/-- All rows. -/
def allRows : List (List F × F) :=
  (P.pts.flatMap fun ac ↦ ac.2.ys.flatMap fun yt ↦ P.rowsFin ac.1 ac.2 yt) ++
    P.inf.ys.flatMap P.rowsInf

/-- All residues. -/
def allRes : List F :=
  (P.pts.flatMap fun ac ↦ ac.2.ys.map fun yt ↦ P.resFin ac.1 ac.2 yt) ++ P.inf.ys.map P.resInf

/-- The columns of the linear system (one per basis element). -/
def cols : List (CPoly F) :=
  (List.range P.basisIdx.length).map fun b ↦ P.allRows.map fun r ↦ r.1.getD b 0

/-- The right-hand side. -/
def rhs : CPoly F := P.allRows.map Prod.snd

/-- The exact part `W` from a solution. -/
def Wsol (cs : List F) : BPoly F :=
  (List.range P.basisIdx.length).foldr (fun b acc ↦
    addB (smulB [cs.getD b 0] (basisB (P.basisIdx.getD b (0, 0)).1 (P.basisIdx.getD b (0, 0)).2))
      acc) []

/-- `A·discR·R0·F_Y − (W_x R0 − W R0′) F_Y + W_Y R0 F_x` (`= (f − v′) R0² F_Y`). -/
def Pg (W : BPoly F) : BPoly F :=
  let FY := derivYB P.Fc
  let FX := dXB P.Fc
  let R := P.R0
  addB (addB (mulB (smulB (mul (discRC P.Fc P.n P.k) R) P.A) FY)
    (smulB [-1] (mulB (addB (smulB R (dXB W)) (smulB (smul (-1) (CPoly.deriv R)) W)) FY)))
    (mulB (smulB R (derivYB W)) FX)

/-- Validity checks. -/
def valid : Bool :=
  decide (0 < P.n) && decide (P.Fc.length = P.n + 1) && decide (P.Fc.getD P.n [] = [1]) &&
  decide ((invB P.Fc P.k (P.k * P.n)).length = P.n + 1) &&
  decide ((invB P.Fc P.k (P.k * P.n)).getD P.n [] = [1]) &&
  (List.range P.Fc.length).all (fun j ↦ decide ((P.Fc.getD j []).length + P.k * j ≤ P.k * P.n + 1)) &&
  (List.range P.Fc.length).all (fun j ↦ decide ((P.Fc.getD j []).length ≤ P.k + 1)) &&
  decide (0 < P.inf.N) &&
  P.pts.all (fun ac ↦ certCheck P.Fc P.n ac.1 ac.2) &&
  certCheck (invB P.Fc P.k (P.k * P.n)) P.n 0 P.inf &&
  !isZero P.D && coverCheck (mul P.D (discRC P.Fc P.n P.k)) (P.pts.map Prod.fst) &&
  -- precision and non-degeneracy of the local data
  P.pts.all (fun ac ↦ decide (P.muFin ac.1 ac.2.N < ac.2.prec) &&
    decide (P.mufFin ac.1 ac.2.N < ac.2.prec + ac.2.N) &&
    decide (P.muFin ac.1 ac.2.N < (P.QFin ac.1 ac.2.N).length) &&
    decide (P.mufFin ac.1 ac.2.N < (P.QfFin ac.1 ac.2.N).length)) &&
  decide (-P.sbInf ≤ P.inf.prec) && decide ((P.inf.N : ℤ) - P.sfInf < P.inf.prec) &&
  decide (0 < (trim P.R0).length) && decide (0 < (trim P.D).length) &&
  (List.range P.A.length).all (fun j ↦ decide ((P.A.getD j []).length + P.k * j ≤ P.DA + 1))

/-- **The residue-free decision.** -/
def decideRF : Option Bool :=
  if P.valid then
    match linSolve P.cols P.rhs with
    | none => some false
    | some cs =>
      if P.allRes.all (· = 0) then some (isZeroB (modF P.Fc P.n (P.Pg (P.Wsol cs))))
      else none
  else none

end CurveProb

end Defs

end Curves
