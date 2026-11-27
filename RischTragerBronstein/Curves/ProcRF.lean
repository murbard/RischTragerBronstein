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

/-- `aᵏ` truncated at `prec`. -/
def rfPowT (a : CPoly F) (prec : ℕ) : ℕ → CPoly F
  | 0 => [1]
  | k + 1 => (mul a (rfPowT a prec k)).take prec

lemma rfX_pow_dvd_take (l : CPoly F) (n : ℕ) :
    (Polynomial.X : Polynomial F) ^ n ∣ toPoly (l.take n) - toPoly l := by
  by_cases hn : n ≤ l.length
  · conv_lhs => rw [show n = (l.take n).length by simp [hn]]
    conv_rhs => rw [← List.take_append_drop n l, toPoly_append]
    rw [List.take_append_drop]
    exact ⟨-toPoly (l.drop n), by ring⟩
  · rw [List.take_of_length_le (by omega), sub_self]; exact dvd_zero _

lemma rfPowT_spec (a : CPoly F) (prec : ℕ) : ∀ k : ℕ,
    (Polynomial.X : Polynomial F) ^ prec ∣ toPoly (rfPowT a prec k) - toPoly a ^ k
  | 0 => by simp [rfPowT, toPoly_cons]
  | k + 1 => by
    obtain ⟨u, hu⟩ := rfPowT_spec a prec k
    obtain ⟨v, hv⟩ := rfX_pow_dvd_take (mul a (rfPowT a prec k)) prec
    rw [toPoly_mul] at hv
    exact ⟨v + toPoly a * u, by rw [rfPowT, pow_succ]; linear_combination hv + toPoly a * hu⟩

lemma rfGetD_eq_of_dvd {p q : CPoly F} {n m : ℕ}
    (h : (Polynomial.X : Polynomial F) ^ n ∣ toPoly p - toPoly q) (hm : m < n) :
    p.getD m 0 = q.getD m 0 := by
  have := (Polynomial.X_pow_dvd_iff.mp h) m hm
  rw [Polynomial.coeff_sub, coeff_toPoly, coeff_toPoly] at this
  exact sub_eq_zero.mp this

lemma rfDivTrunc_congr (W W' U : CPoly F) : ∀ n : ℕ, (∀ m < n, W.getD m 0 = W'.getD m 0) →
    divTrunc W U n = divTrunc W' U n
  | 0, _ => rfl
  | n + 1, h => by
    rw [divTrunc, divTrunc, rfDivTrunc_congr W W' U n fun m hm ↦ h m (by omega), h n (by omega)]

lemma rfToPoly_bivEval_basisB (i e : ℕ) (s Y : CPoly F) :
    toPoly (bivEval (basisB i e) s Y) = toPoly Y ^ i * toPoly s ^ e := by
  induction i with
  | zero =>
    simp [basisB, bivEval, toPoly_compC, toPoly_xPowC]
  | succ i ih =>
    have : basisB (i + 1) e = ([] : CPoly F) :: basisB i e := by
      simp [basisB, List.replicate_succ]
    rw [this]
    show toPoly (add (compC [] s) (mul Y (bivEval (basisB i e) s Y))) = _
    rw [toPoly_add, toPoly_mul, ih, toPoly_compC]
    simp [pow_succ]; ring

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

/-- `rowsFin` with the expansions computed once, from truncated powers of the branch series: the
compiled code (`rowsFin_eq_rowsFinF`). -/
def rowsFinF (a : F) (c : BranchCert F) (yt : CPoly F) : List (List F × F) :=
  let mu := P.muFin a c.N
  let muf := P.mufFin a c.N
  let Vf := P.VfFin a c yt
  let U := P.UFin a c.N
  let sh := shiftC a c.N
  let yps := (List.range P.n).map (rfPowT yt c.prec)
  let sps := (List.range (P.E + 1)).map (rfPowT sh c.prec)
  let Vbs := P.basisIdx.map fun ie ↦
    divTrunc ((mul (yps.getD ie.1 []) (sps.getD ie.2 [])).take c.prec) U c.prec
  let jmin := P.jminFin a c
  (List.range (-1 - jmin).toNat).map fun t ↦
    (Vbs.map fun V ↦ ((jmin + t + 1 : ℤ) : F) * gi V (jmin + t + 1 + mu),
      (c.N : F) * gi Vf (jmin + t - c.N + 1 + muf))

@[csimp] theorem rowsFin_eq_rowsFinF : @rowsFin = @rowsFinF := by
  funext F _ _ P a c yt
  simp only [rowsFin, rowsFinF, rowFinAt, VbFin, List.map_map, Function.comp_def]
  refine List.map_congr_left fun t _ ↦ ?_
  congr 1
  refine List.map_congr_left fun ie hie ↦ ?_
  obtain ⟨i, hi, hie'⟩ := List.mem_flatMap.mp hie
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hie'
  rw [List.mem_range] at hi he
  congr 2
  refine rfDivTrunc_congr _ _ _ _ fun m hm ↦ rfGetD_eq_of_dvd ?_ hm
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map, List.getElem?_range hi, List.getElem?_range he]
  simp only [Option.map_some, Option.getD_some]
  rw [rfToPoly_bivEval_basisB]
  have h1 := rfX_pow_dvd_take (mul (rfPowT yt c.prec i) (rfPowT (shiftC a c.N) c.prec e)) c.prec
  have h2 := rfPowT_spec yt c.prec i
  have h3 := rfPowT_spec (shiftC a c.N) c.prec e
  rw [toPoly_mul] at h1
  obtain ⟨u1, hu1⟩ := h1
  obtain ⟨u2, hu2⟩ := h2
  obtain ⟨u3, hu3⟩ := h3
  refine ⟨-u1 - u2 * toPoly (rfPowT (shiftC a c.N) c.prec e) - toPoly yt ^ i * u3, ?_⟩
  linear_combination -hu1 - toPoly (rfPowT (shiftC a c.N) c.prec e) * hu2 - toPoly yt ^ i * hu3

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

/-- `rowsInf` with the expansions computed once: the compiled code (`rowsInf_eq_rowsInfF`). -/
def rowsInfF (wt : CPoly F) : List (List F × F) :=
  let sb := P.sbInf
  let sf := P.sfInf
  let Vf := P.VfInf wt
  let sh := shiftC (0 : F) P.inf.N
  let den := compC (reflectC (degT P.R0) (trim P.R0)) sh
  let DWb := P.DWb
  let Vbs := P.basisIdx.map fun ie ↦
    divTrunc (bivEval (invB (basisB ie.1 ie.2) P.k DWb) sh wt) den P.inf.prec
  let jmin := P.jminInf
  (List.range (-1 - jmin).toNat).map fun t ↦
    (Vbs.map fun V ↦ ((jmin + t + 1 : ℤ) : F) * gi V (jmin + t + 1 - sb),
      -(P.inf.N : F) * gi Vf (jmin + t + P.inf.N + 1 - sf))

@[csimp] theorem rowsInf_eq_rowsInfF : @rowsInf = @rowsInfF := by
  funext F _ _ P wt
  simp only [rowsInf, rowsInfF, rowInfAt, VbInf, List.map_map, Function.comp_def]

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

/-- `cols` with the rows computed once: the compiled code (`cols_eq_colsF`). -/
def colsF : List (CPoly F) :=
  let rows := P.allRows
  (List.range P.basisIdx.length).map fun b ↦ rows.map fun r ↦ r.1.getD b 0

@[csimp] theorem cols_eq_colsF : @cols = @colsF := rfl

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
