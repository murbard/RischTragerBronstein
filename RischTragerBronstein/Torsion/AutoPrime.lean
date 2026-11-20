import RischTragerBronstein.Torsion.BaseChange
import RischTragerBronstein.Computable.NullSpace

/-!
# Computing the certificates at a prime

The data of `PrimeCert`, `PlaceCert.PrimeData` and the failed test of `TorsWitP` are **computed**
here instead of being supplied: reductions of the integral-basis certificates with left inverses
modulo `p`, a base point, the non-speciality coefficients, a specialization certifying
irreducibility (`noSmallFactor`), the multiplier `m_p` (smallest `m` with a kernel vector of the
test modulo `p`) and the left inverse of the test over the coefficient field. Everything goes
through the checks of `torsOKP`, so `decideLogTPA` is sound by `decideLogTP_spec`
(`decideLogTPA_spec`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section LinAlg

variable {F : Type*} [Field F] [DecidableEq F]

/-- A left inverse of the `R × n` matrix `M` (rows as lists), if its columns are independent:
row `c` solves `∑ᵣ L_{c r} Mᵣ = e_c`. -/
def leftInvL (rows : List (List F)) (n : ℕ) : Option (List (List F)) :=
  (List.range n).mapM fun c ↦ linSolve rows (unitL c)

/-- The first non-zero relation among the columns `cols` (each a list of entries). -/
def kernelL (cols : List (List F)) : Option (List F) := (nullBasis cols).head?

/-- A relation among the columns `cols` with a non-zero coefficient (`placeWit_spec` needs the
non-vanishing, `placeWit_isSome` shows one is found whenever the test passes). -/
def kernelNZ (cols : List (List F)) : Option (List F) :=
  (nullBasis cols).find? fun w ↦ (List.range cols.length).any fun t ↦ decide (w.getD t 0 ≠ 0)

end LinAlg

section Prime

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- The elements of `ZMod p`. -/
def zElems (p : ℕ) : List (ZMod p) := (List.range p).map fun i : ℕ ↦ (i : ZMod p)

/-- The reduced integral-basis certificate at a point, with a left inverse modulo `p`. -/
def redIBPoint (n : ℕ) (Bp : List (BPoly (ZMod p))) (Dp : CPoly (ZMod p))
    (q : K × BranchCert K × List (List K)) :
    Option (ZMod p × BranchCert (ZMod p) × List (List (ZMod p))) :=
  let c : BranchCert (ZMod p) := ⟨q.2.1.N, q.2.1.ys.map (·.map R.red), q.2.1.prec⟩
  let a := R.red q.1
  (leftInvL ((List.range (n * c.N)).map fun r ↦ (List.range n).map fun j ↦
      matEntry Bp Dp a c r j) n).map fun L ↦ (a, c, L)

/-- The reduced certificate above infinity, with a left inverse modulo `p`. -/
def redIBInf (n k : ℕ) (Bp : List (BPoly (ZMod p))) (Dp : CPoly (ZMod p)) (δL : List ℕ)
    (c : BranchCert K) : Option (BranchCert (ZMod p) × List (List (ZMod p))) :=
  let c' : BranchCert (ZMod p) := ⟨c.N, c.ys.map (·.map R.red), c.prec⟩
  (leftInvL ((List.range (n * c'.N)).map fun r ↦ (List.range n).map fun j ↦
      matInf Bp Dp k δL c' r j) n).map fun L ↦ (c', L)

/-- The roots of `F(x, Y)` modulo `p`. -/
def rootsAt (Fp : BPoly (ZMod p)) (x : ZMod p) : List (ZMod p) :=
  (zElems p).filter fun y ↦ evalB Fp x y = 0

/-- Candidate base points: `n` distinct simple roots, `D(x) ≠ 0`, away from `bad`. -/
def basePoints (n : ℕ) (Fp : BPoly (ZMod p)) (Dp : CPoly (ZMod p)) (bad : List (ZMod p)) :
    List (ZMod p × List (ZMod p)) :=
  ((zElems p).filter fun x ↦ !bad.contains x && decide (Kron.evalC Dp x ≠ 0) &&
      decide ((rootsAt Fp x).length = n) &&
      (rootsAt Fp x).all fun y ↦ decide (evalB (derivYB Fp) x y ≠ 0)).map
    fun x ↦ (x, rootsAt Fp x)

/-- The non-speciality coefficients for the base points `xs` (row `i0`). -/
def lamRow (n g : ℕ) (δL : List ℕ) (Bp : List (BPoly (ZMod p))) (xs : List (ZMod p))
    (ys : List (List (ZMod p))) (i0 : ℕ) : Option (List (ZMod p)) :=
  let eqs := (List.range n).flatMap fun j ↦ ((List.range (g + 1)).filter fun d ↦
    decide (d + δL.getD j 0 ≤ g)).map fun d ↦ (j, d)
  let idx := (List.range g).flatMap fun i ↦ ((List.range n).filter (· ≠ 0)).map fun k ↦ (i, k)
  (linSolve (idx.map fun ik ↦ eqs.map fun jd ↦ nsRow Bp xs ys ik.1 ik.2 jd.1 jd.2)
      (eqs.map fun jd ↦ nsRow Bp xs ys i0 0 jd.1 jd.2)).map fun a ↦
    (List.range (g * n)).map fun r ↦
      match idx.findIdx? (fun ik ↦ ik.1 * n + ik.2 = r) with
      | some t => a.getD t 0
      | none => 0

/-- **The certificate at a prime** for the curve data `T` (with the fibres of `Pc` excluded). -/
def autoPrimeCert (T : GlobalCert K) (bad : List K) : Option (PrimeCert p) := do
  let Fp := redBL R T.Fc
  let Bp := T.I.Bc.map (redBL R)
  let Dp := T.I.Dc.map R.red
  let n := T.n
  let g := (∑ j ∈ Finset.range n, T.I.δL.getD j 0) + 1 - n
  let pts ← T.I.pts.mapM (redIBPoint R n Bp Dp)
  let inf ← redIBInf R n T.k Bp Dp T.I.δL T.I.infc
  let cands := basePoints n Fp Dp ((bad ++ T.I.pts.map Prod.fst).map R.red)
  let base := cands.take g
  let xs := base.map Prod.fst
  let ys := base.map Prod.snd
  let lam ← (List.range g).mapM (lamRow n g T.I.δL Bp xs ys)
  let Ls ← (List.range g).mapM fun i ↦
    leftInvL ((List.range n).map fun kk ↦ (List.range n).map fun j ↦ detMat Bp xs ys i kk j) n
  let aI := (zElems p).find? fun a ↦ noSmallFactor (zElems p) (Fp.map fun c ↦ Kron.evalC c a) n
  -- without an irreducible specialization: the subset certificate at the first base point
  let irrP := if aI.isSome then 0 else
    (((List.range 3).map fun e ↦ (T.kD + 2) * 2 ^ e).find? fun pr ↦
      irrAt Fp n T.kD (xs.getD 0 0) (ys.getD 0 []) pr).getD 0
  pure ⟨pts, inf.1, inf.2, xs, ys, lam, Ls, [], 1, [[1]], aI, irrP⟩

/-- The kernel vector of the test at `m Γ` modulo `p`, as `Gw`. -/
def placeWit (n : ℕ) (δL : List ℕ) (Bp : List (BPoly (ZMod p))) (Dp : CPoly (ZMod p))
    (Pc : PlaceCert (ZMod p)) (m : ℕ) : Option (List (List (ZMod p))) :=
  let M := m * Pc.cΓ
  let cL := Pc.fcerts n
  let bL := Pc.bL n m
  let cols := (List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
    decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d)
  let rows := (List.range Pc.fib.length).flatMap fun j ↦ (List.range n).flatMap fun k ↦
    (List.range (rowsN Dp Pc.αs cL bL j k)).map fun t ↦ (j, k, t)
  -- only with enough precision (otherwise the kernel may be spurious)
  if !testSideN n Dp Pc.αs cL bL then none else
  (kernelNZ (cols.map fun id ↦ rows.map fun jkt ↦
      testEntryN Bp Dp Pc.αs cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2)).map fun w ↦
    (List.range n).map fun i ↦ (List.range (M + 1)).map fun d ↦
      match cols.findIdx? (· = (i, d)) with
      | some t => w.getD t 0
      | none => 0

/-- **The multiplier `m_p` and its witness**: the first `m ≤ B` with a kernel vector. -/
def autoPlaceData (T : GlobalCert K) (Pc : PlaceCert K) (B : ℕ) :
    Option (PlaceCert.PrimeData p) :=
  ((List.range B).map (· + 1)).firstM fun m ↦
    (placeWit T.n T.I.δL (T.I.Bc.map (redBL R)) (T.I.Dc.map R.red) (Pc.map R.red) m).map
      fun G ↦ (⟨m, G⟩ : PlaceCert.PrimeData p)

end Prime

section Global

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The failed test over the coefficient field**: a left inverse of the test at `M Γ` (rows
`(j, k, t)` at position `(j n + k) P + t`, `P` the largest multiplicity). -/
def autoLm (n M m : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (Pc : PlaceCert F) :
    Option (ℕ × List (List F)) :=
  let cL := Pc.fcerts n
  let bL := Pc.bL n m
  let Pb := ((List.range Pc.fib.length).flatMap fun j ↦ (List.range n).map fun k ↦
    rowsN Dc Pc.αs cL bL j k).foldr max 0
  let cols := (List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
    decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d)
  let rows := (List.range Pc.fib.length).flatMap fun j ↦ (List.range n).flatMap fun k ↦
    (List.range (rowsN Dc Pc.αs cL bL j k)).map fun t ↦ (j, k, t)
  (leftInvL (rows.map fun jkt ↦ cols.map fun id ↦
      testEntryN Bc Dc Pc.αs cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2) cols.length).map fun L ↦
    (Pb, (List.range (n * (M + 1))).map fun r ↦
      match cols.findIdx? (fun id ↦ id.1 * (M + 1) + id.2 = r) with
      | some c => (List.range (Pc.fib.length * n * Pb)).map fun pos ↦
          match rows.findIdx? (fun jkt ↦ (jkt.1 * n + jkt.2.1) * Pb + jkt.2.2 = pos) with
          | some t => (L.getD c []).getD t 0
          | none => 0
      | none => [])

end Global

section Auto

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- The witness from the global data at the primes `p`, `q` (search bound `B` for `m`). -/
def autoWitAt (redAt : (p : ℕ) → Option (RedFns p F)) (T : GlobalCert F) (Pc : PlaceCert F)
    (eL : List ℤ) (s : ℕ) (j₀ : Fin (EllQuad.QCoords.dim F)) (B p q : ℕ) :
    Option (TorsWitP F) :=
  if hp : p.Prime then if hq : q.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    match redAt p, redAt q with
    | some Rp, some Rq =>
      (autoPrimeCert Rp T (Pc.fib.map Prod.fst)).bind fun Pp ↦
      (autoPrimeCert Rq T (Pc.fib.map Prod.fst)).bind fun Pq ↦
      (autoPlaceData Rp T Pc B).bind fun Qp ↦
      (autoPlaceData Rq T Pc B).bind fun Qq ↦
      (autoLm T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) (pairMult p q Qp.mp Qq.mp) T.I.δL T.I.Bc
        T.I.Dc Pc).map fun L ↦
      (⟨T, Pc, eL, s, j₀, p, q, Pp, Pq, Qp, Qq, L.1, L.2⟩ : TorsWitP F)
    | _, _ => none
  else none else none

/-- **The decision with computed prime data**: the witnesses at places are computed from the
global data `gs` at the pairs of primes `pqs`. -/
def decideLogTPA (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F) (ws : List (LogWit F))
    (tws : List (TorsWit F))
    (gs : List (GlobalCert F × PlaceCert F × List ℤ × ℕ × Fin (EllQuad.QCoords.dim F)))
    (pqs : List (ℕ × ℕ)) (B : ℕ) : Option Bool :=
  decideLogTP redAt P ws tws (gs.flatMap fun g ↦ pqs.filterMap fun pq ↦
    autoWitAt redAt g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 B pq.1 pq.2)

end Auto

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

open IntermediateField Differential in
/-- **Soundness of the decision with computed prime data.** -/
theorem decideLogTPA_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (ws : List (LogWit F)) (tws : List (TorsWit F))
    (gs : List (GlobalCert F × PlaceCert F × List ℤ × ℕ × Fin (EllQuad.QCoords.dim F)))
    (pqs : List (ℕ × ℕ)) (B : ℕ) (b : Bool) (h : decideLogTPA redAt P ws tws gs pqs B = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true :=
  decideLogTP_spec hC S hx hgen redAt hred P ι hSF ws tws _ b h

end Main

end Curves
