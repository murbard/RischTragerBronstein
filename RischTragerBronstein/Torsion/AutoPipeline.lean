import RischTragerBronstein.Torsion.AutoPlace

/-!
# The automatic pipeline for integrands on curves

`autoCurveProb`: the certificates of a `CurveProb` (branches at the roots of `disc · D` and above
infinity, with precisions derived from the orders that `CurveProb.valid` requires), computed by
Newton polygons (`puiseuxAt`). `autoGlobal`: the global certificate from the computed integral
basis (`autoIntBasis`). `autoTorsWits`: for each coordinate `j₀` with non-zero residues, the place
certificate (`autoPlaceCert`) and the prime data at the given pairs of primes (`autoWitAt`).
`decideAutoP` feeds them to `decideLogTP`; **`decideAutoP_spec`**: every answer is correct (the
certificates are all checked, `decideLogTP_spec`).
-/

namespace Curves

open CPoly Sup EllQuad.QCoords

section Pipe

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- The branches above `a` as a certificate of precision `prec` (length `L`). -/
def certAtAuto (rf : RootFinder F) (Fc : BPoly F) (a : F) (L prec : ℕ) : Option (BranchCert F) :=
  match puiseuxAt rf Fc a L (4 * (Fc.length + 1) * L) with
  | .ok bs => some (branchCert bs prec)
  | .error _ => none

/-- The distinct roots of `P`. -/
def rootsAuto (rf : RootFinder F) (P : CPoly F) : Option (List F) :=
  let P := trim P
  if P.length ≤ 1 then some [] else rf P

/-- **The certificates of the integrand** `A/D` on `Fc` (weight `k`), extra precision `ex`. -/
def autoCurveProb (rf : RootFinder F) (Fc : BPoly F) (n k : ℕ) (A : BPoly F) (D : CPoly F)
    (ex : ℕ) : Option (CurveProb F) := do
  let P0 : CurveProb F := ⟨Fc, n, k, A, D, [], ⟨1, [], 0⟩⟩
  let sp ← rootsAuto rf P0.R0
  let pts ← sp.mapM fun a ↦ do
    let c0 ← certAtAuto rf Fc a 4 1
    let N := c0.N
    let prec := P0.muFin a N + P0.mufFin a N + N + ex
    let c ← certAtAuto rf Fc a (prec + 2) prec
    pure (a, c)
  let ci0 ← certAtAuto rf (invB Fc k (k * n)) 0 4 1
  let P1 : CurveProb F := ⟨Fc, n, k, A, D, pts, ci0⟩
  let precI := (max (-P1.sbInf) ((ci0.N : ℤ) - P1.sfInf + 1)).toNat + ex
  let ci ← certAtAuto rf (invB Fc k (k * n)) 0 (precI + 2) precI
  pure ⟨Fc, n, k, A, D, pts, ci⟩

/-- The largest `x`-degree of the coefficients of `F`. -/
def kDOf (Fc : BPoly F) : ℕ := Fc.foldr (fun c m ↦ max m (c.length - 1)) 0

/-- **The global certificate** (integral basis with weight `kI` above infinity). -/
def autoGlobal (rf : RootFinder F) (Fc : BPoly F) (n kI : ℕ) (ex fuel : ℕ) :
    Option (GlobalCert F) := do
  let kD := kDOf Fc
  let sp ← rootsAuto rf (discRC Fc n kD)
  let pts ← sp.mapM fun a ↦ do
    let c ← certAtAuto rf Fc a (2 * n * n + ex + 2) (2 * n * n + ex)
    pure (a, c)
  let ci ← certAtAuto rf (invB Fc kI (kI * n)) 0 (2 * n * n + ex + 2) (2 * n * n + ex)
  let I ← autoIntBasis Fc n kI pts ci fuel
  pure ⟨Fc, n, kI, kD, I, 0, [], [], [], [], 0⟩

/-- The branches above `a` (for the place certificate). -/
def branchesAuto (rf : RootFinder F) (Fc : BPoly F) (a : F) (L : ℕ) : Option (List (PBranch F)) :=
  match puiseuxAt rf Fc a L (4 * (Fc.length + 1) * L) with
  | .ok bs => some bs
  | .error _ => none

/-- **The non-torsion witnesses** for the coordinates with non-zero residues. -/
def autoTorsWits (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (T : GlobalCert F) (L tp B : ℕ) (pqs : List (ℕ × ℕ)) : List (TorsWitP F) :=
  (List.finRange (dim F)).flatMap fun j₀ ↦
    -- the fibres with a non-zero `j₀`-residue
    let fibs := (P.pts.filter fun ac ↦ ac.2.ys.any fun yt ↦ coord j₀ (P.resFin ac.1 ac.2 yt) ≠ 0).map
      Prod.fst
    if fibs.isEmpty then [] else
    match fibs.mapM (fun a ↦ (branchesAuto rf P.Fc a L).map fun bs ↦ (a, bs)) with
    | none => []
    | some fb =>
      match autoPlaceCert rf P j₀ L tp fb with
      | none => []
      | some (Pc, eL, s) =>
        pqs.filterMap fun pq ↦ autoWitAt redAt T Pc eL s j₀ B pq.1 pq.2

/-- **The automatic decision** (log witnesses `ws`, non-torsion witnesses computed). -/
def decideAutoP (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (T : GlobalCert F) (ws : List (LogWit F)) (L tp B : ℕ) (pqs : List (ℕ × ℕ)) : Option Bool :=
  decideLogTP redAt P ws [] (autoTorsWits rf redAt P T L tp B pqs)

end Pipe

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

open IntermediateField Differential Polynomial in
/-- **Soundness of the automatic decision.** -/
theorem decideAutoP_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (T : GlobalCert F) (ws : List (LogWit F)) (L tp B : ℕ) (pqs : List (ℕ × ℕ)) (b : Bool)
    (h : decideAutoP rf redAt P T ws L tp B pqs = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true :=
  decideLogTP_spec hC S hx hgen redAt hred P ι hSF ws [] _ b h

end Main

end Curves
