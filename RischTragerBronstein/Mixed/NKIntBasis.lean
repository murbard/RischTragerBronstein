import RischTragerBronstein.Mixed.NKShear
import RischTragerBronstein.Torsion.AutoPipeline
import RischTragerBronstein.Computable.KronCert

/-!
# Integral bases for the exact part (untrusted search)

At a singular point of the curve, the derivation matrix of the power basis can have a pole of
order `> 1` whose leading matrix is singular (the case of Moser reduction); the shearing search
`exactTS` only divides basis elements by powers of a factor. An integral basis (Trager's
algorithm `autoIntBasis`, from Puiseux certificates at the rational singular points and above
infinity, normalized at infinity) gives a derivation matrix with simple poles at finite places
(`t D` preserves the integral closure). `exactTI` computes it for a curve over `ℚ`, inverts it by
Gauss–Jordan (both untrusted), and runs `exactT`, whose checks (`T T⁻¹ = T⁻¹ T = 1`) make every
answer correct (`exactTI_spec`); `nk_iffTI`, `nk_iffETI` are the decisions.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential

/-- `ℚ` with its trivial coordinates. -/
instance qCoordsIB : EllQuad.QCoords ℚ where
  dim := 1
  coord := fun _ ↦ LinearMap.id
  bvec := fun _ ↦ 1
  repr := fun z ↦ by simp

/-- Rational roots (an untrusted root finder over `ℚ`). -/
def ratRF : RootFinder ℚ := fun P ↦ some (ratRootsF P)

section IrrPts

open Kron

/-! ### Integral bases at irrational singular points

At an irreducible factor `p` of the discriminant with `p² ∣ disc`, the combinations
`∑ cⱼ(t) Bⱼ/(D p)` with rational `cⱼ` of degree `< deg p` that are integral along the branches at
one root `a` of `p` (over `ℚ[X]/(p)`, conditions split into rational coordinates) are integral at
all the conjugate roots; the leading coefficient is made `1` modulo `p` (Bezout), so the new
module contains the old one. -/

section Local
variable (p : CPoly ℚ) [Fact (Irreducible (toPoly p))]

/-- The ℚ-coordinates of an element of `ℚ[X]/(p)`. -/
def coordsN (z : NFC.NF p) : List ℚ := (List.range (degC p)).map fun i ↦ z.1.getD i 0

/-- **One local step at an irreducible factor `p`**: a combination `∑ cⱼ(t) Bⱼ` (`deg cⱼ < deg p`,
rational) integral after division by `D p` along the branches at a root `a` of `p`. -/
def stepP (n : ℕ) (Bs : List (BPoly ℚ)) (D : CPoly ℚ) (c : BranchCert (NFC.NF p)) :
    Option (List (BPoly ℚ) × CPoly ℚ) :=
  let a : NFC.NF p := NFC.mk p [0, 1]
  let dp := degC p
  let toF : BPoly ℚ → BPoly (NFC.NF p) := fun B ↦ B.map (·.map (algebraMap ℚ (NFC.NF p)))
  let DF : CPoly (NFC.NF p) := D.map (algebraMap ℚ (NFC.NF p))
  let μ := Curves.muD DF a c.N
  let R := c.N * (μ + 1)
  if c.prec < R then none else
  let unk := (List.range n).flatMap fun j ↦ (List.range dp).map fun l ↦ (j, l)
  let cols : List (CPoly ℚ) := unk.map fun jl ↦
    (List.range n).flatMap fun k ↦ (List.range R).flatMap fun r ↦
      coordsN p ((bivEval (toF (smulB (List.replicate jl.2 0 ++ [1]) (Bs.getD jl.1 [])))
        (shiftC a c.N) (c.ys.getD k [])).getD r 0)
  match (nullBasis cols).head? with
  | none => none
  | some w =>
    let cj : ℕ → CPoly ℚ := fun j ↦ (List.range dp).map fun l ↦ w.getD (j * dp + l) 0
    match ((List.range n).filter fun j ↦ (trim (cj j)).length ≠ 0).getLast? with
    | none => none
    | some jt =>
      let g := egcd (cj jt) p
      let e : CPoly ℚ := g.2.1.map (· / (trim g.1).getD 0 1)
      let comb := (List.range n).foldr (fun j acc ↦
        addB (smulB (divMod (mul e (cj j)) p).2 (Bs.getD j [])) acc) []
      some ((List.range n).map (fun j ↦ if j = jt then comb else smulB p (Bs.getD j [])), mul D p)

/-- The local loop at `p`. -/
def loopP (n : ℕ) (c : BranchCert (NFC.NF p)) : ℕ → List (BPoly ℚ) × CPoly ℚ →
    List (BPoly ℚ) × CPoly ℚ
  | 0, st => st
  | k + 1, st => match stepP p n st.1 st.2 c with
    | none => st
    | some st' => loopP n c k st'

/-- The branches at a root of `p` and the local loop. -/
def atP (Fq : BPoly ℚ) (n prec fuel : ℕ) (st : List (BPoly ℚ) × CPoly ℚ) :
    List (BPoly ℚ) × CPoly ℚ :=
  let FcF : BPoly (NFC.NF p) := Fq.map (·.map (algebraMap ℚ (NFC.NF p)))
  match certAtAuto (NFC.rfNFZ p) FcF (NFC.mk p [0, 1]) (prec + 2) prec with
  | none => st
  | some c => loopP p n c fuel st

end Local

/-- **A basis integral at all finite places**: local loops at the irreducible factors `p` with
`p² ∣ disc`. -/
def finIntBasis (Fq : BPoly ℚ) (n : ℕ) : List (BPoly ℚ) × CPoly ℚ :=
  let disc := discRC Fq n (kDOf Fq)
  let mon : CPoly ℚ → CPoly ℚ := fun p ↦ (trim p).map (· / (trim p).getLast?.getD 1)
  let ps := ((factorQ 20 disc).map mon).filter fun p ↦
    degC p ≥ 1 && (divMod disc (mul p p)).2.all (· = 0)
  let B0 : List (BPoly ℚ) := (List.range n).map fun j ↦ List.replicate j [] ++ [[1]]
  ps.dedup.foldl (fun st p ↦
    if h : Kron.irredQ p = true then
      haveI : Fact (Irreducible (toPoly p)) := ⟨Kron.irredQ_sound p h⟩
      atP p Fq n (2 * n * n + 8) (4 * n * n + 20) st
    else st) (B0, [1])


end IrrPts

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The code of `c(t)/D(t)` (rational coefficients) at level `m + 1`. -/
def fracCodeQ (m : ℕ) (c D : CPoly ℚ) : LC (m + 1) := (c.map (mcst Fc ks m), D.map (mcst Fc ks m))

/-- Gauss–Jordan inverse of a square matrix of codes (untrusted). -/
def gjInvC (m n : ℕ) (A : List (List (LC (m + 1)))) : Option (List (List (LC (m + 1)))) :=
  let O := MOr Fc ks (m + 1)
  let aug : List (List (LC (m + 1))) := (List.range n).map fun i ↦
    ((List.range n).map fun j ↦ (A.getD i []).getD j O.zero) ++
      (List.range n).map fun j ↦ if i = j then O.one else O.zero
  let step : Option (List (List (LC (m + 1)))) → ℕ → Option (List (List (LC (m + 1)))) :=
    fun M? c ↦ do
      let M ← M?
      let p ← (List.range n).find? fun r ↦ c ≤ r && !O.isZero ((M.getD r []).getD c O.zero)
      let rp := M.getD p []
      let iv := O.inv (rp.getD c O.zero)
      let rp' := rp.map (O.mul iv)
      let M1 := (List.range n).map fun r ↦
        if r = p then M.getD c [] else if r = c then rp' else M.getD r []
      pure ((List.range n).map fun r ↦
        if r = c then rp' else
          let f := (M1.getD r []).getD c O.zero
          (List.range (2 * n)).map fun j ↦ O.add ((M1.getD r []).getD j O.zero)
            (O.neg (O.mul f (rp'.getD j O.zero))))
  ((List.range n).foldl step (some aug)).map fun M ↦ M.map fun r ↦ r.drop n

/-- The weight at infinity `max ⌈deg aᵢ/(n − i)⌉` (so that `y = θ/tᵏ` is integral there). -/
def kAuto (Fq : BPoly ℚ) (n : ℕ) : ℕ :=
  (List.range n).foldr (fun i k ↦ max k (((Fq.getD i []).length - 1 + (n - i) - 1) / (n - i))) 0

/-- **The integral basis codes** `(Tc, Ti)` (rows `Bⱼ/D` and the inverse) of the curve `Fq` over
`ℚ`, if the special points are rational. -/
def ibBasis (m : ℕ) (Fq : BPoly ℚ) (n kI : ℕ) :
    Option (List (List (LC (m + 1))) × List (List (LC (m + 1)))) := do
  let BD : List (BPoly ℚ) × CPoly ℚ :=
    match autoGlobal ratRF Fq n (max kI (kAuto Fq n)) 8 (4 * n * n + 20) with
    | some G => (G.I.Bc, G.I.Dc)
    | none =>
      let st := finIntBasis Fq n
      let kI' := max kI (kAuto Fq n)
      -- normalize at infinity (Trager) when the branches there are rational
      match certAtAuto ratRF (invB Fq kI' (kI' * n)) 0 (2 * n * n + 10) (2 * n * n + 8) with
      | some ci => (normLoop n kI' st.2 ci (4 * n * n + 20) st.1, st.2)
      | none => st
  let Tc := (List.range n).map fun j ↦ (List.range n).map fun i ↦
    fracCodeQ Fc ks m ((BD.1.getD j []).getD i []) BD.2
  let Ti ← gjInvC Fc ks m n Tc
  pure (Tc, Ti)

/-- **The exact-part test in an integral basis** (untrusted basis, checked by `exactT`). -/
def exactTI (m : ℕ) (solve : SysSolver m) (P : GPoly (LC (m + 1))) (Fq : BPoly ℚ) (kI : ℕ)
    (f : List (LC (m + 1))) : Option Bool :=
  match ibBasis Fc ks m Fq (P.length - 1) kI with
  | none => none
  | some B => exactT Fc ks m solve P B.1 B.2 f

lemma exactTI_spec {m : ℕ} {solve : SysSolver m} {P : GPoly (LC (m + 1))} {Fq : BPoly ℚ} {kI : ℕ}
    {f : List (LC (m + 1))} {res : Bool} (h : exactTI Fc ks m solve P Fq kI f = some res) :
    ∃ Tc Ti : List (List (LC (m + 1))), exactT Fc ks m solve P Tc Ti f = some res := by
  unfold exactTI at h
  split at h
  · exact absurd h (by simp)
  · exact ⟨_, _, h⟩

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The logarithmic-level decision in an integral basis.** -/
theorem nk_iffTI (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Fq : BPoly ℚ) (kI : ℕ) (res : Bool)
    (hres : exactTI Fc ks m (primSysC Fc ks m η (paramLimC Fc ks lv m)) (nkPC Fc ks m Pp) Fq kI
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  obtain ⟨Tc', Ti', h⟩ := exactTI_spec Fc ks hres
  exact T.nk_iffT hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp Tc' Ti' res h

/-- **The exponential-level decision in an integral basis.** -/
theorem nk_iffETI (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Fq : BPoly ℚ) (kI : ℕ) (res : Bool)
    (hres : exactTI Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp) Fq kI
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  obtain ⟨Tc', Ti', h⟩ := exactTI_spec Fc ks hres
  exact T.nk_iffET hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp Tc' Ti' res h

end MTower

end Curves.MT
