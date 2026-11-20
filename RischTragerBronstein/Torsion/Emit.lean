import RischTragerBronstein.Torsion.AutoField

/-!
# Emitting kernel-checkable certificates

The automatic decision `decideLoop` runs natively; to obtain a **theorem** for a given integrand
over `ℚ`, `emitStage` reruns the last stage (over the field `ℚ[γ]/(M)` found by the loop), extracts
the certificates behind the answer — the branch data of the integrand, and either the log
witnesses (elementary) or a non-torsion witness at places (not elementary) — and prints a Lean file:
the data, one `decide +kernel` lemma per conjunct of the check (to bound the memory of each), and
the theorem, obtained from `not_elementary_of_torsOKP` or `decideLogT_spec` through the base change
`ℚ → ℚ[γ]/(M) → Kc` (as in `decideLoop_spec`). Nothing here is trusted: the emitted file is
checked by Lean.
-/

namespace Curves.Emit

open CPoly Sup

/-- Printing as Lean source. -/
class ToLean (α : Type*) where
  toLean : α → String

export ToLean (toLean)

instance : ToLean ℕ := ⟨toString⟩
instance : ToLean ℤ := ⟨fun z ↦ if z < 0 then s!"({z})" else toString z⟩
instance : ToLean ℚ := ⟨fun q ↦
  if q.den = 1 then (if q.num < 0 then s!"({q.num})" else toString q.num)
  else s!"({q.num}/{q.den})"⟩
instance {α : Type*} [ToLean α] : ToLean (List α) :=
  ⟨fun l ↦ "[" ++ ", ".intercalate (l.map toLean) ++ "]"⟩
instance {α β : Type*} [ToLean α] [ToLean β] : ToLean (α × β) :=
  ⟨fun ab ↦ "(" ++ toLean ab.1 ++ ", " ++ toLean ab.2 ++ ")"⟩
instance {p : ℕ} : ToLean (ZMod p) := ⟨fun a ↦ toString a.val⟩
/-- Elements of `ℚ[γ]/(M)`, printed with the name `MM` for `M`. -/
instance {M : CPoly ℚ} : ToLean (NFC.NF M) := ⟨fun x ↦ "(NFC.mk MM " ++ toLean x.1 ++ ")"⟩

instance {F : Type*} [ToLean F] : ToLean (BranchCert F) :=
  ⟨fun c ↦ s!"⟨{c.N}, {toLean c.ys}, {c.prec}⟩"⟩
instance {F : Type*} [ToLean F] : ToLean (CurveProb F) :=
  ⟨fun P ↦ s!"⟨{toLean P.Fc}, {P.n}, {P.k}, {toLean P.A}, {toLean P.D}, {toLean P.pts}, {toLean P.inf}⟩"⟩
instance {F : Type*} [ToLean F] : ToLean (IntBasisCert F) :=
  ⟨fun I ↦ s!"⟨{toLean I.Bc}, {toLean I.Dc}, {toLean I.δL}, {toLean I.pts}, {toLean I.infc}, {toLean I.Linf}⟩"⟩
instance {F : Type*} [ToLean F] : ToLean (GlobalCert F) :=
  ⟨fun T ↦ s!"⟨{toLean T.Fc}, {T.n}, {T.k}, {T.kD}, {toLean T.I}, {toLean T.aE}, {toLean T.αL}, {toLean T.yL}, {toLean T.cΓ}, {toLean T.ΓL}, {T.cdeg}⟩"⟩
instance {F : Type*} [ToLean F] : ToLean (PlaceCert F) :=
  ⟨fun D ↦ s!"⟨{toLean D.fib}, {toLean D.pl}, {toLean D.rt}, {toLean D.Γp}, {toLean D.cf}, {toLean D.dΓ}, {D.cΓ}, {toLean D.tp}⟩"⟩
instance {p : ℕ} : ToLean (PrimeCert p) :=
  ⟨fun P ↦ s!"⟨{toLean P.pts}, {toLean P.infc}, {toLean P.Linf}, {toLean P.xs}, {toLean P.ys}, {toLean P.lam}, {toLean P.Ls}, {toLean P.cΓ}, {P.mp}, {toLean P.Gw}, " ++
    (match P.aI with | none => "none" | some a => s!"some {toLean a}") ++ s!", {P.irrP}⟩"⟩
instance {p : ℕ} : ToLean (PlaceCert.PrimeData p) := ⟨fun Q ↦ s!"⟨{Q.mp}, {toLean Q.Gw}⟩"⟩
instance {F : Type*} [ToLean F] : ToLean (LogWit F) := ⟨fun w ↦ s!"⟨{w.m}, {toLean w.W}, {toLean w.Q}⟩"⟩

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F] [ToLean F]

/-- The components of a non-torsion witness (the prime certificates carry their primes). -/
def twDefs (tw : TorsWitP F) : String :=
  s!"def TT : GlobalCert KK := {toLean tw.T}\n\n" ++
  s!"def PcW : PlaceCert KK := {toLean tw.Pc}\n\n" ++
  s!"def Pp : PrimeCert {tw.p} := {toLean tw.Pp}\n\n" ++
  s!"def Pq : PrimeCert {tw.q} := {toLean tw.Pq}\n\n" ++
  s!"def Qp : PlaceCert.PrimeData {tw.p} := {toLean tw.Qp}\n\n" ++
  s!"def Qq : PlaceCert.PrimeData {tw.q} := {toLean tw.Qq}\n\n" ++
  s!"def LmW : List (List KK) := {toLean tw.Lm}\n\n" ++
  s!"def tw : TorsWitP KK :=\n  ⟨TT, PcW, {toLean tw.eL}, {tw.s}, ⟨{tw.j₀.val}, by decide +kernel⟩, {tw.p}, {tw.q}, Pp, Pq, Qp, Qq, {tw.Pb}, LmW⟩\n\n"

end Curves.Emit

namespace Curves

open CPoly Sup Emit

variable (P0 : CurveProb ℚ)

/-- The header: the field and the integrand over `ℚ`. -/
def emitHeader (name : String) (M : CPoly ℚ) : String :=
  "import RischTragerBronstein\n\n" ++
  "open Polynomial CPoly Sup Differential IntermediateField\n\n" ++
  s!"namespace Curves.{name}\n\n" ++
  s!"/-- The coefficient field `ℚ[γ]/(M)`. -/\ndef MM : CPoly ℚ := {toLean M}\n\n" ++
  "theorem hMM : Kron.irredQ MM = true := by decide +kernel\n\n" ++
  "instance : Fact (Irreducible (toPoly MM)) := ⟨Kron.irredQ_sound MM hMM⟩\n\n" ++
  "abbrev KK := NFC.NF MM\n\n" ++
  s!"/-- The integrand over `ℚ`. -/\ndef P0 : CurveProb ℚ := {toLean P0}\n\n"

/-- The common part of the final theorems. -/
def emitFooterIntro : String :=
  "variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]\n" ++
  "variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]\n\n"

/-- The branch certificate above infinity, one definition per root (so that the kernel checks the
roots one at a time), and the checks: one lemma per root, then `certCheck`. -/
def emitInf {F : Type*} [ToLean F] (N : ℕ) (ys : List (CPoly F)) (prec : ℕ) : String × String :=
  let ks := List.range ys.length
  let defs := String.join (ks.map fun k ↦ s!"def infY{k} : CPoly KK := {toLean (ys.getD k [])}\n\n")
  let infDef := s!"def infB : BranchCert KK := ⟨{N}, [" ++ ", ".intercalate (ks.map fun k ↦ s!"infY{k}") ++
    s!"], {prec}⟩\n\n"
  let rootLemmas := String.join (ks.map fun k ↦
    s!"set_option maxRecDepth 200000 in\nlemma okInfR{k} : rootCheck (invB Pb.Fc Pb.k (Pb.k * Pb.n)) 0 {N} {prec} infY{k} = true := by\n  decide +kernel\n\n")
  let okInf := "set_option maxRecDepth 200000 in\nlemma okInf : certCheck (invB Pb.Fc Pb.k (Pb.k * Pb.n)) Pb.n 0 Pb.inf = true := by\n" ++
    "  have e : Pb.inf = infB := rfl\n  rw [e, infB, certCheck]\n" ++
    "  simp only [List.all_cons, List.all_nil, " ++ ", ".intercalate (ks.map fun k ↦ s!"okInfR{k}") ++
    ", Bool.and_true]\n  decide +kernel\n\n"
  (defs ++ infDef, rootLemmas ++ okInf)

/-- **The file for a non-elementary answer** (witness `tw` over `ℚ[γ]/(M)`, branch data `Pb`). -/
def emitNonElem (name : String) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (k : ℕ)
    (pts : List (NFC.NF M × BranchCert (NFC.NF M))) (inf : BranchCert (NFC.NF M))
    (tw : TorsWitP (NFC.NF M)) : String :=
  emitHeader P0 name M ++
  s!"def ptsB : List (KK × BranchCert KK) := {toLean pts}\n\n" ++
  (emitInf inf.N inf.ys inf.prec).1 ++
  s!"/-- The integrand over `ℚ[γ]/(M)` with its branch data. -/\n" ++
  s!"def Pb : CurveProb KK := P0.baseChange (algebraMap ℚ KK) {k} ptsB infB\n\n" ++
  twDefs tw ++
  "/-! The kernel checks, one conjunct at a time. -/\n\n" ++
  (emitInf inf.N inf.ys inf.prec).2 ++
  "set_option maxRecDepth 200000 in\nlemma okV : Pb.valid = true := by\n  unfold CurveProb.valid\n  rw [okInf]\n  decide +kernel\n\n" ++
  "set_option maxRecDepth 200000 in\nlemma okG : tw.T.globalCheck = true := by decide +kernel\n\n" ++
  "set_option maxRecDepth 200000 in\nlemma okPc : tw.Pc.check tw.T.Fc tw.T.n = true := by decide +kernel\n\n" ++
  "set_option maxRecDepth 200000 in\nlemma okR : torsResCheckP Pb tw.T tw.Pc tw.eL tw.s tw.j₀ = true := by decide +kernel\n\n" ++
  "set_option maxRecDepth 200000 in\nlemma okP : primeOKP (redAtM MM) tw.T tw.Pc tw.p tw.Pp tw.Qp = true := by decide +kernel\n\n" ++
  "set_option maxRecDepth 200000 in\nlemma okQ : primeOKP (redAtM MM) tw.T tw.Pc tw.q tw.Pq tw.Qq = true := by decide +kernel\n\n" ++
  "set_option maxRecDepth 200000 in\nlemma okN : nonPrincOK tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp * tw.Pc.cΓ) tw.Pb\n" ++
  "    tw.T.I.δL tw.T.I.Bc tw.T.I.Dc tw.Pc.αs (tw.Pc.fcerts tw.T.n)\n" ++
  "    (tw.Pc.bL tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp)) tw.Lm = true := by\n  decide +kernel\n\n" ++
  "lemma okAll : torsOKP (redAtM MM) Pb tw = true := by\n  unfold torsOKP\n  rw [okV, okG, okPc, okR, okP, okQ, okN, Bool.or_true]\n  decide\n\n" ++
  emitFooterIntro ++
  "/-- **The integral is not elementary** (certificates checked above). -/\n" ++
  "theorem not_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)\n" ++
  "    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)\n" ++
  "    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) :\n" ++
  "    ¬ HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) := by\n" ++
  "  set ι : KK →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Kc)).toRingHom\n" ++
  "  have hι : ι.comp (algebraMap ℚ KK) = algebraMap ℚ Kc := Subsingleton.elim _ _\n" ++
  "  have hSF' : S.F = (toB Pb.Fc).map (mapRingHom ι) := by\n" ++
  "    rw [hSF, Pb, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]\n" ++
  "  have h := not_elementary_of_torsOKP hC S hx hgen (redAtM MM) (redAtM_valid MM) Pb ι hSF' tw okAll\n" ++
  "  rwa [Pb, S.fE_baseChange, hι] at h\n\n" ++
  s!"end Curves.{name}\n"

/-- **The file for an answer by log witnesses** (`decideLog`). -/
def emitLog (name : String) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (k : ℕ)
    (pts : List (NFC.NF M × BranchCert (NFC.NF M))) (inf : BranchCert (NFC.NF M))
    (ws : List (LogWit (NFC.NF M))) (b : Bool) (sol : Option (List (NFC.NF M))) (allZero : Bool) :
    String :=
  emitHeader P0 name M ++
  s!"def ptsB : List (KK × BranchCert KK) := {toLean pts}\n\n" ++
  (emitInf inf.N inf.ys inf.prec).1 ++
  s!"def Pb : CurveProb KK := P0.baseChange (algebraMap ℚ KK) {k} ptsB infB\n\n" ++
  s!"def ws : List (LogWit KK) := {toLean ws}\n\n" ++
  (emitInf inf.N inf.ys inf.prec).2 ++
  "set_option maxRecDepth 200000 in\nlemma okV : Pb.valid = true := by\n  unfold CurveProb.valid\n  rw [okInf]\n  decide +kernel\n\n" ++
  -- the checks of `decideLog`, one at a time: the exact part (with its solution), the residues,
  -- the witnesses and the zero test
  (match sol with
    | none =>
      "set_option maxRecDepth 200000 in\nlemma okL : linSolve Pb.cols Pb.rhs = none := by decide +kernel\n\n" ++
      s!"lemma okD : Pb.decideLog ws = some {b} := by\n  simp only [CurveProb.decideLog, okV, okL, ↓reduceIte]\n\n"
    | some cs =>
      s!"def csW : List KK := {toLean cs}\n\n" ++
      "set_option maxRecDepth 200000 in\nlemma okL : linSolve Pb.cols Pb.rhs = some csW := by decide +kernel\n\n" ++
      s!"set_option maxRecDepth 200000 in\nlemma okR : (Pb.allRes.all fun r ↦ decide (r = 0)) = {allZero} := by decide +kernel\n\n" ++
      (if allZero then
        s!"set_option maxRecDepth 200000 in\nlemma okZ : isZeroB (modF Pb.Fc Pb.n (Pb.Pg (Pb.Wsol csW))) = {b} := by decide +kernel\n\n" ++
        s!"lemma okD : Pb.decideLog ws = some {b} := by\n  simp only [CurveProb.decideLog, okV, okL, okR, okZ, ↓reduceIte]\n\n"
      else
        "set_option maxRecDepth 200000 in\nlemma okW : Pb.witCheck ws = true := by decide +kernel\n\n" ++
        s!"set_option maxRecDepth 200000 in\nlemma okZ : isZeroB (modF Pb.Fc Pb.n (Pb.logNum csW ws)) = {b} := by decide +kernel\n\n" ++
        s!"lemma okD : Pb.decideLog ws = some {b} := by\n  simp only [CurveProb.decideLog, okV, okL, okR, okW, okZ, ↓reduceIte, Bool.false_eq_true]\n\n")) ++
  s!"lemma okT : decideLogTP (redAtM MM) Pb ws [] [] = some {b} := by\n" ++
  "  simp [decideLogTP, decideLogT, okD]\n\n" ++
  emitFooterIntro ++
  "/-- **The decision** (certificates checked above). -/\n" ++
  "theorem decided (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)\n" ++
  "    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)\n" ++
  "    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) :\n" ++
  s!"    HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ {b} = true := by\n" ++
  "  set ι : KK →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Kc)).toRingHom\n" ++
  "  have hι : ι.comp (algebraMap ℚ KK) = algebraMap ℚ Kc := Subsingleton.elim _ _\n" ++
  "  have h := decideLogTP_baseChange_spec hC S hx hgen (redAtM MM) (redAtM_valid MM)\n" ++
  s!"    (algebraMap ℚ KK) P0 {k} ptsB infB ι (by rw [hι]; exact hSF) ws [] [] {b} okT\n" ++
  "  rwa [hι] at h\n\n" ++
  s!"end Curves.{name}\n"

/-- **Rerun the last stage and emit the certificate file** (`none` if the stage does not answer). -/
def emitStage (name : String) (fast : Bool) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]
    (kI : ℕ) (exs : List ℕ) (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) : Option String :=
  let φ := algebraMap ℚ (NFC.NF M)
  let rf := if fast then NFC.rfNFZ M else NFC.rfNF M
  let Fc := P0.Fc.map (·.map φ)
  let A := P0.A.map (·.map φ)
  let D := P0.D.map φ
  let pqs := if pqs.isEmpty then autoPairs M 3 else pqs
  (autoGlobal rf Fc P0.n kI ex fuel).bind fun T ↦
    exs.findSome? fun e ↦ (autoCurveProb rf Fc P0.n P0.k A D e).bind fun P ↦
      let Pb := P0.baseChange φ P0.k P.pts P.inf
      -- the first pair of primes at which every coordinate is treated settles this precision
      -- (a failing `decideLog` then asks for more precision, not for other primes)
      (pqs.findSome? fun pq ↦
        -- the cheap coordinates first; the first non-torsion witness is emitted (the kernel checks it)
        let js := (List.finRange (EllQuad.QCoords.dim (NFC.NF M))).mergeSort fun i j ↦
          coordCost rf Pb T L tp i ≤ coordCost rf Pb T L tp j
        match js.findSome? fun j ↦ ((autoCoord rf (redAtM M) Pb T L tp B pq.1 pq.2 j).map (·.2)).bind
            List.head? with
        | some tw => some (some (emitNonElem P0 name M P0.k P.pts P.inf tw))
        | none =>
          let cs := (List.finRange (EllQuad.QCoords.dim (NFC.NF M))).map
            (autoCoord rf (redAtM M) Pb T L tp B pq.1 pq.2)
          if cs.all Option.isSome then
            let ws := cs.map fun c ↦ (c.bind (·.1)).getD ⟨1, [[1]], [1]⟩
            some ((Pb.decideLog ws).map fun b ↦ emitLog P0 name M P0.k P.pts P.inf ws b
              (linSolve Pb.cols Pb.rhs) (Pb.allRes.all fun r ↦ decide (r = 0)))
          else none).bind id

/-- **Decide and emit**: the loop over number fields of `decideLoop` (adjoining the missing roots),
then `emitStage` over the field it reaches. -/
def emitLoop (name : String) (fast : Bool) (kI : ℕ) (exs : List ℕ) (ex fuel L tp B : ℕ)
    (pqs : List (ℕ × ℕ)) : ℕ → (M : CPoly ℚ) → Kron.irredQ M = true → Option String
  | 0, _, _ => none
  | m + 1, M, hM =>
    haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    let φ := algebraMap ℚ (NFC.NF M)
    let rf := if fast then NFC.rfNFZ M else NFC.rfNF M
    match probeMissing rf (P0.Fc.map (·.map φ)) P0.n P0.k kI (P0.D.map φ) L fuel with
    | some g =>
      match NFC.extStep M (remRoots fast M g) with
      | some ⟨M', hM'⟩ => emitLoop name fast kI exs ex fuel L tp B pqs m M' hM'
      | none => none
    | none => emitStage P0 name fast M kI exs ex fuel L tp B pqs

end Curves
