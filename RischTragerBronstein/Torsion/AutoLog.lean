import RischTragerBronstein.Torsion.AutoMob

/-!
# Logarithms from passing principality tests

When the test at `M Γ` (`M = m_p m_q c_Γ`) passes over the coefficient field, its kernel vector
gives `γ = ∑ cᵢ(x) Bᵢ / D` with `div γ = M (Γ − c ∞ₓ)`; dividing by `∏ (x − α)^{M e_α}` gives `u`
with `div u = M s R_{j₀}` (the scaled `j₀`-component of the residue divisor), a log witness
(`LogWit`) for `decideLog`. `decideAutoFull` computes, for every coordinate, either such a witness
(torsion) or the non-torsion witness, and calls `decideLogTP`; **`decideAutoFull_spec`**: every
answer is correct.
-/

namespace Curves

open CPoly Sup EllQuad.QCoords

section Log

variable {F : Type*} [Field F] [DecidableEq F]

/-- The kernel vector of the test at `m Γ` (over the coefficient field), as `G[i][d]`. -/
def testKernel (n : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (Pc : PlaceCert F)
    (M m : ℕ) : Option (List (List F)) :=
  let cL := Pc.fcerts n
  let bL := Pc.bL n m
  let cols := (List.range n).flatMap fun i ↦ ((List.range (M + 1)).filter fun d ↦
    decide (d + δL.getD i 0 ≤ M)).map fun d ↦ (i, d)
  let rows := (List.range Pc.fib.length).flatMap fun j ↦ (List.range n).flatMap fun k ↦
    (List.range (rowsN Dc Pc.αs cL bL j k)).map fun t ↦ (j, k, t)
  (kernelL (cols.map fun id ↦ rows.map fun jkt ↦
      testEntryN Bc Dc Pc.αs cL jkt.1 jkt.2.1 jkt.2.2 id.1 id.2)).map fun w ↦
    (List.range n).map fun i ↦ (List.range (M + 1)).map fun d ↦
      match cols.findIdx? (· = (i, d)) with
      | some t => w.getD t 0
      | none => 0

/-- `(x − a)ᵉ`. -/
def xSubPow (a : F) : ℕ → CPoly F
  | 0 => [1]
  | e + 1 => mul (xSubPow a e) [-a, 1]

/-- The log witness from a kernel vector `G`: `W = ∑ᵢ (∑_d G[i][d] xᵈ) Bᵢ` and
`Q = D ∏ (x − αⱼ)^{M e_j}`, multiplier `M s`. -/
def logWitOf (n : ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (αs : List F) (eL : List ℤ) (M s : ℕ)
    (G : List (List F)) : LogWit F :=
  let W := (List.range n).foldr (fun i acc ↦ addB (smulB (G.getD i []) (Bc.getD i [])) acc) []
  let Wp := (List.range αs.length).foldr (fun j acc ↦
    if eL.getD j 0 < 0 then smulB (xSubPow (αs.getD j 0) (M * (-(eL.getD j 0)).toNat)) acc else acc) W
  let Q := (List.range αs.length).foldr (fun j acc ↦
    if 0 < eL.getD j 0 then mul (xSubPow (αs.getD j 0) (M * (eL.getD j 0).toNat)) acc else acc) Dc
  ⟨M * s, Wp, Q⟩

end Log

section Full

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- A bound for the order of a divisor class modulo `p` (Hasse–Weil type, `(√p + 2)^{2g}` with
`g = ∑ δⱼ + 1 − n` read off the integral basis); only a search bound. -/
def hwBound (T : GlobalCert F) (p : ℕ) : ℕ :=
  (Nat.sqrt p + 2) ^ (2 * ((T.I.δL.foldr (· + ·) 0) + 1 - T.n))

/-- The size of the test of the coordinate `j₀` at `Γ` itself (the largest number of rows), from a
first place certificate: the cheap coordinates are treated first. -/
def coordCost (rf : RootFinder F) (P : CurveProb F) (T : GlobalCert F) (L tp : ℕ)
    (j₀ : Fin (dim F)) : ℕ :=
  let fibs := (P.pts.filter fun ac ↦ ac.2.ys.any fun yt ↦ coord j₀ (P.resFin ac.1 ac.2 yt) ≠ 0).map
    Prod.fst
  ((fibs.mapM fun a ↦ (branchesAuto rf P.Fc a L).map fun bs ↦ (a, bs)).bind fun fb ↦
    (autoPlaceCert rf P j₀ L tp fb).map fun (Pc, _, _) ↦
      ((List.range Pc.fib.length).flatMap fun j ↦ (List.range T.n).map fun k ↦
        rowsN T.I.Dc Pc.αs (Pc.fcerts T.n) (Pc.bL T.n 1) j k).foldr max 0).getD 0

/-- The data of one coordinate: a log witness (torsion) or a non-torsion witness (the multipliers
`m_p` are searched up to `max B (hwBound T p)`). -/
def autoCoord (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (T : GlobalCert F) (L tp B : ℕ) (p q : ℕ) (j₀ : Fin (dim F)) :
    Option (Option (LogWit F) × List (TorsWitP F)) :=
  let fibs := (P.pts.filter fun ac ↦ ac.2.ys.any fun yt ↦ coord j₀ (P.resFin ac.1 ac.2 yt) ≠ 0).map
    Prod.fst
  if fibs.isEmpty then some (none, []) else
  -- the precision needed by the test at `Γ` itself (a first place certificate)
  let need := ((fibs.mapM fun a ↦ (branchesAuto rf P.Fc a L).map fun bs ↦ (a, bs)).bind fun fb ↦
    (autoPlaceCert rf P j₀ L tp fb).map fun (Pc, _, _) ↦
      ((List.range Pc.fib.length).flatMap fun j ↦ (List.range T.n).map fun k ↦
        rowsN T.I.Dc Pc.αs (Pc.fcerts T.n) (Pc.bL T.n 1) j k).foldr max 0).getD 0
  let tp0 := max tp (need + 2)
  let B' := max B (max (hwBound T p) (hwBound T q))
  -- the test precision is doubled until the tests have enough precision; the last precision
  -- suffices for every multiplier up to `B'²` (`exists_autoPlaceData_tp`: `m s Γ_π ≤ tp`)
  [tp0, 2 * tp0, 4 * tp0, max tp0 (B' * B' * need + 2)].findSome? fun tp' ↦
  let L' := max L (tp' + 2)
  (fibs.mapM fun a ↦ (branchesAuto rf P.Fc a L').map fun bs ↦ (a, bs)).bind fun fb ↦
  (autoPlaceCert rf P j₀ L' tp' fb).bind fun (Pc, eL, s) ↦
  if hp : p.Prime then if hq : q.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    match redAt p, redAt q with
    | some Rp, some Rq =>
      (autoPlaceData Rp T Pc B').bind fun Qp ↦ (autoPlaceData Rq T Pc B').bind fun Qq ↦
        let m := pairMult p q Qp.mp Qq.mp
        if !testSideN T.n T.I.Dc Pc.αs (Pc.fcerts T.n) (Pc.bL T.n m) then none else
        match testKernel T.n T.I.δL T.I.Bc T.I.Dc Pc (m * Pc.cΓ) m with
        | some G => some (some (logWitOf T.n T.I.Bc T.I.Dc Pc.αs eL (m * Pc.cΓ) s G), [])
        | none => some (none, (autoWitAt redAt T Pc eL s j₀ B' p q).toList)
    | _, _ => none
  else none else none

/-- **The automatic decision**: log witnesses for the torsion coordinates, non-torsion witnesses
for the others. -/
def decideAutoFull (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (T : GlobalCert F) (L tp B p q : ℕ) : Option Bool :=
  -- the cheap coordinates first; one passing non-torsion witness suffices for `some false`
  let js := (List.finRange (dim F)).mergeSort fun i j ↦ coordCost rf P T L tp i ≤ coordCost rf P T L tp j
  match js.findSome? fun j ↦ ((autoCoord rf redAt P T L tp B p q j).map (·.2)).bind
      fun tws ↦ tws.find? (torsOKP redAt P) with
  | some tw => decideLogTP redAt P [] [] [tw]
  | none =>
    -- `some true` needs all the log witnesses
    let cs := (List.finRange (dim F)).map (autoCoord rf redAt P T L tp B p q)
    decideLogTP redAt P (cs.map fun c ↦ (c.bind (·.1)).getD ⟨1, [[1]], [1]⟩) []
      (cs.flatMap fun c ↦ (c.map (·.2)).getD [])

end Full

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

open IntermediateField Differential Polynomial in
/-- **Soundness of the automatic decision.** -/
theorem decideAutoFull_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (T : GlobalCert F) (L tp B p q : ℕ) (b : Bool)
    (h : decideAutoFull rf redAt P T L tp B p q = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  unfold decideAutoFull at h
  dsimp only at h
  split at h <;> exact decideLogTP_spec hC S hx hgen redAt hred P ι hSF _ [] _ b h

end Main

end Curves
