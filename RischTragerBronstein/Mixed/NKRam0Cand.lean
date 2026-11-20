import RischTragerBronstein.Mixed.NKDecidesETInf0R
import RischTragerBronstein.Mixed.NKSplit0Cand
import RischTragerBronstein.Mixed.NKRamCand

/-!
# A ramified place at infinity and a split fibre above `t = 0`: computed candidates

`searchET0RP` (precomputed candidates first, `searchET0RP_sound`, `searchET0RP_isSome`),
`nk_decidesETInf0RP`, and `ram0Cands` for a single ramified place at infinity (`n = e`): S-units
with zeros above `0` (`findUnit0R`: Hensel branches above `0`, monomials of bounded order at
infinity, norm by the determinant of the multiplication matrix), logarithmic derivatives,
Wronskian certificate, the ramified gauge at infinity and the Vandermonde gauge at `0`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The search with precomputed candidates** (several places above `t = 0`), tried first. -/
def searchET0RP (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (et0RTry Fc ks m a rde Pp e dθ wθ s f) with
  | some b => some b
  | none => searchET0R Fc ks m a rde Pp e dθ wθ s f B

lemma searchET0RP_sound (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ) (b : Bool)
    (h : searchET0RP Fc ks m a rde Pp e dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (gls : List (GPoly (LC (m + 1))))
      (J D : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ)
      (Cg Cgi C Ci : List (List (LC m))) (dg dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 2 = Pp.length / e + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true ∧
      exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchET0RP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold et0RTry at hc
    dsimp only at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchET0R_sound Fc ks m a rde Pp e dθ wθ s f B b h

lemma searchET0RP_isSome (m : ℕ) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ)
    (h : (searchET0R Fc ks m a rde Pp e dθ wθ s f B).isSome) :
    (searchET0RP Fc ks m a rde Pp e dθ wθ s f pre B).isSome := by
  unfold searchET0RP
  split
  · rfl
  · exact h

/-- An S-unit with divisor `μ (P0ᵢ − P∞)` (a single ramified place at infinity, `n = e`) normalized
to norm `1`: `(U, V, k, j)` with `U V = tᵏ`, the unit being `U/tʲ`. Monomials `tˡ θʲ` with
`e l + s' j ≤ μ` have distinct orders at infinity, so the pole bound is linear. -/
def findUnit0R (m n e sR Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (ys : List (List (LC m)))
    (i0 : ℕ) : Option (List (GPoly (LC m)) × List (GPoly (LC m)) × ℕ × ℕ) :=
  let O := MO Fc ks m
  (List.range mmax).findSome? fun μ0 ↦ do
    let μ : ℕ := μ0 + 1
    let B := Bmax
    -- unknowns `x_{jl}`, `j < n`, `l ≤ B`; monomials above the weight bound are forced to `0`
    let R0 := μ * n + 2
    let pw : ℕ → List (List (LC m)) := fun k ↦ serPowsO O R0 n (ys.getD k [])
    let rows : ℕ → ℕ → (ℕ → Bool) → List (List (LC m)) := fun bound k0 sel ↦
      ((List.range n).flatMap fun k ↦ if sel k then
        (List.range (if k = k0 then μ else 0) ++ (if k = k0 then [] else List.range μ)).map fun eI ↦
          (List.range n).flatMap fun (j : ℕ) ↦ (List.range (B + 1)).map fun (l : ℕ) ↦
            if eI < l then O.zero else ((pw k).getD j []).getD (eI - l) O.zero
        else []) ++
      ((List.range n).flatMap fun (j : ℕ) ↦ (List.range (B + 1)).filterMap fun (l : ℕ) ↦
        if e * l + sR * j ≤ bound then none else
          some ((List.range n).flatMap fun (j' : ℕ) ↦ (List.range (B + 1)).map fun (l' : ℕ) ↦
            if j' = j ∧ l' = l then O.one else O.zero))
    let x ← kerVecO O (n * (B + 1)) (rows μ i0 (fun k ↦ k = i0))
    let y ← kerVecO O (n * (B + 1)) (rows (μ * (n - 1)) i0 (fun k ↦ k ≠ i0))
    let u := unitPolyS Fc ks m n B x
    let v := unitPolyS Fc ks m n B y
    let uv := thMulS Fc ks m Pp u v
    let κ := (uv.getD 0 []).getD μ O.zero
    if O.isZero κ then none else
    -- the norm `N(u) = c t^μ` as the determinant of the multiplication by `u`
    let Mu : Fin n → Fin n → GPoly (LC m) := fun i j ↦
      (thMulS Fc ks m Pp u ((List.range n).map fun k ↦ if k = (j : ℕ) then [O.one] else [])).getD i []
    let Nu := pdetC O n Mu
    let cN := Nu.getD μ O.zero
    if O.isZero cN then none else
    let v' := v.map (GPoly.smul O (O.inv κ))
    pure ((thPowS Fc ks m Pp u n).map (GPoly.smul O (O.inv cN)),
      (thPowS Fc ks m Pp v' n).map (GPoly.smul O cN), n * μ, μ)

/-- **Candidates for a single ramified place at infinity (`n = e`) and a split fibre above `0`**:
the S-units `findUnit0R` (`n − 1` of them), their logarithmic derivatives `U′V/tᵏ − j η`, the
Wronskian certificate, the basis `θʲ` with shifts `⌈j s'/e⌉`, the gauge `ramGaugeC` at infinity with
its diagonal data, the Vandermonde gauge `(βₐᵇ)` at `0`, zero diagonal data at `0`. -/
def ram0Cands (m e sR R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs βs : List (LC m))
    (ηc : LC m) : List (CandET0R m) :=
  let n := Pp.length
  let r := n / e
  let O := MO Fc ks m
  let O1 := MOr Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let ys := βs.map (expand0S Fc ks m n R Pp)
  match dThetaC O1 P, (List.range (n - 1)).mapM fun i ↦ findUnit0R Fc ks m n e sR Bmax mmax Pp ys i with
  | some dθ, some us =>
    let Us := us.map (·.1)
    let Vs := us.map (·.2.1)
    let kk := us.map (·.2.2.1)
    let jj := us.map (·.2.2.2)
    let glOf : ℕ → GPoly (LC (m + 1)) := fun i ↦
      let u := nkFl Fc ks m (Us.getD i [])
      let rr := (remP O1 P (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 u)
        (GPoly.mul O1 dθ (GPoly.derivX O1 u))) (nkFl Fc ks m (Vs.getD i [])))).map
          (O1.mul (tInvPowC Fc ks m (kk.getD i 0)))
      let jη : LC (m + 1) := ([O.mul (O.natCast (jj.getD i 0)) ηc], [O.one])
      ((List.range (max rr.length 1)).map fun l ↦
        if l = 0 then O1.add (rr.getD 0 O1.zero) (O1.neg jη) else rr.getD l O1.zero)
    let gls := (List.range Us.length).map glOf
    let k := gls.length
    let J := (List.range k).map fun p ↦ 1 + p % (n - 1)
    let D := (List.range k).map fun p ↦ p / (n - 1)
    let W := (List.range k).map fun i ↦ (List.range k).map fun p ↦
      iterDC Fc ks m (D.getD p 0) ((gls.getD i []).getD (J.getD p 0) O1.zero)
    match gjInvO (MO Fc ks (m + 1)) k W, gjInvO O n (ramGaugeC Fc ks m n e sR r γs) with
    | some H, some Cgi =>
      let I1 := idMatC O1 n
      let rl := (List.range n).map fun i ↦ ((gR e sR i : ℕ) : ℤ)
      let Cg := ramGaugeC Fc ks m n e sR r γs
      let dg : List (ℚ × ℚ × LC m) := (List.range n).map fun a ↦
        (-(((e - 1 - a / r : ℕ)) : ℚ) / e, (tResC e sR (e - 1 - a / r) : ℚ) / e,
          γs.getD (a % r) O.zero)
      let g0 := (match splitGaugeS Fc ks m βs with | some g => [g, (g.2, g.1)] | none => []) ++
        [(idMatC O n, idMatC O n)]
      let dg0 := (List.range n).map fun _ ↦ ((0 : ℚ), (0 : ℚ), O.one)
      g0.map fun gz ↦
        (kk, jj, D, ((Us, Vs, gls, J, H, I1, I1, rl, Cg, Cgi, gz.1, gz.2, dg0), dg))
    | _, _ => []
  | _, _ => []

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision with precomputed candidates tried first: for curves with any coefficients split at infinity and above `t = 0`, with
`2n − 2` S-units** (exponential level): for every large bound, `elM` decides `τ(f)/n`, `searchET0`
decides the exact part (finding the units, the basis and both gauges), and together they decide
`f`. -/
theorem nk_decidesETInf0RP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ) (H : List (List (LC (m + 1)))),
      gls.length + 2 = Pp.length / e + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0RP Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hshF T' (m + 1) hT'n hc hT'gen q
  -- `L` is algebraic over `F (m + 1)`
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ
  have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have h0 : HasElementaryIntegral (T.ev (m + 1) q) ↔ HasElementaryIntegral (T'.ev (m + 1) q) := by
    rw [← hasElementaryIntegral_isAlgebraic_iff halg]
    rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) q) = T.ev (m + 1) q from
      hT'ev (m + 1) le_rfl q]
  -- the search answers for large bounds
  obtain ⟨Us, Vs, kk, jj, gls, J, D, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg, dg0, hex⟩ := T.exactTLEVG_exists_ram0 m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck e sR γs hram βs hsp0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchET0R_complete Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs kk jj gls J D H Tc Ti r Cg Cgi C Ci dg dg0 hk1 hU hJH
    hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchET0RP_isSome Fc ks m a _ Pp e dθ wθ s _
    pre N (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', kk', jj', gls', J', D', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg', dg0', hk1', hU',
    hJH', hex'⟩ := searchET0RP_sound Fc ks m a _ Pp e dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInf0R hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram θ Us' Vs' kk' jj'
    gls' hk1' dθ wθ s hU' J' D' H' hJH' hθ hgen hs fp Tc' Ti' res dg' Cg' Cgi' r' C' Ci' dg0' hex', h0,
    hiff]

end MTower

end Curves.MT
