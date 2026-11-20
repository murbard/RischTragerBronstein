import RischTragerBronstein.Mixed.NKDecidesETInfVR
import RischTragerBronstein.Mixed.NKSplitCand

/-!
# Candidates for ramified places at infinity (untrusted)

For `θⁿ + ∑ aᵢ(t) θⁱ = 0` with a single slope `s'/e` at infinity and residual polynomial
`∏ₖ (Zᵉ − γₖ)` (`ramShapeC`), the data of `searchIVR`/`searchETVR` are computed here; every output
is re-checked by the kernel checks of the decisions, the enumeration stays the complete fallback.

* `ramUnits`: when `P = M̃(θᵉ)`, the units of the split subcurve `M̃(φ) = 0`, `φ = θᵉ`
  (`splitUnits`), lifted to `θ`-polynomials; their logarithmic derivatives have coordinates only
  at multiples of `e` (independence certificate on the columns `e, 2e, …`).
* `ramGaugeC`: the gauge at infinity of the monomial basis `θʲ/t^{⌈j s'/e⌉}` — the level-graded
  Vandermonde matrix of the `γₖ`, rows sorted by decreasing level (`a ↦ (e − 1 − a/r, a mod r)`),
  with the diagonal data `((t_R/e), γₖ)` (`t_R` the residue of level `R`, `tResC`).
* `ramCandsL`, `ramCandsE`: complete candidates; `searchIVRP`, `searchETVRP` try them first.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The residue `t < e` of level `R`. -/
def tResC (e sR R : ℕ) : ℕ := ((List.range e).find? fun t ↦ levR e sR t == R).getD 0

/-- Powers of a code. -/
def powCo {α : Type} (O : COps α) (a : α) (k : ℕ) : α :=
  (List.range k).foldl (fun acc _ ↦ O.mul acc a) O.one

/-- **The gauge at infinity of the monomial basis** (rows sorted by decreasing level). -/
def ramGaugeC (m n e sR r : ℕ) (γs : List (LC m)) : List (List (LC m)) :=
  let O := MO Fc ks m
  (List.range n).map fun a ↦ (List.range n).map fun i ↦
    if levR e sR i = e - 1 - a / r then powCo O (γs.getD (a % r) O.zero) (i / e) else O.zero

/-- **The units of a curve in `θᵉ`** from its split subcurve, with logarithmic derivatives, `θ′`,
`1/P_θ`, the trace codes and the independence certificate. -/
def ramUnits (m e sR R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m)) :
    Option (List (List (GPoly (LC m))) × List (List (GPoly (LC m))) ×
      List (GPoly (LC (m + 1))) × List ℕ × List (List (LC (m + 1))) ×
      GPoly (LC (m + 1)) × GPoly (LC (m + 1)) × List (LC (m + 1))) := do
  let n := Pp.length
  let r := n / e
  let Psub := (List.range r).map fun l ↦ Pp.getD (l * e) []
  let (Us0, Vs0, _, _, _, _, _, _) ← splitUnits Fc ks m sR R Bmax mmax Psub γs
  let lift : List (GPoly (LC m)) → List (GPoly (LC m)) := fun u ↦
    (List.range n).map fun i ↦ if i % e = 0 then u.getD (i / e) [] else []
  let Us := Us0.map lift
  let Vs := Vs0.map lift
  let O1 := MOr Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let dθ ← dThetaC O1 P
  let wθ ← invModC O1 P (GPoly.derivX O1 P)
  let gls ← Us.mapM fun u ↦ logDerC O1 P dθ (nkFl Fc ks m u)
  let J := (List.range (r - 1)).map fun l ↦ e * (l + 1)
  let A := (List.range (r - 1)).map fun i ↦ J.map fun j ↦ (gls.getD i []).getD j O1.zero
  let H ← gjInvO O1 (r - 1) A
  pure (Us, Vs, gls, J, H, dθ, wθ, traceCodes Fc ks m P)

/-- **The candidates at a logarithmic level** (ramified places at infinity). -/
def ramCandsL (m e sR R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m)) :
    List (CandIVR m) :=
  match ramUnits Fc ks m e sR R Bmax mmax Pp γs with
  | none => []
  | some (Us, Vs, gls, J, H, _) =>
    let n := Pp.length
    let r := n / e
    let O := MO Fc ks m
    let I1 := idMatC (MOr Fc ks (m + 1)) n
    let rl := (List.range n).map fun i ↦ ((gR e sR i : ℕ) : ℤ)
    let Cg := ramGaugeC Fc ks m n e sR r γs
    match gjInvO O n Cg with
    | none => []
    | some Cgi =>
      let dg : List (LC m × List (LC m × LC m)) := (List.range n).map fun a ↦
        (O.zero, [(mcst Fc ks m ((tResC e sR (e - 1 - a / r) : ℚ) / e), γs.getD (a % r) O.zero)])
      [((Us, Vs, gls, J, H, I1, I1, rl, Cg, Cgi), dg)]

/-- **The candidates at an exponential level** (ramified places at infinity, a single place above
`t = 0` of trailing degree `d₀`): basis `θʲ/t^{⌊j d₀/n⌋}`, shifts `⌈j s'/e⌉ − ⌊j d₀/n⌋`. -/
def ramCandsE (m e sR R Bmax mmax : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m)) :
    List (CandETVR m) :=
  match ramUnits Fc ks m e sR R Bmax mmax Pp γs with
  | none => []
  | some (Us, Vs, gls, J, H, _) =>
    let n := Pp.length
    let r := n / e
    let O := MO Fc ks m
    let O1 := MOr Fc ks (m + 1)
    let a0 := Pp.getD 0 []
    let d0 := trailG O a0
    let c0 := a0.getD d0 O.zero
    let fl : ℕ → ℕ := fun j ↦ j * d0 / n
    let Tc := (List.range n).map fun i ↦ (List.range n).map fun j ↦
      if i = j then tInvPowC Fc ks m (fl j) else O1.zero
    let Ti := (List.range n).map fun i ↦ (List.range n).map fun j ↦
      if i = j then tPowC Fc ks m (fl j) else O1.zero
    let rl := (List.range n).map fun j ↦ ((gR e sR j : ℕ) : ℤ) - (fl j : ℤ)
    let Cg := ramGaugeC Fc ks m n e sR r γs
    match gjInvO O n Cg with
    | none => []
    | some Cgi =>
      let dg : List (ℚ × ℚ × LC m) := (List.range n).map fun a ↦
        (-(((e - 1 - a / r : ℕ)) : ℚ) / e, (tResC e sR (e - 1 - a / r) : ℚ) / e,
          γs.getD (a % r) O.zero)
      let τ := (List.range n).insertionSort fun i j ↦ j * d0 % n ≤ i * d0 % n
      let τi := (List.range n).map fun a ↦ τ.idxOf a
      let zs : List (List ℕ) := [τ, τi, List.range n, (List.range n).reverse]
      let z0 := zs.flatMap fun σ ↦
        let σi := (List.range n).map fun a ↦ σ.idxOf a
        [(permMatC O n σ, permMatC O n σi, σ), (permMatC O n σi, permMatC O n σ, σ)]
      z0.map fun c ↦
        ((Us, Vs, gls, J, H, Tc, Ti, rl, Cg, Cgi, c.1, c.2.1,
          (List.range n).map fun a ↦
            let j := c.2.2.getD a 0
            (((j * d0 % n : ℕ) : ℚ) / n, ((j : ℕ) : ℚ) / n, c0)), dg)

/-- **The ramified search with precomputed candidates** (logarithmic level), tried first. -/
def searchIVRP (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVR m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (ivrTry Fc ks m η rde Pp e dθ wθ s f) with
  | some b => some b
  | none => searchIVR Fc ks m η rde Pp e dθ wθ s f B

lemma searchIVRP_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVR m)) (B : ℕ) (b : Bool)
    (h : searchIVRP Fc ks m η rde Pp e dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      gls.length + 1 = Pp.length / e ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchIVRP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold ivrTry at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchIVR_sound Fc ks m η rde Pp e dθ wθ s f B b h

lemma searchIVRP_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVR m)) (B : ℕ)
    (h : (searchIVR Fc ks m η rde Pp e dθ wθ s f B).isSome) :
    (searchIVRP Fc ks m η rde Pp e dθ wθ s f pre B).isSome := by
  unfold searchIVRP
  split
  · rfl
  · exact h

/-- **The ramified search with precomputed candidates** (exponential level), tried first. -/
def searchETVRP (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVR m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (etvrTry Fc ks m a rde Pp e dθ wθ s f) with
  | some b => some b
  | none => searchETVR Fc ks m a rde Pp e dθ wθ s f B

lemma searchETVRP_sound (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVR m)) (B : ℕ) (b : Bool)
    (h : searchETVRP Fc ks m a rde Pp e dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (Cg Cgi C Ci : List (List (LC m)))
      (dg dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 1 = Pp.length / e ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchETVRP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold etvrTry at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchETVR_sound Fc ks m a rde Pp e dθ wθ s f B b h

lemma searchETVRP_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVR m)) (B : ℕ)
    (h : (searchETVR Fc ks m a rde Pp e dθ wθ s f B).isSome) :
    (searchETVRP Fc ks m a rde Pp e dθ wθ s f pre B).isSome := by
  unfold searchETVRP
  split
  · rfl
  · exact h

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision for curves with ramified rational places at infinity (single slope), with
`n/e − 1` units** (logarithmic level): for every large bound, `elM` decides `τ(f)/n`, `searchIVR`
decides the exact part (finding the units, the basis, the gauge and the diagonal data), and
together they decide `f`. -/
theorem nk_decidesInfVRP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length / e ∧
      unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVRP Fc ks m η (prdeC Fc ks lv m) Pp e dθ wθ s
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
  obtain ⟨Us, Vs, gls, J, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, C, Ci, dg, hex⟩ := T.exactTLVG_exists_ram m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp qE csE sE tE s2E t2E hck e sR γs hram θ hθ (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchIVR_complete Fc ks m η (prdeC Fc ks lv m) Pp e dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs gls J H Tc Ti r C Ci dg hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchIVRP_isSome Fc ks m η _ Pp e dθ wθ s _ pre N
    (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', gls', J', H', Tc', Ti', r', C', Ci', dg', hk1', hU', hJH', hex'⟩ :=
    searchIVRP_sound Fc ks m η _ Pp e dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVR hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram θ Us' Vs' gls'
    hk1' dθ wθ s hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res dg' C' Ci' r' hex', h0, hiff]

set_option maxHeartbeats 4000000 in
/-- **The decision for curves with ramified rational places at infinity (single slope), with
`n/e − 1` units** (exponential level, a single place above `t = 0`): for every large bound, `elM`
decides `τ(f)/n`, `searchETVR` decides the exact part, and together they decide `f`. -/
theorem nk_decidesETInfVRP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length / e ∧
      unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVRP Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
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
  obtain ⟨Us, Vs, gls, J, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg, dg0, hex⟩ := T.exactTLEVG_exists_ram m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck e sR γs hram hsh0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchETVR_complete Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs gls J H Tc Ti r Cg Cgi C Ci dg dg0 hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchETVRP_isSome Fc ks m a _ Pp e dθ wθ s _ pre N
    (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', gls', J', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg', dg0', hk1', hU', hJH', hex'⟩ :=
    searchETVRP_sound Fc ks m a _ Pp e dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInfVR hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram hsh0 θ Us' Vs'
    gls' hk1' dθ wθ s hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res dg' Cg' Cgi' r' C' Ci' dg0' hex', h0,
    hiff]

end MTower

end Curves.MT
