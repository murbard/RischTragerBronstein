import RischTragerBronstein.Mixed.NKDecidesETInf0MR
import RischTragerBronstein.Mixed.NKRam0Cand
import RischTragerBronstein.Mixed.NKWitET
import RischTragerBronstein.Mixed.NKDecidesPM
import RischTragerBronstein.Mixed.NKMultiRWit

/-!
# Several slopes at infinity and a split fibre above `t = 0`: variants

`searchET0MP` and `nk_decidesETInf0MRP` (precomputed candidates first), `nk_decidesETInf0MRPW`
(no independence certificate), `nk_decidesETInf0MRPM` (multiplicatively independent S-units) and
`nk_integrateETInf0MRPW` (the antiderivative, `NKExpl`, as `nk_integrateETInf0RPW`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- **The search with precomputed candidates** (several places above `t = 0`), tried first. -/
def searchET0MP (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (et0MTry Fc ks m a rde Pp np dθ wθ s f) with
  | some b => some b
  | none => searchET0M Fc ks m a rde Pp np dθ wθ s f B

lemma searchET0MP_sound (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ) (b : Bool)
    (h : searchET0MP Fc ks m a rde Pp np dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (gls : List (GPoly (LC (m + 1))))
      (J D : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ)
      (Cg Cgi C Ci : List (List (LC m))) (dg dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 2 = np + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true ∧
      exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchET0MP at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold et0MTry at hc
    dsimp only at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchET0M_sound Fc ks m a rde Pp np dθ wθ s f B b h

lemma searchET0MP_isSome (m : ℕ) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ)
    (h : (searchET0M Fc ks m a rde Pp np dθ wθ s f B).isSome) :
    (searchET0MP Fc ks m a rde Pp np dθ wθ s f pre B).isSome := by
  unfold searchET0MP
  split
  · rfl
  · exact h

/-- The checks on a candidate (ramified at infinity, several places above `t = 0`). -/
def et0MCond (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (cc : CandET0R m) : Bool :=
  let c := cc.2.2.2.1
  decide (c.2.2.1.length + 2 = np + Pp.length) &&
      unitsC0 Fc ks m Pp c.1 c.2.1 cc.1 cc.2.1 ((MO Fc ks m).deriv a) c.2.2.1 dθ wθ s &&
      indepWC Fc ks m c.2.2.1 c.2.2.2.1 cc.2.2.1 c.2.2.2.2.1

def et0MExW (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (cc : CandET0R m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  etvrExW Fc ks m a rde Pp f cc.2.2.2

lemma searchET0MP_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandET0R m)) (B : ℕ) :
    searchET0MP Fc ks m a rde Pp np dθ wθ s f pre B =
      searchPS (et0MCond Fc ks m a Pp np dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2) pre B := by
  have ht : et0MTry Fc ks m a rde Pp np dθ wθ s f = tryS (et0MCond Fc ks m a Pp np dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2) := funext fun _ ↦ rfl
  have hs : searchET0M Fc ks m a rde Pp np dθ wθ s f B = searchS (et0MCond Fc ks m a Pp np dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2) B := by
    unfold searchET0M searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandET0R m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchET0MP searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (et0MCond Fc ks m a Pp np dθ wθ s) (fun cc ↦ etvrEx Fc ks m a rde Pp f cc.2.2.2)) pre = o
  cases o <;> rfl

def nkET0MRW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (et0MCond Fc ks m a Pp np dθ wθ s) (et0MExW Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

lemma et0MExW_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandET0R m) :
    (et0MExW Fc ks m a rde Pp f c).map Option.isSome = etvrEx Fc ks m a rde Pp f c.2.2.2 :=
  etvrExW_isSome _ _ _ _ _ _ _ _

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision with precomputed candidates tried first: several slopes at infinity and a split
fibre above `t = 0`, with `∑ₖ |Γₖ| + n − 2` S-units** (exponential level): for every large bound, `elM` decides `τ(f)/n`, `searchET0`
decides the exact part (finding the units, the basis and both gauges), and together they decide
`f`. -/
theorem nk_decidesETInf0MRP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ) (H : List (List (LC (m + 1)))),
      gls.length + 2 = nPlacesR segs + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      indepWC Fc ks m gls J D H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0MP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
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
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg, dg0, hex⟩ := T.exactTLEVG_exists_multiR0 m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck segs hms βs hsp0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchET0M_complete Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs kk jj gls J D H Tc Ti r Cg Cgi C Ci dg dg0 hk1 hU hJH
    hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchET0MP_isSome Fc ks m a _ Pp (nPlacesR segs) dθ wθ s _
    pre N (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', kk', jj', gls', J', D', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg', dg0', hk1', hU',
    hJH', hex'⟩ := searchET0MP_sound Fc ks m a _ Pp (nPlacesR segs) dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInf0MR hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ Us' Vs' kk' jj'
    gls' hk1' dθ wθ s hU' J' D' H' hJH' hθ hgen hs fp Tc' Ti' res dg' Cg' Cgi' r' C' Ci' dg0' hex', h0,
    hiff]

/-- **`nk_decidesETInf0MRP` without an independence certificate.** -/
theorem nk_decidesETInf0MRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 2 = nPlacesR segs + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0MP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, kk, jj, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, hJH, -⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC0_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInf0MRP hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms βs
    hsp0 θ hθ hgen dθ wθ s hs ⟨Us, Vs, kk, jj, gls, J, D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesETInf0MRPW` with multiplicatively independent units.** -/
theorem nk_decidesETInf0MRPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 2 = nPlacesR segs + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) * T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ))) ^ a i =
          algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0MP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, kk, jj, gls, hk1, hU, hmult⟩ := hunits
  have hn0 : 0 < Pp.length := by
    unfold multiShapeRC at hms
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    exact hms.1.1.1.1
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesETInf0MRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms βs hsp0 θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, kk, jj, gls, hk1, hU, fun h1 ↦ T.hli_of_mult0 m h1 (by omega) hk (h1 m (by omega)) θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs kk jj gls dθ wθ s hs hU (hmult h1)⟩ fp pre

/-- **The integral over an exponential level, several slopes at infinity and split above
`t = 0`, decided and computed.** -/
theorem nk_integrateETInf0MRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 2 = nPlacesR segs + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkET0MRW Fc ks lv m a Pp (nPlacesR segs) dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.2.2.2.1.1.getD i [])) *
            T.ts m ^ (-((b.1.2.1.getD i 0 : ℕ) : ℤ))) b.1.2.2.2.1.2.2.1.length b.2 := by
  have hn0 : 0 < Pp.length := by
    unfold multiShapeRC at hms
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    exact hms.1.1.1.1
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (et0MExW_isSome Fc ks m a _ Pp _) pre N).trans
        (searchET0MP_eq Fc ks m a _ Pp (nPlacesR segs) dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInf0MRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms βs
      hsp0 θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [et0MCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units0_logs m h1 (by omega) hk (h1 m (by omega)) θ Pp hP _ _ _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC0_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

end MTower

end Curves.MT
