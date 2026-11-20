import RischTragerBronstein.Mixed.NKDecidesETInfVMR
import RischTragerBronstein.Mixed.NKInfRVExpMRD
import RischTragerBronstein.Mixed.NKDecidesETInfVRD

/-!
# Several slopes at infinity, ramified or not, over an exponential level: the decision

`searchETVMD … np B`: as `searchETVR`, with the unit count `np − 1` (`np = ∑ₖ |Γₖ|` places at
infinity); `searchETVMPD` tries precomputed candidates first. Sound (`searchETVMP_soundD`,
`nk_iffETInfVMRD`) and complete when the units exist (`searchETVM_completeD`, from
`exactTLEVG_exists_multiR`).

**`nk_decidesETInfVMRD`**: for Newton segments of any rational slopes at infinity with rational
places (`multiShapeRC`), a single place above `t = 0` (`nkShape0`) and `∑ₖ |Γₖ| − 1` independent
units, `elM` and `searchETVMPD` decide whether `∑ bⱼ θʲ` has an elementary integral.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- One candidate: check the units, then run `exactTLEVG`. -/
def etvmTryD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandETVRD m) : Option Bool :=
  if (decide (c.1.1.2.2.1.length + 1 = np) &&
      unitsCD Fc ks m Pp c.1.1.1 c.1.1.2.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 c.1.1.2.2.1 dθ wθ s && indepC Fc ks m c.1.1.2.2.1 c.1.1.2.2.2.1 c.1.1.2.2.2.2.1)
    = true then
    exactTLEVG Fc ks m a rde c.1.2 c.1.1.2.2.2.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.2.2.2.1
      (fun i ↦ c.1.1.2.2.2.2.2.2.2.1.getD i 0) c.1.1.2.2.2.2.2.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.2.2.2.2.2.1
      c.1.1.2.2.2.2.2.2.2.2.2.2.2.2 (nkPC Fc ks m Pp) c.1.1.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.1 f c.1.1.2.2.1
  else none

/-- **The search** over the first `B` candidates. -/
def searchETVMD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandETVRD m)) with
    | none => none
    | some c => etvmTryD Fc ks m a rde Pp np dθ wθ s f c

lemma searchETVM_soundD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchETVMD Fc ks m a rde Pp np dθ wθ s f B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (Cg Cgi C Ci : List (List (LC m)))
      (dg dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 1 = np ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · rename_i c _
    unfold etvmTryD at hk
    split_ifs at hk with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc.1.1, hc.1.2, hc.2, hk⟩

/-- **Completeness of the search**: if units and an answering basis exist, the search answers for
every large bound. -/
lemma searchETVM_completeD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1))))
    (J : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (Cg Cgi C Ci : List (List (LC m))) (dg dg0 : List (ℚ × ℚ × LC m))
    (hk1 : gls.length + 1 = np) (hU : unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true)
    (hJH : indepC Fc ks m gls J H = true)
    (hex : (exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchETVMD Fc ks m a rde Pp np dθ wθ s f B).isSome := by
  set c : CandETVRD m := (((Us, Vs, gls, J, H, Tc, Ti,
    (List.range ((nkPC Fc ks m Pp).length - 1)).map r, Cg, Cgi, C, Ci, dg0), dg), ds, cUs, cVs, Es) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchETVMD
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  unfold etvmTryD
  rw [if_pos (by simp [hk1, hU, hJH])]
  rw [exactTLEVG_congr_r Fc ks m a rde dg Cg Cgi _ r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls
    (fun k hk ↦ by simp [List.getD_eq_getElem?_getD, hk])]
  exact hex


/-- **The search with precomputed candidates**, tried first. -/
def searchETVMPD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVRD m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (etvmTryD Fc ks m a rde Pp np dθ wθ s f) with
  | some b => some b
  | none => searchETVMD Fc ks m a rde Pp np dθ wθ s f B

lemma searchETVMP_soundD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVRD m)) (B : ℕ) (b : Bool)
    (h : searchETVMPD Fc ks m a rde Pp np dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (Cg Cgi C Ci : List (List (LC m)))
      (dg dg0 : List (ℚ × ℚ × LC m)),
      gls.length + 1 = np ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchETVMPD at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold etvmTryD at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchETVM_soundD Fc ks m a rde Pp np dθ wθ s f B b h

lemma searchETVMP_isSomeD (m : ℕ) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVRD m)) (B : ℕ)
    (h : (searchETVMD Fc ks m a rde Pp np dθ wθ s f B).isSome) :
    (searchETVMPD Fc ks m a rde Pp np dθ wθ s f pre B).isSome := by
  unfold searchETVMPD
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
/-- **The decision for curves with several slopes at infinity, ramified or not, with `∑ₖ |Γₖ| − 1`
units** (exponential level, a single place above `t = 0`; `pre` arbitrary candidates tried first):
for every large bound, `elM` decides `τ(f)/n`, `searchETVMPD` decides the exact part, and together
they decide `f`. -/
theorem nk_decidesETInfVMRD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = nPlacesR segs ∧
      unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVRD m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVMPD Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
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
  obtain ⟨Us, Vs, ds, cUs, cVs, Es, gls, J, H, hk1, hU, hJH⟩ := hunits
  obtain ⟨Tc, Ti, r, Cg, Cgi, C, Ci, dg, dg0, hex⟩ := T.exactTLEVG_exists_multiR m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) Pp qE csE sE tE s2E t2E hck segs hms hsh0 θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchETVM_completeD Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs ds cUs cVs Es gls J H Tc Ti r Cg Cgi C Ci dg dg0 hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchETVMP_isSomeD Fc ks m a _ Pp
    (nPlacesR segs) dθ wθ s _ pre N (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', ds', cUs', cVs', Es', gls', J', H', Tc', Ti', r', Cg', Cgi', C', Ci', dg', dg0', hk1', hU', hJH', hex'⟩ :=
    searchETVMP_soundD Fc ks m a _ Pp (nPlacesR segs) dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffETInfVMRD hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms hsh0 θ Us' Vs'
    ds' cUs' cVs' Es' gls' hk1' dθ wθ s hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res dg' Cg' Cgi' r' C' Ci' dg0' hex', h0,
    hiff]

end MTower

end Curves.MT

