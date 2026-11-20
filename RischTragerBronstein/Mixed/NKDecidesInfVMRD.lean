import RischTragerBronstein.Mixed.NKDecidesInfVMR
import RischTragerBronstein.Mixed.NKInfRVMRD
import RischTragerBronstein.Mixed.NKDecidesInfVRD

/-!
# Several slopes at infinity, ramified or not: the decision (logarithmic level)

`searchIVMD … np B`: as `searchIVR`, with the unit count `np − 1` (`np = ∑ₖ |Γₖ|` places at infinity);
`searchIVMPD` tries precomputed candidates first. Every answer is correct (`searchIVMP_soundD`,
`nk_iffInfVMRD`), and **when the units exist the search answers for every large `B`**
(`searchIVM_completeD`, from `exactTLVG_exists_multiR`).

**`nk_decidesInfVMRD`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithmic level with any coefficients in
`Fₘ[t]` (Eisenstein certificate), Newton segments at infinity of any rational slopes with rational
places (`multiShapeRC`), and `∑ₖ |Γₖ| − 1` units multiplicatively independent modulo `Fₘ`: `elM` and
`searchIVMPD` decide whether `∑ bⱼ θʲ` has an elementary integral.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- One candidate: check the units (`np − 1` of them), then run `exactTLVG`. -/
def ivmTryD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVRD m) : Option Bool :=
  if (decide (c.1.1.2.2.1.length + 1 = np) &&
      unitsCD Fc ks m Pp c.1.1.1 c.1.1.2.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 c.1.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.1.2.2.1 c.1.1.2.2.2.1 c.1.1.2.2.2.2.1) = true then
    exactTLVG Fc ks m η rde (dgOfR m c.1.2) c.1.1.2.2.2.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.2.2.2
      (fun i ↦ c.1.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.1.1.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.1 f
      c.1.1.2.2.1
  else none

/-- **The search** over the first `B` candidates. -/
def searchIVMD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandIVRD m)) with
    | none => none
    | some c => ivmTryD Fc ks m η rde Pp np dθ wθ s f c

lemma searchIVM_soundD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchIVMD Fc ks m η rde Pp np dθ wθ s f B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      gls.length + 1 = np ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · rename_i c _
    unfold ivmTryD at hk
    split_ifs at hk with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc.1.1, hc.1.2, hc.2, hk⟩

/-- **Completeness of the search**: if units and an answering basis exist, the search answers for
every large bound. -/
lemma searchIVM_completeD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1))))
    (J : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg : List (FRep (LC m)))
    (hk1 : gls.length + 1 = np) (hU : unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true)
    (hJH : indepC Fc ks m gls J H = true)
    (hex : (exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchIVMD Fc ks m η rde Pp np dθ wθ s f B).isSome := by
  set c : CandIVRD m := (((Us, Vs, gls, J, H, Tc, Ti,
    (List.range ((nkPC Fc ks m Pp).length - 1)).map r, C, Ci), dg.map fun fr ↦ (fr.h, fr.logs)), ds, cUs, cVs, Es)
    with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchIVMD
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  unfold ivmTryD
  rw [if_pos (by simp [hk1, hU, hJH]), dgOfR_of]
  rw [exactTLVG_congr_r Fc ks m η rde dg C Ci _ r (nkPC Fc ks m Pp) Tc Ti f gls (fun k hk ↦ by
    simp [List.getD_eq_getElem?_getD, hk])]
  exact hex


/-- **The search with precomputed candidates**, tried first. -/
def searchIVMPD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVRD m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (ivmTryD Fc ks m η rde Pp np dθ wθ s f) with
  | some b => some b
  | none => searchIVMD Fc ks m η rde Pp np dθ wθ s f B

lemma searchIVMP_soundD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVRD m)) (B : ℕ) (b : Bool)
    (h : searchIVMPD Fc ks m η rde Pp np dθ wθ s f pre B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      gls.length + 1 = np ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchIVMPD at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    unfold ivmTryD at hc
    split_ifs at hc with hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc'.1.1, hc'.1.2, hc'.2, hc⟩
  · exact searchIVM_soundD Fc ks m η rde Pp np dθ wθ s f B b h

lemma searchIVMP_isSomeD (m : ℕ) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVRD m)) (B : ℕ)
    (h : (searchIVMD Fc ks m η rde Pp np dθ wθ s f B).isSome) :
    (searchIVMPD Fc ks m η rde Pp np dθ wθ s f pre B).isSome := by
  unfold searchIVMPD
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
/-- **The decision for curves with several slopes at infinity, ramified or not, with
`∑ₖ |Γₖ| − 1` units** (logarithmic level; `pre` arbitrary candidates tried first): for every large
bound, `elM` decides `τ(f)/n`, `searchIVMPD` decides the exact part (finding the units, the basis,
the gauge and the diagonal data), and together they decide `f`. -/
theorem nk_decidesInfVMRD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = nPlacesR segs ∧
      unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandIVRD m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVMPD Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
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
  obtain ⟨Tc, Ti, r, C, Ci, dg, hex⟩ := T.exactTLVG_exists_multiR m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp qE csE sE tE s2E t2E hck segs hms θ hθ (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchIVM_completeD Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs ds cUs cVs Es gls J H Tc Ti r C Ci dg hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchIVMP_isSomeD Fc ks m η _ Pp
    (nPlacesR segs) dθ wθ s _ pre N (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', ds', cUs', cVs', Es', gls', J', H', Tc', Ti', r', C', Ci', dg', hk1', hU', hJH', hex'⟩ :=
    searchIVMP_soundD Fc ks m η _ Pp (nPlacesR segs) dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVMRD hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ Us' Vs' ds' cUs' cVs' Es' gls'
    hk1' dθ wθ s hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res dg' C' Ci' r' hex', h0, hiff]

end MTower

end Curves.MT

