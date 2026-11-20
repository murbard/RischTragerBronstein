import RischTragerBronstein.Mixed.NKDecidesInfVR
import RischTragerBronstein.Mixed.NKInfRVRD
import RischTragerBronstein.Mixed.NKDecidesInfVGD

/-!
# Ramified places at infinity, non-constant coefficients: the decision (logarithmic level)

`searchIVRD … B`: as `searchIVG`, with the candidates extended by the diagonal data `dg` of the
gauged limit (`(t/e) γₖ′/γₖ`), and the unit count `n/e − 1` (`n/e` places of ramification `e`).
Every answer is correct (`searchIVR_soundD`, `nk_iffInfVRD`), and **when the units exist the search
answers for every large `B`** (`searchIVR_completeD`, from `exactTLVG_exists_ram`).

**`nk_decidesInfVRD`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithmic level with any coefficients in
`Fₘ[t]` (Eisenstein certificate), a single slope `s'/e` at infinity with rational places
(`ramShapeC`), and `n/e − 1` units multiplicatively independent modulo `Fₘ`: `elM` and `searchIVRD`
decide whether `∑ bⱼ θʲ` has an elementary integral.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- Candidates with denominators for the units. -/
abbrev CandIVRD (m : ℕ) : Type :=
  CandIVR m × List (GPoly (LC m)) × List (List (GPoly (LC m))) × List (List (GPoly (LC m))) ×
    List (GPoly (LC (m + 1)))

/-- The diagonal data of codes. -/
def dgOfRD (m : ℕ) (d : List (LC m × List (LC m × LC m))) : List (FRep (LC m)) :=
  d.map fun p ↦ ⟨p.1, p.2⟩

lemma dgOfR_ofD (m : ℕ) (dg : List (FRep (LC m))) : dgOfRD m (dg.map fun fr ↦ (fr.h, fr.logs)) = dg := by
  induction dg with
  | nil => rfl
  | cons a l ih => simp only [dgOfRD, List.map_cons] at ih ⊢; rw [ih]

/-- One candidate: check the units (`n/e − 1` of them), then run `exactTLVG`. -/
def ivrTryD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVRD m) : Option Bool :=
  if (decide (c.1.1.2.2.1.length + 1 = Pp.length / e) &&
      unitsCD Fc ks m Pp c.1.1.1 c.1.1.2.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 c.1.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.1.2.2.1 c.1.1.2.2.2.1 c.1.1.2.2.2.2.1) = true then
    exactTLVG Fc ks m η rde (dgOfRD m c.1.2) c.1.1.2.2.2.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.2.2.2
      (fun i ↦ c.1.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.1.1.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.1 f
      c.1.1.2.2.1
  else none

/-- **The search** over the first `B` candidates. -/
def searchIVRD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) : Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandIVRD m)) with
    | none => none
    | some c => ivrTryD Fc ks m η rde Pp e dθ wθ s f c

lemma searchIVR_soundD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) (b : Bool)
    (h : searchIVRD Fc ks m η rde Pp e dθ wθ s f B = some b) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
      (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      gls.length + 1 = Pp.length / e ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      indepC Fc ks m gls J H = true ∧
      exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · rename_i c _
    unfold ivrTryD at hk
    split_ifs at hk with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc.1.1, hc.1.2, hc.2, hk⟩

/-- **Completeness of the search**: if units and an answering basis exist, the search answers for
every large bound. -/
lemma searchIVR_completeD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1))))
    (J : List ℕ) (H Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg : List (FRep (LC m)))
    (hk1 : gls.length + 1 = Pp.length / e) (hU : unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true)
    (hJH : indepC Fc ks m gls J H = true)
    (hex : (exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchIVRD Fc ks m η rde Pp e dθ wθ s f B).isSome := by
  set c : CandIVRD m := (((Us, Vs, gls, J, H, Tc, Ti,
    (List.range ((nkPC Fc ks m Pp).length - 1)).map r, C, Ci), dg.map fun fr ↦ (fr.h, fr.logs)), ds, cUs, cVs, Es)
    with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchIVRD
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  unfold ivrTryD
  rw [if_pos (by simp [hk1, hU, hJH]), dgOfR_ofD]
  rw [exactTLVG_congr_r Fc ks m η rde dg C Ci _ r (nkPC Fc ks m Pp) Tc Ti f gls (fun k hk ↦ by
    simp [List.getD_eq_getElem?_getD, hk])]
  exact hex

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision for curves with ramified rational places at infinity (single slope), with
`n/e − 1` units** (logarithmic level): for every large bound, `elM` decides `τ(f)/n`, `searchIVRD`
decides the exact part (finding the units, the basis, the gauge and the diagonal data), and
together they decide `f`. -/
theorem nk_decidesInfVRD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length / e ∧
      unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVRD Fc ks m η (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) N =
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
  obtain ⟨Tc, Ti, r, C, Ci, dg, hex⟩ := T.exactTLVG_exists_ram m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp qE csE sE tE s2E t2E hck e sR γs hram θ hθ (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchIVR_completeD Fc ks m η (prdeC Fc ks lv m) Pp e dθ wθ s
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Us Vs ds cUs cVs Es gls J H Tc Ti r C Ci dg hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨Us', Vs', ds', cUs', cVs', Es', gls', J', H', Tc', Ti', r', C', Ci', dg', hk1', hU', hJH', hex'⟩ :=
    searchIVR_soundD Fc ks m η _ Pp e dθ wθ s _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVRD hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram θ Us' Vs' ds' cUs' cVs' Es' gls'
    hk1' dθ wθ s hU' J' H' hJH' hθ hgen hs fp Tc' Ti' res dg' C' Ci' r' hex', h0, hiff]

end MTower

end Curves.MT

