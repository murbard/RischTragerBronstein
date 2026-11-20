import RischTragerBronstein.Mixed.NKDecidesInfVMR0
import RischTragerBronstein.Mixed.NKInfRVMR1

/-!
# Several Newton segments at infinity, units matching the residues: the decision

`searchIVR1 … gls B`: the exact-part search of `searchIVR0` with the logarithmic derivatives `gls`
of given units. `nk_decidesInfVMR1`: with units with denominators (`unitsCD`) and a passing
residue-matching certificate (`multiMatchCk`), `elM` and `searchIVR1P` decide `∫ ∑ bⱼ θʲ`; no
rank condition on the units (only the residue divisor of `f` must be matched).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- One candidate: run `exactTLVG` with the logarithmic derivatives `gls`. -/
def ivr1Try (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1))))
    (c : CandIVR0 m) : Option Bool :=
  exactTLVG Fc ks m η rde (dgOfR m c.2) c.1.2.2.2.1 c.1.2.2.2.2 (fun i ↦ c.1.2.2.1.getD i 0)
    (nkPC Fc ks m Pp) c.1.1 c.1.2.1 f gls

/-- **The search** over the first `B` candidates. -/
def searchIVR1 (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1)))) (B : ℕ) :
    Option Bool :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandIVR0 m)) with
    | none => none
    | some c => ivr1Try Fc ks m η rde Pp f gls c

/-- **The search with precomputed candidates**, tried first. -/
def searchIVR1P (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1))))
    (pre : List (CandIVR0 m)) (B : ℕ) : Option Bool :=
  match pre.findSome? (ivr1Try Fc ks m η rde Pp f gls) with
  | some b => some b
  | none => searchIVR1 Fc ks m η rde Pp f gls B

lemma searchIVR1_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1)))) (B : ℕ)
    (b : Bool) (h : searchIVR1 Fc ks m η rde Pp f gls B = some b) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  split at hk
  · exact absurd hk (by simp)
  · exact ⟨_, _, _, _, _, _, hk⟩

lemma searchIVR1P_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1))))
    (pre : List (CandIVR0 m)) (B : ℕ) (b : Bool)
    (h : searchIVR1P Fc ks m η rde Pp f gls pre B = some b) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls = some b := by
  unfold searchIVR1P at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    exact ⟨_, _, _, _, _, _, hc⟩
  · exact searchIVR1_sound Fc ks m η rde Pp f gls B b h

lemma searchIVR1_complete (m : ℕ) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1))))
    (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg : List (FRep (LC m)))
    (hex : (exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gls).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → (searchIVR1 Fc ks m η rde Pp f gls B).isSome := by
  set c : CandIVR0 m := ((Tc, Ti, (List.range ((nkPC Fc ks m Pp).length - 1)).map r, C, Ci),
    dg.map fun fr ↦ (fr.h, fr.logs)) with hc
  refine ⟨Encodable.encode c + 1, fun B hB ↦ ?_⟩
  unfold searchIVR1
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simp only [hc]
  unfold ivr1Try
  rw [dgOfR_of]
  rw [exactTLVG_congr_r Fc ks m η rde dg C Ci _ r (nkPC Fc ks m Pp) Tc Ti f gls (fun k hk ↦ by
    simp [List.getD_eq_getElem?_getD, hk])]
  exact hex

lemma searchIVR1P_isSome (m : ℕ) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1))))
    (pre : List (CandIVR0 m)) (B : ℕ)
    (h : (searchIVR1 Fc ks m η rde Pp f gls B).isSome) :
    (searchIVR1P Fc ks m η rde Pp f gls pre B).isSome := by
  unfold searchIVR1P
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
/-- **The decision for curves with several slopes at infinity, units matching the residues**
(logarithmic level; `pre` arbitrary candidates tried first): given units with denominators
(`unitsCD`) and a passing residue-matching certificate `multiMatchCk` (no rank condition), for every
large bound `elM` decides `τ(f)/n`, `searchIVR1P` decides the exact part with the logarithmic
derivatives of the units, and together they decide `f`. -/
theorem nk_decidesInfVMR1 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
    (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
    (gls : List (GPoly (LC (m + 1)))) (hUl : Us.length = gls.length)
    (hU : unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true)
    (fp : List (GPoly (LC m))) (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m))))
    (MR : ℕ) (os : List (List (List ℤ))) (κs : List ℚ)
    (hres0 : multiMatchCk Fc ks lv m η Pp segs βs Θs MR fp Us ds os κs = true)
    (pre : List (CandIVR0 m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVR1P Fc ks m η (prdeC Fc ks lv m) Pp
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gls pre N =
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
  obtain ⟨Tc, Ti, r, C, Ci, dg, hex⟩ := T.exactTLVG_exists_multiR m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp qE csE sE tE s2E t2E hck segs hms θ hθ (nkRest Fc ks m (nkFl Fc ks m fp) q) gls
  obtain ⟨B0, hB0⟩ := searchIVR1_complete Fc ks m η (prdeC Fc ks lv m) Pp
    (nkRest Fc ks m (nkFl Fc ks m fp) q) gls Tc Ti r C Ci dg hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchIVR1P_isSome Fc ks m η _ Pp _ gls pre N
    (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Tc', Ti', r', C', Ci', dg', hex'⟩ :=
    searchIVR1P_sound Fc ks m η _ Pp _ gls pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVMR1 hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ Us Vs ds cUs cVs
    Es gls hUl dθ wθ s hU hθ hgen hs fp βs Θs MR os κs hres0 Tc' Ti' res dg' C' Ci' r' hex', h0,
    hiff]

end MTower

end Curves.MT
