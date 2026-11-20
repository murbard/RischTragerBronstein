import RischTragerBronstein.Mixed.NKDecidesInfVR0
import RischTragerBronstein.Mixed.NKRamCand

/-!
# Ramified places at infinity with zero residues: computed candidates (untrusted)

`ramZCands`: the monomial basis, its shifts, the level-graded gauge at infinity (`ramGaugeC`) and
the diagonal data — the units-free part of `ramCandsL`. `searchIVR0P` tries them before the
complete enumeration `searchIVR0`; every answer is correct (`searchIVR0P_sound`) and
`nk_decidesInfVR0P` keeps the decision.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **Units-free candidates** for a single ramified slope `s'/e` with residual `∏ₖ (Zᵉ − γₖ)`. -/
def ramZCands (m e sR n : ℕ) (γs : List (LC m)) : List (CandIVR0 m) :=
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
    [((I1, I1, rl, Cg, Cgi), dg)]

/-- **The search with precomputed candidates**, tried first. -/
def searchIVR0P (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (pre : List (CandIVR0 m)) (B : ℕ) :
    Option Bool :=
  match pre.findSome? (ivr0Try Fc ks m η rde Pp f) with
  | some b => some b
  | none => searchIVR0 Fc ks m η rde Pp f B

lemma searchIVR0P_sound (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (pre : List (CandIVR0 m)) (B : ℕ) (b : Bool)
    (h : searchIVR0P Fc ks m η rde Pp f pre B = some b) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f [] = some b := by
  unfold searchIVR0P at h
  split at h
  · rename_i b' hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [Option.some.inj h] at hc
    exact ⟨_, _, _, _, _, _, hc⟩
  · exact searchIVR0_sound Fc ks m η rde Pp f B b h

lemma searchIVR0P_isSome (m : ℕ) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (pre : List (CandIVR0 m)) (B : ℕ)
    (h : (searchIVR0 Fc ks m η rde Pp f B).isSome) :
    (searchIVR0P Fc ks m η rde Pp f pre B).isSome := by
  unfold searchIVR0P
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
/-- **The decision with precomputed candidates tried first** (`searchIVR0P`):
(logarithmic level): if the ramified zero-residue certificate passes, then for every large bound `elM` decides `τ(f)/n`,
`searchIVG0` decides the exact part, and together they decide `f`. -/
theorem nk_decidesInfVR0P (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sp : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sp γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (sR MR : ℕ) (γR : List (LC m)) (Θs : List (GPoly (LC m)))
    (hres0 : splitResRamCk Fc ks lv m e sR MR Pp γR Θs fp = true) (pre : List (CandIVR0 m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVR0P Fc ks m η (prdeC Fc ks lv m) Pp
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
  have hn0 : 0 < Pp.length := by
    by_contra h0
    simp [ramShapeC, show Pp.length = 0 by omega] at hram
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hshF T' (m + 1) hT'n hc hT'gen q
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
  obtain ⟨Tc, Ti, r, C, Ci, dg, hex⟩ := T.exactTLVG_exists_ram m hTr (by omega) hk
    (hTr m (by omega)) (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega)))
    (prdeC Fc ks lv m) MSm.rde Pp qE csE sE tE s2E t2E hck e sp γs hram θ hθ
    (nkRest Fc ks m (nkFl Fc ks m fp) q) []
  obtain ⟨B0, hB0⟩ := searchIVR0_complete Fc ks m η (prdeC Fc ks lv m) Pp
    (nkRest Fc ks m (nkFl Fc ks m fp) q) Tc Ti r C Ci dg hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchIVR0P_isSome Fc ks m η _ Pp _ pre N
    (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Tc', Ti', r', C', Ci', dg', hex'⟩ := searchIVR0P_sound Fc ks m η _ Pp _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVR0 hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck θ hn0 dθ wθ s hθ hgen hs fp
    e sR MR γR Θs hres0 Tc' Ti' res dg' C' Ci' r' hex', h0, hiff]

end MTower

end Curves.MT
