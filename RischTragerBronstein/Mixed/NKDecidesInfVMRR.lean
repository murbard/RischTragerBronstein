import RischTragerBronstein.Mixed.NKDecidesInfVMR
import RischTragerBronstein.Mixed.NKInfRVMRR

/-!
# Several slopes at infinity with residue-free finite poles: the decision (logarithmic level)

**`nk_decidesInfVMRR`**: `nk_decidesInfVMR` for integrands `∑ bⱼ(t)/D(t) θʲ` with `D` squarefree and
residue-free poles (`resCert`): `elM` and `searchIVMP` decide elementary integrability.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`nk_decidesInfVMR` with residue-free finite poles** (`∑ bⱼ(t)/D(t) θʲ`, `resCert`): with
`∑ₖ |Γₖ| − 1` units (logarithmic level; `pre` arbitrary candidates tried first): for every large
bound, `elM` decides `τ(f)/n`, `searchIVMP` decides the exact part (finding the units, the basis,
the gauge and the diagonal data), and together they decide `f`. -/
theorem nk_decidesInfVMRR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = nPlacesR segs ∧
      unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N = some b ∧
      searchIVMP Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set q := nkTau Fc ks m Pp.length (nkFlR m fp D) s
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
  obtain ⟨Tc, Ti, r, C, Ci, dg, hex⟩ := T.exactTLVG_exists_multiR m hTr (by omega) hk (hTr m (by omega))
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega))) (prdeC Fc ks lv m) MSm.rde
    Pp qE csE sE tE s2E t2E hck segs hms θ hθ (nkRest Fc ks m (nkFlR m fp D) q) gls
  obtain ⟨B0, hB0⟩ := searchIVM_complete Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
    (nkRest Fc ks m (nkFlR m fp D) q) Us Vs gls J H Tc Ti r C Ci dg hk1 hU hJH hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (searchIVMP_isSome Fc ks m η _ Pp
    (nPlacesR segs) dθ wθ s _ pre N (hB0 N (le_of_max_le_right hN)))
  obtain ⟨Us', Vs', gls', J', H', Tc', Ti', r', C', Ci', dg', hk1', hU', hJH', hex'⟩ :=
    searchIVMP_sound Fc ks m η _ Pp (nPlacesR segs) dθ wθ s _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffInfVMRR hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ Us' Vs' gls'
    hk1' dθ wθ s hU' J' H' hJH' hθ hgen hs fp D hsq kc U hcert hfpl Tc' Ti' res dg' C' Ci' r' hex', h0, hiff]

end MTower

end Curves.MT
