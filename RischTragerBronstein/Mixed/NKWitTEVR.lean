import RischTragerBronstein.Mixed.NKDecidesTEV
import RischTragerBronstein.Mixed.NKWitTEV
import RischTragerBronstein.Mixed.NKExpDecideTEVR
import RischTragerBronstein.Mixed.NKMultiRRWit

/-!
# Exponential level, single places, residue-free finite poles: decision and antiderivative

`nk_decidesTEVR` and `nk_integrateTEVR` (the antiderivative, `NKExplR`): the constructive
counterparts of `nk_decidesRE`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- **The constructive decision** (residue-free poles, single places, exponential level). -/
def nkTEVRW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (s : List (LC (m + 1)))
    (fp : List (GPoly (LC m))) (D : GPoly (LC m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N)
    (searchPW (fun _ ↦ true) (tevExW Fc ks m a (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s))) [] N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The decision for curves with any coefficients in `Fₘ[t]` over an exponential** (Risch's
mixed case for a single place at infinity and a single place above `t = 0`): for every large
bound, `elM` decides `τ(f)/n`, `searchTEV` decides the exact part, and together they decide `f`. -/
theorem nk_decidesTEVR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N = some b ∧
      searchTEV Fc ks m a (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
        (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) N =
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
  obtain ⟨Tc, Ti, r, dg, C, Ci, dg0, hex⟩ := T.exactTEV_exists m hTr (by omega) hk
    (hTr m (by omega)) (prdeC Fc ks lv m) MSm.rde Pp hsh hsh0 θ hθ
    (nkRest Fc ks m (nkFlR m fp D) q)
  obtain ⟨B0, hB0⟩ := searchTEV_complete Fc ks m a (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
    (nkRest Fc ks m (nkFlR m fp D) q) dg r C Ci dg0 Tc Ti hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨dg', r', C', Ci', dg0', Tc', Ti', hex'⟩ := searchTEV_sound Fc ks m a _ _ _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffTEVR hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp D hsq kc U hcert hfpl dg' r' C' Ci' dg0' Tc' Ti'
    res hex', h0, hiff]

/-- **The integral with residue-free poles and a single place at infinity (exponential level),
decided and computed.** -/
theorem nk_integrateTEVR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTEVRW Fc ks lv m a Pp s fp D N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplR m h1 θ Pp fp D s (fun _ ↦ 1) 0 b.2 := by
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (tevExW_isSome Fc ks m a _ _ _) [] N).trans
        (searchTEV_eq Fc ks m a _ _ _ N).symm)
    _ (T.nk_decidesTEVR hmon hdeg hshF m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp D hsq kc U hcert
      hfpl) _
    fun N w hw h1 ↦ ?_
  obtain ⟨-, hex⟩ := searchPW_src _ _ [] N w hw
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurve_ind m h1 Pp hsh θ hθ
  have hY := T.exactTLEVSW_valid m h1 (by omega) hk (h1 m (by omega)) _
    (T.expSpecV (by omega) h1.of_succ hk _ hrde hom _) hom _ _ _ _ (nkPC Fc ks m Pp) _ θ hP hind
    _ _ [] w.2 hex
  exact T.nk_explicit_coreR m h1 Pp (T.nkShape_spec m h1.of_succ Pp hsh).1 θ [] (fun _ ↦ 1)
    (fun i hi ↦ absurd hi (by simp)) (fun i hi ↦ absurd hi (by simp)) fp D s w.2 hY

end MTower

end Curves.MT
