import RischTragerBronstein.Mixed.NKMultiRRWit
import RischTragerBronstein.Mixed.NKLogCert

/-!
# Several slopes at infinity with non-zero residues, through a logarithm certificate

`nk_decidesInfVMRC`, `nk_decidesETInfVMRC`: for `f = ∑ fⱼ θʲ` (`fⱼ ∈ Fₘ₊₁`, any poles) and a
certificate `(uⱼ, cⱼ)` (`logCert`, `cⱼ ∈ ℚ`) such that `g = f − ∑ cⱼ uⱼ′/uⱼ = ∑ bⱼ/D θʲ` has
residue-free poles (`resCert`): `∑ cⱼ log uⱼ` is elementary, so `f` has an elementary integral iff
`g` has one, which `nk_decidesInfVMRR` (`nk_decidesETInfVMRR`) decides. The existence of the
certificate is the torsion question for the residue divisors (as for the units at infinity).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **Several slopes, non-zero residues with a logarithm certificate** (logarithmic level). -/
theorem nk_decidesInfVMRC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ)
    (hlog : logCert Fc ks m (nkPC Fc ks m Pp) fl (nkFlR m fp D) us cs = true)
    (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N = some b ∧
      searchIVMP Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
          (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  obtain ⟨hu0, hfg⟩ := T.logCert_sound m hTr θ _ hP _ _ us cs hlog
  have hlen : (nkFlR m fp D).length = fp.length := List.length_map _
  have hev : T.evθ m hTr θ (nkFlR m fp D) =
      ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j := by
    rw [T.evθ_list, hlen, hfpl]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [T.sem_nkFlR m hTr fp D j]
  rw [T.evθ_list, hfl, hev] at hfg
  have hL := hasElementaryIntegralIn_logs us.length (fun j ↦ cs.getD j 0)
    (fun j ↦ T.evθ m hTr θ (us.getD j [])) hu0
  obtain ⟨N₀, hN₀⟩ := T.nk_decidesInfVMRR hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck
    segs hms θ hθ hgen dθ wθ s hs hunits fp D hsq kc U hcert hfpl pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, hb, hres, hiff⟩ := hN₀ N hN
  refine ⟨b, res, hb, hres, ?_⟩
  rw [← hiff, hfg]
  constructor
  · intro h
    have := h.sub_in hL
    simpa using this
  · intro h
    exact h.add_in hL

set_option maxHeartbeats 4000000 in
/-- **Several slopes, non-zero residues with a logarithm certificate** (exponential level). -/
theorem nk_decidesETInfVMRC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = nPlacesR segs ∧
      unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧ indepC Fc ks m gls J H = true)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ)
    (hlog : logCert Fc ks m (nkPC Fc ks m Pp) fl (nkFlR m fp D) us cs = true)
    (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N = some b ∧
      searchETVMP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
          (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  obtain ⟨hu0, hfg⟩ := T.logCert_sound m hTr θ _ hP _ _ us cs hlog
  have hlen : (nkFlR m fp D).length = fp.length := List.length_map _
  have hev : T.evθ m hTr θ (nkFlR m fp D) =
      ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j := by
    rw [T.evθ_list, hlen, hfpl]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [T.sem_nkFlR m hTr fp D j]
  rw [T.evθ_list, hfl, hev] at hfg
  have hL := hasElementaryIntegralIn_logs us.length (fun j ↦ cs.getD j 0)
    (fun j ↦ T.evθ m hTr θ (us.getD j [])) hu0
  obtain ⟨N₀, hN₀⟩ := T.nk_decidesETInfVMRR hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck
    segs hms hsh0 θ hθ hgen dθ wθ s hs hunits fp D hsq kc U hcert hfpl pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, hb, hres, hiff⟩ := hN₀ N hN
  refine ⟨b, res, hb, hres, ?_⟩
  rw [← hiff, hfg]
  constructor
  · intro h
    have := h.sub_in hL
    simpa using this
  · intro h
    exact h.add_in hL

end MTower

end Curves.MT
