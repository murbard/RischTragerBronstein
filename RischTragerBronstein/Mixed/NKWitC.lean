import RischTragerBronstein.Mixed.NKWitTVR
import RischTragerBronstein.Mixed.NKWitTEVR
import RischTragerBronstein.Mixed.NKMultiRRWit
import RischTragerBronstein.Mixed.NKLogCert

/-!
# Non-zero residues with a logarithm certificate: the antiderivative

`integrate_of_logs`: a decided-and-computed statement for `g` transfers to `f = g + ∑ cⱼ uⱼ′/uⱼ`
(`cⱼ ∈ ℚ`, `uⱼ ≠ 0`): `∫ f` is elementary iff `∫ g` is, and an antiderivative of `f` is one of
`g` plus `∑ cⱼ log uⱼ`. Instances: `nk_integrateTVC`, `nk_integrateTEVC` (a single place at
infinity), `nk_integrateInfVMRC`, `nk_integrateETInfVMRC` (several slopes), with the certificate
`logCert` (`f − g − ∑ cⱼ uⱼ′/uⱼ ≡ 0 mod P`); the constructive counterparts of `nk_iffC`.
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

/-- **Transfer along a logarithmic sum**. -/
theorem integrate_of_logs {L : Type u} [Field L] [Differential L] [CharZero L] {X : Type*}
    (W : ℕ → Option (Option X)) (f g : L) (n : ℕ) (c : ℕ → ℚ) (u : ℕ → L) (hu : ∀ j < n, u j ≠ 0)
    (hfg : f = g + ∑ j ∈ Finset.range n, ((c j : ℚ) : L) * ((u j)′ / u j)) (R : Option X → Prop)
    (hW : ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, W N = some o ∧ (HasElementaryIntegral g ↔ o.isSome) ∧ R o) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, W N = some o ∧ (HasElementaryIntegral f ↔ o.isSome) ∧ R o := by
  obtain ⟨N₀, hN₀⟩ := hW
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨o, ho, hiff, hR⟩ := hN₀ N hN
  refine ⟨o, ho, ?_, hR⟩
  have hL := hasElementaryIntegralIn_logs n c u hu
  rw [← hiff, hfg]
  constructor
  · intro h
    have := h.sub_in hL
    simpa using this
  · intro h
    exact h.add_in hL

set_option maxHeartbeats 4000000 in
/-- **With a logarithm certificate** (`logCert`: `f = g + ∑ cⱼ uⱼ′/uⱼ`, `g` residue-free): the
procedure of `nk_integrateTVR` on `g` decides `f`, and its witness with the logarithms of the certificate is an
antiderivative of `f`.  **The integral with a single place at infinity (logarithmic level), decided and computed**:
an elementary answer carries an antiderivative of the trace part and an exact part `Y` with
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′`. -/
theorem nk_integrateTVC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ)
    (hlog : logCert Fc ks m (nkPC Fc ks m Pp) fl (nkFlR m fp D) us cs = true) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTVRW Fc ks lv m η Pp s fp D N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
          (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplR m h1 θ Pp fp D s (fun _ ↦ 1) 0 b.2 := by
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
  exact MTower.integrate_of_logs _ _ _ _ _ _ hu0 hfg _ (T.nk_integrateTVR hmon hdeg hshF m hn hc hk Pp hsh θ hθ hgen s hs fp D hsq kc U hcert hfpl)


set_option maxHeartbeats 4000000 in
/-- **With a logarithm certificate** (`logCert`: `f = g + ∑ cⱼ uⱼ′/uⱼ`, `g` residue-free): the
procedure of `nk_integrateTEVR` on `g` decides `f`, and its witness with the logarithms of the certificate is an
antiderivative of `f`.  **The integral with residue-free poles and a single place at infinity (exponential level),
decided and computed.** -/
theorem nk_integrateTEVC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ)
    (hlog : logCert Fc ks m (nkPC Fc ks m Pp) fl (nkFlR m fp D) us cs = true) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTEVRW Fc ks lv m a Pp s fp D N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
          (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplR m h1 θ Pp fp D s (fun _ ↦ 1) 0 b.2 := by
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
  exact MTower.integrate_of_logs _ _ _ _ _ _ hu0 hfg _ (T.nk_integrateTEVR hmon hdeg hshF m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp D hsq kc U hcert hfpl)


set_option maxHeartbeats 4000000 in
/-- **With a logarithm certificate** (`logCert`: `f = g + ∑ cⱼ uⱼ′/uⱼ`, `g` residue-free): the
procedure of `nk_integrateInfVMRRPW` on `g` decides `f`, and its witness with the logarithms of the certificate is an
antiderivative of `f`.  **The integral with several slopes at infinity (logarithmic level), decided and computed.** -/
theorem nk_integrateInfVMRC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ)
    (hlog : logCert Fc ks m (nkPC Fc ks m Pp) fl (nkFlR m fp D) us cs = true)
    (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkInfVMRRW Fc ks lv m η Pp (nPlacesR segs) dθ wθ s fp D pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
          (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplR m h1 θ Pp fp D s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
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
  exact MTower.integrate_of_logs _ _ _ _ _ _ hu0 hfg _ (T.nk_integrateInfVMRRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ hθ hgen dθ wθ s hs hunits fp D hsq kc U hcert hfpl pre)


set_option maxHeartbeats 4000000 in
/-- **With a logarithm certificate** (`logCert`: `f = g + ∑ cⱼ uⱼ′/uⱼ`, `g` residue-free): the
procedure of `nk_integrateETInfVMRRPW` on `g` decides `f`, and its witness with the logarithms of the certificate is an
antiderivative of `f`.  **The integral with several slopes at infinity (exponential level), decided and computed.** -/
theorem nk_integrateETInfVMRC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ)
    (hlog : logCert Fc ks m (nkPC Fc ks m Pp) fl (nkFlR m fp D) us cs = true)
    (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkETVMRRW Fc ks lv m a Pp (nPlacesR segs) dθ wθ s fp D pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
          (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplR m h1 θ Pp fp D s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
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
  exact MTower.integrate_of_logs _ _ _ _ _ _ hu0 hfg _ (T.nk_integrateETInfVMRRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms hsh0 θ hθ hgen dθ wθ s hs hunits fp D hsq kc U hcert hfpl pre)

end MTower

end Curves.MT
