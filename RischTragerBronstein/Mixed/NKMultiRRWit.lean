import RischTragerBronstein.Mixed.NKMultiRWit
import RischTragerBronstein.Mixed.NKDecidesInfVMRR
import RischTragerBronstein.Mixed.NKDecidesETInfVMRR

/-!
# Several slopes with residue-free poles: units without certificate, and the antiderivative

`…RRPW`, `…RRPM` and `nk_integrateInfVMRRPW`, `nk_integrateETInfVMRRPW`: the variants of
`Mixed/NKMultiRWit` for integrands `∑ bⱼ(t)/D(t) θʲ` with residue-free poles (`resCert`); the
explicit antiderivative `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ` (`NKExplR`, `nk_explicit_coreR`).
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- **The constructive decision** (several slopes, residue-free poles, logarithmic level). -/
def nkInfVMRRW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (D : GPoly (LC m)) (pre : List (CandIVR m))
    (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N)
    (searchPW (ivmCond Fc ks m Pp np dθ wθ s) (ivmExW Fc ks m η (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s))) pre N)

/-- **The constructive decision** (several slopes, residue-free poles, exponential level). -/
def nkETVMRRW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (D : GPoly (LC m)) (pre : List (CandETVR m))
    (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N)
    (searchPW (etvmCond Fc ks m Pp np dθ wθ s) (etvrExW Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s))) pre N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The explicit antiderivative statement** (residue-free poles): `uᵢ ≠ 0` and
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ`. -/
def NKExplR (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp fp : List (GPoly (LC m)))
    (D : GPoly (LC m)) (s : List (LC (m + 1))) (u : ℕ → L) (ng : ℕ) (wt : List ℚ × List (LC (m + 1))) : Prop :=
  (∀ i < ng, u i ≠ 0) ∧
  ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j =
    T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) +
    (∑ k ∈ Finset.range Pp.length, T.ev (m + 1) (wt.2.getD k (MOr Fc ks (m + 1)).zero) * θ ^ k)′ +
    ∑ i ∈ Finset.range ng, ((wt.1.getD i 0 : ℚ) : L) * logDeriv (u i)

/-- **The explicit antiderivative from an exact part and units** (residue-free poles). -/
theorem nk_explicit_coreR (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (hn0 : 0 < Pp.length) (θ : L) (gls : List (GPoly (LC (m + 1)))) (u : ℕ → L)
    (hui : ∀ i < gls.length, u i ≠ 0 ∧ T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (hgl : ∀ i < gls.length, (gls.getD i []).length ≤ Pp.length)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m)) (s : List (LC (m + 1)))
    (wt : List ℚ × List (LC (m + 1)))
    (hY : T.ExW m h1 ((nkPC Fc ks m Pp).length - 1) (fun k ↦ θ ^ k)
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) gls wt) :
    T.NKExplR m h1 θ Pp fp D s u gls.length wt := by
  classical
  unfold ExW at hY
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  refine ⟨fun i hi ↦ (hui i hi).1, ?_⟩
  have hg : ∑ j ∈ Finset.range Pp.length, (∑ i ∈ Finset.range gls.length,
      ((wt.1.getD i 0 : ℚ) : L) * ((M1.sem ((gls.getD i []).getD j O1.zero) : T.F (m + 1)) : L)) *
        θ ^ j =
      ∑ i ∈ Finset.range gls.length, ((wt.1.getD i 0 : ℚ) : L) * logDeriv (u i) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [logDeriv, ← (hui i hi').2, T.evθ_list_le m h1 θ _ Pp.length (hgl i hi'), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [length_nkPC] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRestR m h1 Pp.length hn0] at hY
  have hev : ∀ k, ((M1.sem (wt.2.getD k O1.zero) : T.F (m + 1)) : L) =
      T.ev (m + 1) (wt.2.getD k O1.zero) := fun k ↦ T.sem_MP (m + 1) h1 _
  simp only [hev] at hY
  rw [hY]
  ring

/-- **`nk_decidesInfVMR` without an independence certificate.** -/
theorem nk_decidesInfVMRRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, Dw, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesInfVMRR hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ hθ
    hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ Dw, H, hk1, hU, hJH⟩ fp D hsq kc U hcert hfpl pre

/-- **`nk_decidesETInfVMR` without an independence certificate.** -/
theorem nk_decidesETInfVMRRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N = some b ∧
      searchETVMP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, Dw, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInfVMRR hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms hsh0
    θ hθ hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ Dw, H, hk1, hU, hJH⟩ fp D hsq kc U hcert hfpl pre

/-- **`nk_decidesInfVMRPW` with multiplicatively independent units.** -/
theorem nk_decidesInfVMRRPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
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
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesInfVMRRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ hθ
    hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩
    fp D hsq kc U hcert hfpl pre

/-- **`nk_decidesETInfVMRPW` with multiplicatively independent units.** -/
theorem nk_decidesETInfVMRRPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) N = some b ∧
      searchETVMP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesETInfVMRRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms hsh0
    θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩
    fp D hsq kc U hcert hfpl pre

/-- **The integral with several slopes at infinity (logarithmic level), decided and computed.** -/
theorem nk_integrateInfVMRRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkInfVMRRW Fc ks lv m η Pp (nPlacesR segs) dθ wθ s fp D pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplR m h1 θ Pp fp D s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (ivmExW_isSome Fc ks m η _ Pp _) pre N).trans
        (searchIVMP_eq Fc ks m η _ Pp (nPlacesR segs) dθ wθ s _ pre N).symm)
    _ (T.nk_decidesInfVMRRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms
      θ hθ hgen dθ wθ s hs hunits fp D hsq kc U hcert hfpl pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [ivmCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hY := T.exactTLVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ MSm.rde _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_coreR m h1 Pp hn0 θ _ _
    (T.units_logs m h1 θ Pp hP _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC_spec hcd.1.2 i hi).2.2.1) fp D s w.2 hY

/-- **The integral with several slopes at infinity (exponential level), decided and computed.** -/
theorem nk_integrateETInfVMRRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkETVMRRW Fc ks lv m a Pp (nPlacesR segs) dθ wθ s fp D pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExplR m h1 θ Pp fp D s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (etvrExW_isSome Fc ks m a _ Pp _) pre N).trans
        (searchETVMP_eq Fc ks m a _ Pp (nPlacesR segs) dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInfVMRRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms
      hsh0 θ hθ hgen dθ wθ s hs hunits fp D hsq kc U hcert hfpl pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [etvmCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_coreR m h1 Pp hn0 θ _ _
    (T.units_logs m h1 θ Pp hP _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC_spec hcd.1.2 i hi).2.2.1) fp D s w.2 hY

end MTower

end Curves.MT
