import RischTragerBronstein.Mixed.NKRam0Cand
import RischTragerBronstein.Mixed.NKSplitCand
import RischTragerBronstein.Mixed.NKRamCand
import RischTragerBronstein.Mixed.NKWronskExists

/-!
# Deciders with independent units, no certificate

`nk_decidesETInf0PW`, `nk_decidesETInf0RPW` (split or ramified at infinity, split above `t = 0`)
and `nk_decidesInfVGPW`, `nk_decidesETInfVGPW`, `nk_decidesInfVRPW`, `nk_decidesETInfVRPW`
(places at infinity only) take S-units certified by `unitsC0`/`unitsC` whose logarithmic
derivatives are linearly independent over the constants of the code field modulo `Fₘ₊₁`; the
independence certificate (`indepWC`, or `indepC` with derivative orders appended to `J`) is no
longer an input — it exists (`indepWC_exists_of_logs`) and the search finds it.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`nk_decidesETInf0P` without a Wronskian certificate**: the units' logarithmic derivatives
need only be independent over the constants modulo `Fₘ₊₁`. -/
theorem nk_decidesETInf0PW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0 m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0P Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, kk, jj, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, hJH, -⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC0_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInf0P hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit βs
    hsp0 θ hθ hgen dθ wθ s hs ⟨Us, Vs, kk, jj, gls, J, D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesETInf0RP` without a Wronskian certificate** (ramified at infinity). -/
theorem nk_decidesETInf0RPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 2 = Pp.length / e + Pp.length ∧
      unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0RP Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, kk, jj, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, hJH, -⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC0_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInf0RP hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram βs
    hsp0 θ hθ hgen dθ wθ s hs ⟨Us, Vs, kk, jj, gls, J, D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesInfVGP` without an independence certificate**: the units' logarithmic
derivatives need only be independent over the constants modulo `Fₘ₊₁`. -/
theorem nk_decidesInfVGPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVGP Fc ks m η (prdeC Fc ks lv m) Pp dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesInfVGP hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit θ hθ
    hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesETInfVGP` without an independence certificate**: the units' logarithmic
derivatives need only be independent over the constants modulo `Fₘ₊₁`. -/
theorem nk_decidesETInfVGPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVGP Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInfVGP hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit hsh0
    θ hθ hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesInfVRP` without an independence certificate**: the units' logarithmic
derivatives need only be independent over the constants modulo `Fₘ₊₁`. -/
theorem nk_decidesInfVRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length / e ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVRP Fc ks m η (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesInfVRP hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram θ hθ
    hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesETInfVRP` without an independence certificate**: the units' logarithmic
derivatives need only be independent over the constants modulo `Fₘ₊₁`. -/
theorem nk_decidesETInfVRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length / e ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVRP Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInfVRP hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram hsh0
    θ hθ hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

end MTower

end Curves.MT
