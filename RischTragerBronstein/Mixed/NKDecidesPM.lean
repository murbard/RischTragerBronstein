import RischTragerBronstein.Mixed.NKMultLin

/-!
# The decisions with several places, assuming multiplicatively independent units

`nk_decides…PM`: the decisions `nk_decides…PW` with the natural hypothesis on the units — `r − 1`
S-units certified by `unitsC` (`unitsC0` above `t = 0`) that are multiplicatively independent
modulo the constants — instead of the linear independence of their logarithmic derivatives,
which follows (`hli_of_mult`, `hli_of_mult0`: the constants among the code values are rational,
`codeVals_const_rat`, and a rational relation has zero trace).
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

/-- **`nk_decidesInfVGPW` with multiplicatively independent units.** -/
theorem nk_decidesInfVGPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVGP Fc ks m η (prdeC Fc ks lv m) Pp dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 : 0 < Pp.length := by omega
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesInfVGPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩ fp pre

/-- **`nk_decidesETInfVGPW` with multiplicatively independent units.** -/
theorem nk_decidesETInfVGPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVGP Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 : 0 < Pp.length := by omega
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesETInfVGPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit hsh0 θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩ fp pre

/-- **`nk_decidesInfVRPW` with multiplicatively independent units.** -/
theorem nk_decidesInfVRPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVRP Fc ks m η (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 : 0 < Pp.length := by
    rcases Nat.eq_zero_or_pos Pp.length with h0 | h0
    · rw [h0, Nat.zero_div] at hk1; omega
    · exact h0
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesInfVRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩ fp pre

/-- **`nk_decidesETInfVRPW` with multiplicatively independent units.** -/
theorem nk_decidesETInfVRPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVRP Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 : 0 < Pp.length := by
    rcases Nat.eq_zero_or_pos Pp.length with h0 | h0
    · rw [h0, Nat.zero_div] at hk1; omega
    · exact h0
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesETInfVRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram hsh0 θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩ fp pre

/-- **`nk_decidesETInf0PW` with multiplicatively independent units.** -/
theorem nk_decidesETInf0PM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) * T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ))) ^ a i =
          algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0 m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0P Fc ks m a (prdeC Fc ks lv m) Pp dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, kk, jj, gls, hk1, hU, hmult⟩ := hunits
  have hn0 : 0 < Pp.length := by omega
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesETInf0PW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp γs hsplit βs hsp0 θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, kk, jj, gls, hk1, hU, fun h1 ↦ T.hli_of_mult0 m h1 (by omega) hk (h1 m (by omega)) θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs kk jj gls dθ wθ s hs hU (hmult h1)⟩ fp pre

/-- **`nk_decidesETInf0RPW` with multiplicatively independent units.** -/
theorem nk_decidesETInf0RPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) * T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ))) ^ a i =
          algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchET0RP Fc ks m a (prdeC Fc ks lv m) Pp e dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true)   := by
  obtain ⟨Us, Vs, kk, jj, gls, hk1, hU, hmult⟩ := hunits
  have hn0 : 0 < Pp.length := by
    rcases Nat.eq_zero_or_pos Pp.length with h0 | h0
    · rw [h0, Nat.zero_div] at hk1; omega
    · exact h0
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesETInf0RPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck e sR γs hram βs hsp0 θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, kk, jj, gls, hk1, hU, fun h1 ↦ T.hli_of_mult0 m h1 (by omega) hk (h1 m (by omega)) θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs kk jj gls dθ wθ s hs hU (hmult h1)⟩ fp pre

end MTower

end Curves.MT
