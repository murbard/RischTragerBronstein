import RischTragerBronstein.Mixed.NKBCW
import RischTragerBronstein.Mixed.NKBC0R
import RischTragerBronstein.Mixed.NKIndepPW0
import RischTragerBronstein.Mixed.NKWitET

/-!
# Changing the base curve with the antiderivative, exponential level

Constructive versions (via `bc_integrates`) of `nk_decidesETInfVGP_bc`, `nk_decidesETInfVRP_bc`,
`nk_decidesETInf0P_bc` and `nk_decidesETInf0RP_bc`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 8000000 in
/-- **`nk_integrateETInfVGPW` over a new base curve** (`bc_integrates`). -/
theorem nk_integrateETInfVGP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) sp γs = true)
    (hsh0 : nkShape0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVG m)) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L') (T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L'),
      (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o,
        nkETVGW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
          o.isSome) ∧
        ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
          ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 (algebraMap L L' θ) (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
            (fun i ↦ T'.evθ m h1 (algebraMap L L' θ) (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.getD i []))) b.1.2.2.1.length b.2 := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  obtain ⟨Us, Vs, gls, J, H, hk1, hU, hJH⟩ := hunits
  have hn0 : 0 < (Pp.map (·.map (tauC Fc' Yc m))).length := by
    rw [List.length_map]; exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hk1
  have key := T.bc_integrates Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (nkETVGW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' θ' o ↦ ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
            ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 θ' (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
              (fun i ↦ T'.evθ m h1 θ' (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.getD i []))) b.1.2.2.1.length b.2)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen' ↦ by
      have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
          ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
          T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by
        rw [List.length_map]; exact hθ'
      have hli := T'.hli_of_indepC m _ hn0 θ' hθ''
        (fun h1 ↦ T'.nkCurveE_ind m h1 _ qE csE sE tE s2E t2E hck θ' hθ'') Us Vs gls dθ wθ s hs hU J H hJH
      obtain ⟨N₀, hN₀⟩ := T'.nk_integrateETInfVGPW hmon' hdeg' hshF' m hTn hc' hk'
        _ qE csE sE tE s2E t2E hck
        sp γs hsplit hsh0 θ' hθ'' hgen' dθ wθ s hs
        ⟨Us, Vs, gls, by rw [List.length_map]; exact hk1, hU, hli⟩ (fp.map (·.map (tauC Fc' Yc m))) pre
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨o, h1, h2, h3⟩ := hN₀ N hN
      rw [List.length_map] at h2
      exact ⟨o, h1, h2, h3⟩)
  exact key

set_option maxHeartbeats 8000000 in
/-- **`nk_integrateETInfVRPW` over a new base curve** (`bc_integrates`). -/
theorem nk_integrateETInfVRP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) e sR γs = true)
    (hsh0 : nkShape0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length / e ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L') (T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L'),
      (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o,
        nkETVRW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) e dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
          o.isSome) ∧
        ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
          ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 (algebraMap L L' θ) (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
            (fun i ↦ T'.evθ m h1 (algebraMap L L' θ) (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  obtain ⟨Us, Vs, gls, J, H, hk1, hU, hJH⟩ := hunits
  have hn0 : 0 < (Pp.map (·.map (tauC Fc' Yc m))).length := by
    rw [List.length_map]; exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hk1
  have key := T.bc_integrates Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (nkETVRW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) e dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' θ' o ↦ ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
            ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 θ' (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
              (fun i ↦ T'.evθ m h1 θ' (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen' ↦ by
      have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
          ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
          T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by
        rw [List.length_map]; exact hθ'
      have hli := T'.hli_of_indepC m _ hn0 θ' hθ''
        (fun h1 ↦ T'.nkCurveE_ind m h1 _ qE csE sE tE s2E t2E hck θ' hθ'') Us Vs gls dθ wθ s hs hU J H hJH
      obtain ⟨N₀, hN₀⟩ := T'.nk_integrateETInfVRPW hmon' hdeg' hshF' m hTn hc' hk'
        _ qE csE sE tE s2E t2E hck
        e sR γs hram hsh0 θ' hθ'' hgen' dθ wθ s hs
        ⟨Us, Vs, gls, by rw [List.length_map]; exact hk1, hU, hli⟩ (fp.map (·.map (tauC Fc' Yc m))) pre
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨o, h1, h2, h3⟩ := hN₀ N hN
      rw [List.length_map] at h2
      exact ⟨o, h1, h2, h3⟩)
  exact key

set_option maxHeartbeats 8000000 in
/-- **`nk_integrateETInf0PW` over a new base curve** (`bc_integrates`). -/
theorem nk_integrateETInf0P_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E =
      true)
    (sp : ℕ) (γs : List (LC m))
    (hsplit : splitShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) sp γs = true)
    (βs : List (LC m))
    (hsp0 : split0C Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ) (H : List (List (LC (m + 1)))),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs kk jj
        ((MO Fc' (tauK Fc' Yc ks) m).deriv (tauC Fc' Yc m a)) gls dθ wθ s = true ∧
      indepWC Fc' (tauK Fc' Yc ks) m gls J D H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandET0 m)) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L') (T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L'),
      (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o,
        nkET0W Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
          o.isSome) ∧
        ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
          ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 (algebraMap L L' θ) (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
            (fun i ↦ T'.evθ m h1 (algebraMap L L' θ) (nkFl Fc' (tauK Fc' Yc ks) m (b.1.2.2.2.1.getD i [])) *
              T'.ts m ^ (-((b.1.2.1.getD i 0 : ℕ) : ℤ))) b.1.2.2.2.2.2.1.length b.2 := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by
    unfold tauK; rw [hk]
  obtain ⟨Us, Vs, kk, jj, gls, J, D, H, hk1, hU, hJH⟩ := hunits
  have hn0 : 0 < (Pp.map (·.map (tauC Fc' Yc m))).length := by
    rw [List.length_map]; exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hk1
  have key := T.bc_integrates Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (nkET0W Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' θ' o ↦ ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
            ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 θ' (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
              (fun i ↦ T'.evθ m h1 θ' (nkFl Fc' (tauK Fc' Yc ks) m (b.1.2.2.2.1.getD i [])) *
                T'.ts m ^ (-((b.1.2.1.getD i 0 : ℕ) : ℤ))) b.1.2.2.2.2.2.1.length b.2)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen' ↦ by
      have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
          ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
          T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by
        rw [List.length_map]; exact hθ'
      have hli := T'.hli_of_indepWC0 m (by omega) hk' _ hn0 θ' hθ''
        (fun h1 ↦ T'.nkCurveE_ind m h1 _ qE csE sE tE s2E t2E hck θ' hθ'') Us Vs kk jj gls dθ wθ s hs hU J D H hJH
      obtain ⟨N₀, hN₀⟩ := T'.nk_integrateETInf0PW hmon' hdeg' hshF' m hTn hc' hk'
        _ qE csE sE tE s2E t2E hck sp γs hsplit βs hsp0 θ' hθ'' hgen' dθ wθ s hs
        ⟨Us, Vs, kk, jj, gls, by rw [List.length_map]; exact hk1, hU, hli⟩ (fp.map (·.map (tauC Fc' Yc m))) pre
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨o, h1, h2, h3⟩ := hN₀ N hN
      rw [List.length_map] at h2
      exact ⟨o, h1, h2, h3⟩)
  exact key

set_option maxHeartbeats 8000000 in
/-- **`nk_integrateETInf0RPW` over a new base curve** (`bc_integrates`). -/
theorem nk_integrateETInf0RP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E =
      true)
    (e sR : ℕ) (γs : List (LC m))
    (hram : ramShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) e sR γs = true)
    (βs : List (LC m))
    (hsp0 : split0C Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ) (H : List (List (LC (m + 1)))),
      gls.length + 2 = Pp.length / e + Pp.length ∧
      unitsC0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs kk jj
        ((MO Fc' (tauK Fc' Yc ks) m).deriv (tauC Fc' Yc m a)) gls dθ wθ s = true ∧
      indepWC Fc' (tauK Fc' Yc ks) m gls J D H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandET0R m)) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L') (T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L'),
      (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o,
        nkET0RW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) e dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
          o.isSome) ∧
        ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
          ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 (algebraMap L L' θ) (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
            (fun i ↦ T'.evθ m h1 (algebraMap L L' θ) (nkFl Fc' (tauK Fc' Yc ks) m (b.1.2.2.2.1.1.getD i [])) *
              T'.ts m ^ (-((b.1.2.1.getD i 0 : ℕ) : ℤ))) b.1.2.2.2.1.2.2.1.length b.2 := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  obtain ⟨Us, Vs, kk, jj, gls, J, D, H, hk1, hU, hJH⟩ := hunits
  have hn0 : 0 < (Pp.map (·.map (tauC Fc' Yc m))).length := by
    rw [List.length_map]; exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hk1
  have key := T.bc_integrates Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (nkET0RW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m))) e dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' θ' o ↦ ∀ w b, o = some (w, b) → T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
            ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 θ' (Pp.map (·.map (tauC Fc' Yc m))) (fp.map (·.map (tauC Fc' Yc m))) s
              (fun i ↦ T'.evθ m h1 θ' (nkFl Fc' (tauK Fc' Yc ks) m (b.1.2.2.2.1.1.getD i [])) *
                T'.ts m ^ (-((b.1.2.1.getD i 0 : ℕ) : ℤ))) b.1.2.2.2.1.2.2.1.length b.2)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen' ↦ by
      have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
          ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
          T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by
        rw [List.length_map]; exact hθ'
      have hli := T'.hli_of_indepWC0 m (by omega) hk' _ hn0 θ' hθ''
        (fun h1 ↦ T'.nkCurveE_ind m h1 _ qE csE sE tE s2E t2E hck θ' hθ'') Us Vs kk jj gls dθ wθ s hs hU J D H hJH
      obtain ⟨N₀, hN₀⟩ := T'.nk_integrateETInf0RPW hmon' hdeg' hshF' m hTn hc' hk'
        _ qE csE sE tE s2E t2E hck e sR γs hram βs hsp0 θ' hθ'' hgen' dθ wθ s hs
        ⟨Us, Vs, kk, jj, gls, by rw [List.length_map]; exact hk1, hU, hli⟩ (fp.map (·.map (tauC Fc' Yc m))) pre
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨o, h1, h2, h3⟩ := hN₀ N hN
      rw [List.length_map] at h2
      exact ⟨o, h1, h2, h3⟩)
  exact key

end MTower

end Curves.MT

