import RischTragerBronstein.Mixed.NKBCW

/-!
# Changing the base curve with the antiderivative, exponential level

`nk_integrateETInfVMR_bc`: the exponential analogue of `nk_integrateInfVMR_bc`, via `bc_integrates`.
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
/-- **`nk_integrateETInfVMRPW` over a new base curve**: several slopes at infinity whose places
become rational after the change of base curve; the antiderivative lives in a tower `T'` over the
new base, in an algebraic extension of `L`. -/
theorem nk_integrateETInfVMR_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
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
    (segs : List (SegRC m))
    (hms : multiShapeRC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) segs = true)
    (hsh0 : nkShape0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
    (H : List (List (LC (m + 1)))) (hk1 : gls.length + 1 = nPlacesR segs)
    (hU : unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true)
    (hJH : indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L') (T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L'),
      (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o,
        nkETVMRW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m)))
          (nPlacesR segs) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
          o.isSome) ∧
        ∀ w b, o = some (w, b) →
          T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length
            (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
          ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 (algebraMap L L' θ) (Pp.map (·.map (tauC Fc' Yc m)))
            (fp.map (·.map (tauC Fc' Yc m))) s
            (fun i ↦ T'.evθ m h1 (algebraMap L L' θ)
              (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  have hn0 : 0 < (Pp.map (·.map (tauC Fc' Yc m))).length := by
    unfold multiShapeRC at hms
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    exact hms.1.1.1.1
  have key := T.bc_integrates Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (nkETVMRW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m a) (Pp.map (·.map (tauC Fc' Yc m)))
      (nPlacesR segs) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' θ' o ↦ ∀ w b, o = some (w, b) →
      T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length
        (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
      ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 θ' (Pp.map (·.map (tauC Fc' Yc m)))
        (fp.map (·.map (tauC Fc' Yc m))) s
        (fun i ↦ T'.evθ m h1 θ' (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.1.getD i [])))
        b.1.1.2.2.1.length b.2)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen' ↦ by
      have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
          ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
          T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by
        rw [List.length_map]; exact hθ'
      have hli := T'.hli_of_indepC m _ hn0 θ' hθ''
        (fun h1 ↦ T'.nkCurveE_ind m h1 _ qE csE sE tE s2E t2E hck θ' hθ'') Us Vs gls dθ wθ s hs hU J H hJH
      obtain ⟨N₀, hN₀⟩ := T'.nk_integrateETInfVMRPW hmon' hdeg' hshF' m hTn hc' hk'
        _ qE csE sE tE s2E t2E hck segs hms hsh0 θ' hθ'' hgen' dθ wθ s hs
        ⟨Us, Vs, gls, hk1, hU, hli⟩ (fp.map (·.map (tauC Fc' Yc m))) pre
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨o, h1, h2, h3⟩ := hN₀ N hN
      rw [List.length_map] at h2
      exact ⟨o, h1, h2, h3⟩)
  exact key

end MTower

end Curves.MT

