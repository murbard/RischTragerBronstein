import RischTragerBronstein.Mixed.NKBC
import RischTragerBronstein.Mixed.NKMultiRWit

/-!
# Several slopes at infinity with non-rational places, through a change of the base curve

`nk_decidesInfVMR_bc`, `nk_decidesETInfVMR_bc`: the several-slopes deciders over a new base curve
(`bc_decides`): places at infinity whose residue fields are `Fₘ(β)` with `β` algebraic over the base
field `F₀` (e.g. `θ ≈ ±√x t`) become rational over the new base (`w² = x`). Example
(`Mixed/NKBCMRExamples`): `θ² = x log² x + 1`.
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

set_option maxHeartbeats 40000000 in
/-- **`nk_decidesInfVMR` over a new base curve (several slopes at infinity)** (`bc_decides`). -/
theorem nk_decidesInfVMR_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = nPlacesR segs ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      (elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchIVMP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m η) (prdeC Fc' (tauK Fc' Yc ks) lv' m) (Pp.map (·.map (tauC Fc' Yc m))) (nPlacesR segs) dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  have hk' : tauK Fc' Yc ks m = .prim (tauC Fc' Yc m η) := by unfold tauK; rw [hk]
  refine T.bc_decides Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (fun N b res ↦ elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
      (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchIVMP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m η) (prdeC Fc' (tauK Fc' Yc ks) lv' m)
        (Pp.map (·.map (tauC Fc' Yc m))) (nPlacesR segs) dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
            (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ?_
  intro Cc' L' _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen'
  have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length + ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by rw [List.length_map]; exact hθ'
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesInfVMR hmon' hdeg' hshF' m hTn hc' hk' (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck
    segs hms θ' hθ'' hgen' dθ wθ s hs hunits (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, h1, h2, h3⟩ := hN₀ N hN
  rw [List.length_map] at h1 h2 h3
  exact ⟨b, res, ⟨h1, h2⟩, h3⟩

set_option maxHeartbeats 40000000 in
/-- **`nk_decidesETInfVMR` over a new base curve (several slopes at infinity)** (`bc_decides`). -/
theorem nk_decidesETInfVMR_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
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
    (segs : List (SegRC m)) (hms : multiShapeRC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) segs = true)
    (hsh0 : nkShape0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = nPlacesR segs ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      (elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchETVMP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m a) (prdeC Fc' (tauK Fc' Yc ks) lv' m) (Pp.map (·.map (tauC Fc' Yc m))) (nPlacesR segs) dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  refine T.bc_decides Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (fun N b res ↦ elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
      (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchETVMP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m a) (prdeC Fc' (tauK Fc' Yc ks) lv' m)
        (Pp.map (·.map (tauC Fc' Yc m))) (nPlacesR segs) dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
            (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ?_
  intro Cc' L' _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen'
  have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length + ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by rw [List.length_map]; exact hθ'
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesETInfVMR hmon' hdeg' hshF' m hTn hc' hk' (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck
    segs hms hsh0 θ' hθ'' hgen' dθ wθ s hs hunits (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, h1, h2, h3⟩ := hN₀ N hN
  rw [List.length_map] at h1 h2 h3
  exact ⟨b, res, ⟨h1, h2⟩, h3⟩

end MTower

end Curves.MT
