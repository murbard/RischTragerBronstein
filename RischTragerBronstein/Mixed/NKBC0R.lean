import RischTragerBronstein.Mixed.NKBC
import RischTragerBronstein.Mixed.NKRam0Cand

/-!
# A ramified place at infinity and a non-rational fibre above `0`, through a base change

`nk_decidesETInf0RP_bc`: `nk_decidesETInf0RP` over a new base curve (`bc_decides`), for fibres above
`t = 0` whose roots are algebraic over `F₀`. Example (`Mixed/NKBC0RExamples`): `√(x eˣ + x)`.
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
/-- **`nk_decidesETInf0RP` over a new base curve** (`bc_decides`). -/
theorem nk_decidesETInf0RP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
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
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      (elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
        (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchET0RP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m a) (prdeC Fc' (tauK Fc' Yc ks) lv' m)
        (Pp.map (·.map (tauC Fc' Yc m))) e dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
            (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  refine T.bc_decides Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen _ ?_
  intro Cc' L' _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen'
  have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
      ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by
    rw [List.length_map]; exact hθ'
  have hunits' := hunits
  rw [← List.length_map (f := (·.map (tauC Fc' Yc m))) (as := Pp)] at hunits'
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesETInf0RP hmon' hdeg' hshF' m hTn hc' hk'
    (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck e sR γs hram βs hsp0 θ' hθ'' hgen'
    dθ wθ s hs hunits' (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, h1, h2, h3⟩ := hN₀ N hN
  rw [List.length_map] at h1 h2 h3
  exact ⟨b, res, ⟨h1, h2⟩, h3⟩

end MTower

end Curves.MT
