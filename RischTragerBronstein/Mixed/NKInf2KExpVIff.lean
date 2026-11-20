import RischTragerBronstein.Mixed.NKInf2KExpV

/-! `nk_iffET2KV`: the decision assembled from `nk_necessaryET2KV` and `nk_sufficientETInfVGD`
(without units). -/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

variable {Fc : BPoly ℚ} [Fact (Irreducible (toPoly (fKc Fc)))] {ks : (m : ℕ) → KindC m}
  {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The decision with two places at infinity** (exponential level, non-constant curve, gauge and
rescaling at infinity, no units). -/
theorem nk_iffET2KV (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (hn0 : 0 < Pp.length) (hsh0 : nkShape0 Fc ks m Pp = true)
    (ha0K : (toB (trCurveK Fc m Pp)).coeff 0 ≠ 0) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB (trCurveK Fc m Pp) 0))
    (hGm : (toB (invB (shiftB (trCurveK Fc m Pp) 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB (trCurveK Fc m Pp) 0) k0 M)).natDegree = Pp.length)
    (hcert : TwoPlaceCertK (KF Fc m) (invB (shiftB (trCurveK Fc m Pp) 0) k0 M)) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m))
    (hres : exactTLEVG Fc ks m a (prdeC Fc ks lv m) dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) [] = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  refine ⟨T.nk_necessaryET2KV hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck hn0 hsh0 ha0K k0 M hinv
    hGm hGn hcert θ hθ hgen s hs fp Tc Ti res dg Cg Cgi r C Ci dg0 hres, fun h ↦ ?_⟩
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  exact T.nk_sufficientETInfVGD m hTr (by omega) hk (hTr m (by omega)) (prdeC Fc ks lv m) hrde hom
    dg Cg Cgi r C Ci dg0 Pp hn0 θ hθ (T.nkCurveE_ind m hTr Pp qE csE sE tE s2E t2E hck θ hθ) [] []
    [] [] [] [] [] [] [] s (by simp [unitsCD]) fp Tc Ti res hres h.1 h.2

end MTower

end Curves.MT
