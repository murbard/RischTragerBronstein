import RischTragerBronstein.Mixed.NKInfRLog
import RischTragerBronstein.Mixed.NKUnitsInfLog
import RischTragerBronstein.Mixed.NKEisGeo
import RischTragerBronstein.Mixed.NKExactTLVG
import RischTragerBronstein.Mixed.NKInfRV
import RischTragerBronstein.Mixed.NKResCodes

/-!
# Split places at infinity with zero residues: no units needed

`nk_necessaryInfVG0`: if the zero-residue certificate `splitResCk` passes, an elementary integrand
has no logarithmic part, so the exact-part test `exactTLVG` without units (`gls = []`) succeeds.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`⇒` with zero residues at the split places at infinity (no units).** -/
theorem nk_necessaryInfVG0 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true) (θ : L)
    (hn0 : 0 < Pp.length) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (sR MR : ℕ) (γs : List (LC m)) (Θs : List (GPoly (LC m)))
    (hres0 : splitResCk Fc ks lv m sR MR Pp γs Θs fp = true)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ)
    (hres : exactTLVG Fc ks m η (prdeC Fc ks lv m) dg C Ci r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) [] = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  classical
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFl Fc ks m fp) s with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have MSEm := TE.mspecs hmon hdeg lv m (by omega) hcm
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  -- the curve over `C₁ = Fₘ` of the lifted tower
  set S₁ := TE.nkCurveE m hTE Pp qE csE sE tE s2E t2E hck (ψ θ) hθE with hS₁
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  set η₁ : TE.F m := TE.val m η with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁) := by
    rw [aeval_C]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m),
      α′ ≠ ((Polynomial.C η₁).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α ↦ by
      rw [Polynomial.map_C, eval_C]
      exact not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd m (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the integrand is a polynomial in `x, y`
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_pow, hPE]
  set Q : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQ
  have hQv : S₁.evXY Q = ψ f := by
    rw [hψf, CurveData.evXY, hQ, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C,
      eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfT : ψ f ∈ T₁ := hLT f
  have hfQ : (⟨ψ f, hfT⟩ : T₁) = S₁.evT Q := Subtype.ext (by rw [S₁.coe_evT, hQv])
  have hreg : S₁.RegularFinite (AlgebraicClosure (TE.F m)) ⟨ψ f, hfT⟩ := by
    rw [hfQ]; exact S₁.regularFinite_evT Q
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  -- geometric irreducibility and a branch system above infinity
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := TE.nkF_geo_of_eisCk m hTEm Pp qE csE sE tE s2E t2E hck _
  -- zero residues along the split branch system above infinity
  have hrde0 := MSEm.rde ⟨(MO Fc ks m).one, []⟩ (fun cw hcw ↦ by simp at hcw)
  obtain ⟨li, hli, hzr⟩ := zero_res_codes (K := AlgebraicClosure (TE.F m)) S₁ (TE.MP m hTEm)
    _ hrde0 hK Pp rfl sR MR γs Θs fp hres0 hn0
  have hnd' : ∀ a : AlgebraicClosure (TE.F m),
      a′ ≠ algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) η₁ := fun a ↦ by
    have := hnd a; rwa [Polynomial.map_C, eval_C] at this
  have hzero : ∀ r (hr : r ∈ li), ∃ γ : AlgebraicClosure (TE.F m),
      (S₁.embG (infSub 1) (infSub_injective 1 one_pos) r (S₁.root_of_mem hli hr)
        ⟨ψ f, hfT⟩).coeff 1 = γ′ := by
    intro r hr; rw [hfQ]; exact hzr r hr
  obtain ⟨ℓ₀, hℓ₀⟩ := S₁.nk_liouville_noRes η₁ hx hK hnd' hgeo' 1 one_pos li hli hconstC (ψ f) hfT
    hreg hzero s' c u (fun i hi ↦ (hdata i hi).1)
    (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v (hCT v hv) heq₁
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  -- the trace
  obtain ⟨hs0, hτ⟩ := TE.traceW_sound m hTE Pp (ψ θ) hPθE dθ wθ s hs
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  obtain ⟨w, hw, hwe⟩ := S₁.trace_split (fun j ↦ ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁))
    (fun j ↦ (TE.mem_F_succ).mp (M1.sem (s.getD j O1.zero)).2)
    (by rw [hS₁F, hs0]; push_cast; rfl)
    (fun i hi ↦ by
      rw [hS₁F] at hi ⊢
      obtain ⟨c', hc'd, hc's⟩ := hτ i hi
      refine ⟨fun j ↦ (c' j : E₁), fun j ↦ (TE.mem_F_succ).mp (c' j).2, hc'd, ?_⟩
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) hc's
      simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        MTower.coe_deriv] at this
      exact this)
    hdx (fun j ↦ TE.evP m (fp.getD j []))
    (fun j ↦ (TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j = _
      rw [← hψf, hℓ₀])
  rw [hS₁F] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ = ∑ i ∈ s', c i * logDeriv (u i) := by
    have := hℓ₀.symm.trans heq₁
    linear_combination this
  refine ⟨?_, ?_⟩
  · -- the exact part in the lifted tower
    have hvw : v - w ∈ T₁ := sub_mem (hCT v hv) (IntermediateField.algebraMap_mem T₁
      (⟨w, hw⟩ : (TE.F m)⟮S₁.x⟯))
    obtain ⟨Y', hY'm, hY'⟩ := S₁.exists_coords (v - w) hvw
    rw [hS₁F] at hY'
    have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
    have hind : ∀ a : ℕ → TE.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : E₁) * (ψ θ) ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [hlen]; exact TE.nkCurveE_ind m hTE Pp qE csE sE tE s2E t2E hck (ψ θ) hθE
    have hiff := TE.exactTLVG_correct m hTE (by omega) hk (hTE m (by omega)) (prdeC Fc ks lv m)
      MSEm.rde dg C Ci r (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind Tc Ti [] res hres
    refine hiff.mpr ⟨fun _ ↦ 0, fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen]
    simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, sub_zero]
    rw [TE.sum_nkRest m hTE n hn0, hTEev (m + 1) q]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map (fun i ↦ (c i, u i)) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [Finset.mem_toList] at hi
      exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_map, Finset.sum_map_toList]
      rfl
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform

/-- **The decision with zero residues at the split places at infinity** (logarithmic level,
non-constant curves, no units): if `splitResCk` passes, `∫ f` is elementary iff the exact-part test
without logarithms succeeds and `τ(f)/n` is elementary. -/
theorem nk_iffInfVG0 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true) (θ : L)
    (hn0 : 0 < Pp.length) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (sR MR : ℕ) (γs : List (LC m)) (Θs : List (GPoly (LC m)))
    (hres0 : splitResCk Fc ks lv m sR MR Pp γs Θs fp = true)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ)
    (hres : exactTLVG Fc ks m η (prdeC Fc ks lv m) dg C Ci r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) [] =
        some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  refine ⟨T.nk_necessaryInfVG0 hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck θ hn0 dθ wθ s hθ
    hgen hs fp sR MR γs Θs hres0 Tc Ti res dg C Ci r hres, fun h ↦ ?_⟩
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  exact T.nk_sufficientInfVG m hTr (by omega) hk (hTr m (by omega)) (prdeC Fc ks lv m) MSm.rde dg C
    Ci r Pp hn0 θ hθ (T.nkCurveE_ind m hTr Pp qE csE sE tE s2E t2E hck θ hθ) [] [] [] dθ wθ s
    (by simp [unitsC]) fp Tc Ti res hres h.1 h.2

end MTower

end Curves.MT


