import RischTragerBronstein.Mixed.NKInf0ExpRD
import RischTragerBronstein.Mixed.NKUnits0D
import RischTragerBronstein.Mixed.NKMultiRUnits0
import RischTragerBronstein.Mixed.NKMultiRShape

/-!
# Several slopes at infinity and several places above `t = 0` (exponential level)

`nk_iffETInf0MRD`: as `nk_iffETInf0R`, with Newton segments of any rational slopes at infinity
(`multiShapeRC`, `∑ₖ |Γₖ|` places): `∑ₖ |Γₖ| + n − 2` S-units (`unitsC0`, `indepWC`) with `x` span
the S-units (`unitsSpan0_multiR`).
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

lemma nPlacesR_pos {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} (m : ℕ) (Pp : List (GPoly (LC m)))
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) : 0 < nPlacesR segs := by
  unfold multiShapeRC at hms
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
  obtain ⟨⟨⟨⟨hn0, -⟩, hsum⟩, -⟩, -⟩ := hms
  by_contra h0
  have h0' : nPlacesR segs = 0 := by omega
  unfold nPlacesR at h0'
  have : (segs.map fun sg ↦ sg.1 * sg.2.2.2.2.length).sum = 0 := by
    rw [List.sum_eq_zero_iff] at h0' ⊢
    intro x hx
    obtain ⟨sg, hsg, rfl⟩ := List.mem_map.mp hx
    have := h0' _ (List.mem_map.mpr ⟨sg, hsg, rfl⟩)
    simp [this]
  omega


variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 16000000 in
/-- **`⇒`** (several places at infinity, exponential level): the logarithmic part of a Liouville
form is `∑ κᵢ uᵢ′/uᵢ + ℓ`. -/
theorem nk_necessaryETInf0MRD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (ds : List (GPoly (LC m)))
    (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
    (gls : List (GPoly (LC (m + 1))))
    (hk1 : gls.length + 2 = nPlacesR segs + Pp.length)
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ((MO Fc ks m).deriv a) gls dθ wθ s = true)
    (J D : List ℕ) (H : List (List (LC (m + 1)))) (hJH : indepWC Fc ks m gls J D H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m))
    (hres : exactTLEVG Fc ks m a (prdeC Fc ks lv m) dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gls = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  classical
  have hn0 : 0 < Pp.length := by
    unfold multiShapeRC at hms
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    exact hms.1.1.1.1
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
  set η₁ : TE.F m := (TE.val m a)′ with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁ * X) := by
    rw [map_mul, aeval_C, aeval_X]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m), α ≠ 0 →
      α′ ≠ ((Polynomial.C η₁ * X).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α hα ↦ by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X]
      refine not_exp_of_integral η₁ (fun dd hdd z hz h ↦ ?_) α (Algebra.IsIntegral.isIntegral α) hα
      have := MSE.hyp.hom m (by omega) a hk (-(dd : ℤ)) (by omega) z hz
      apply this
      rw [h, show TE.val m a = TE.val m a from rfl]
      push_cast
      ring
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
  have hresF : ∀ (b : AlgebraicClosure (TE.F m)), b ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l) (k : ℤ), k < 1 - (N : ℤ) →
      (S₁.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S₁.root_of_mem hl hr) ⟨ψ f, hfT⟩).coeff k = 0 := by
    intro b _ N hN l hl r hr k hk
    apply HahnSeries.coeff_eq_zero_of_lt_order
    have := hreg b N hN l hl r hr
    have : (1 : ℤ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
    omega
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  -- geometric irreducibility and a branch system above infinity
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := TE.nkF_geo_of_eisCk m hTEm Pp qE csE sE tE s2E t2E hck _
  obtain ⟨Ni, hNi, li, -, hli⟩ := S₁.hasBranchesInf (K := AlgebraicClosure (TE.F m))
  have htsE : TE.ts m ≠ 0 := fun h ↦ (hTE m (by omega)) ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  have hevPol : ∀ W : List (GPoly (LC m)), S₁.evXY (∑ j ∈ Finset.range W.length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (W.getD j [])) * X ^ j) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m W) := by
    intro W
    rw [TE.evθ_nkFl m hTE (ψ θ) W, CurveData.evXY, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
      eval_C, eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  set k := gls.length with hkk
  set UP : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ j ∈ Finset.range (Us.getD i []).length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) ((Us.getD i []).getD j [])) * X ^ j with hUP
  set VP : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ j ∈ Finset.range (Vs.getD i []).length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) ((Vs.getD i []).getD j [])) * X ^ j with hVP
  set jE : Fin k → ℤ := fun i ↦ ((jj.getD i 0 : ℕ) : ℤ) with hjE
  set CP : GPoly (LC m) → (TE.F m)[X][X] := fun c ↦ ∑ j ∈ Finset.range [c].length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) ([c].getD j [])) * X ^ j with hCP
  have hcP : ∀ c, (S₁.evT (CP c) : E₁) = TE.evP m c := fun c ↦ by
    rw [S₁.coe_evT, hCP, hevPol, TE.evθ_nkFl_single]
  set WU : Fin k → T₁ := fun i ↦ S₁.evT (UP i) / S₁.evT (CP (ds.getD i [])) with hWU
  set WV : Fin k → T₁ := fun i ↦ S₁.evT (VP i) / S₁.evT (CP (ds.getD i [])) with hWV
  set u0T : Fin k → T₁ := fun i ↦ WU i * S₁.xE ^ (-jE i) with hu0T
  set v0T : Fin k → T₁ := fun i ↦ WV i * S₁.xE ^ (jE i - (kk.getD i 0 : ℕ)) with hv0T
  have hxE1 : (S₁.xE : E₁) = TE.ts m := by rw [S₁.coe_xE]; rfl
  have hzE : ∀ e : ℤ, ((S₁.xE ^ e : T₁) : E₁) = TE.ts m ^ e := fun e ↦ by
    rw [show ((S₁.xE ^ e : T₁) : E₁) = (S₁.xE : E₁) ^ e from map_zpow₀ T₁.val S₁.xE e, hxE1]
  have hUv : ∀ i : Fin k, ((S₁.evT (UP i) : T₁) : E₁) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Us.getD i [])) := fun i ↦ by
    rw [S₁.coe_evT, hUP, hevPol]
  have hVv : ∀ i : Fin k, ((S₁.evT (VP i) : T₁) : E₁) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Vs.getD i [])) := fun i ↦ by
    rw [S₁.coe_evT, hVP, hevPol]
  have hWUv : ∀ i : Fin k, (WU i : E₁) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Us.getD i [])) / TE.evP m (ds.getD i []) := fun i ↦ by
    rw [hWU]; simp only; rw [IntermediateField.coe_div, hUv, hcP]
  have hWVv : ∀ i : Fin k, (WV i : E₁) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Vs.getD i [])) / TE.evP m (ds.getD i []) := fun i ↦ by
    rw [hWV]; simp only; rw [IntermediateField.coe_div, hVv, hcP]
  have hu0v : ∀ i : Fin k, (u0T i : E₁) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Us.getD i [])) / TE.evP m (ds.getD i []) *
        TE.ts m ^ (-jE i) := fun i ↦ by
    rw [hu0T]; simp only; rw [IntermediateField.coe_mul, hWUv, hzE]
  have hv0v : ∀ i : Fin k, (v0T i : E₁) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Vs.getD i [])) / TE.evP m (ds.getD i []) *
        TE.ts m ^ (jE i - (kk.getD i 0 : ℕ)) :=
    fun i ↦ by rw [hv0T]; simp only; rw [IntermediateField.coe_mul, hWVv, hzE]
  have hfacts := fun i : Fin k ↦ TE.units0D_facts m hTE (ψ θ) Pp hPθE htsE _ _ _ _ _ _ _ _ _ _ dθ wθ
    (unitsC0D_spec hU i i.2).1 (unitsC0D_spec hU i i.2).2.1
  have hhor : ∀ (z : T₁) (zE : E₁) (cs : List (GPoly (LC m))), (z : E₁) = zE →
      hornerZ zE (cs.map (TE.evP m)) 1 = 0 → hornerZ z ((cs.map CP).map S₁.evT) 1 = 0 := by
    intro z zE cs hz h0
    apply (algebraMap T₁ E₁).injective
    rw [hornerZ_map, map_one, map_zero, List.map_map, List.map_map, IntermediateField.algebraMap_apply,
      hz, ← h0]
    congr 1
    exact List.map_congr_left fun c _ ↦ by
      simp only [Function.comp, IntermediateField.algebraMap_apply]; exact hcP c
  have huvE : ∀ i : Fin k, (u0T i : E₁) * (v0T i : E₁) = 1 := fun i ↦ by
    have h := (hfacts i).2.1
    rw [hu0v, hv0v]
    calc _ = (TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Us.getD i [])) / TE.evP m (ds.getD i []) *
          (TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Vs.getD i [])) / TE.evP m (ds.getD i []))) *
          (TE.ts m ^ (-jE i) * TE.ts m ^ (jE i - (kk.getD i 0 : ℕ))) := by ring
      _ = 1 := by
        rw [h, ← zpow_add₀ htsE, ← zpow_natCast, ← zpow_add₀ htsE]
        ring_nf
        exact zpow_zero _
  have huv1 : ∀ i, u0T i * v0T i = 1 := fun i ↦
    Subtype.ext (by rw [IntermediateField.coe_mul, huvE]; rfl)
  have hu00 : ∀ i, u0T i ≠ 0 := fun i ↦ left_ne_zero_of_mul_eq_one (huv1 i)
  have hu0E : ∀ i, (u0T i : E₁) ≠ 0 := fun i h ↦ hu00 i (Subtype.ext h)
  have hfin0 : ∀ i (a : AlgebraicClosure (TE.F m)), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l),
      (S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S₁.root_of_mem hl hr) (u0T i)).order = 0 := by
    intro i a ha N hN l hl r hr
    set φ := S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S₁.root_of_mem hl hr)
    have hx0 := S₁.order_xE_branch a ha N hN l hl r hr
    have hxne : φ S₁.xE ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr S₁.xE_ne_zero
    have h1 : φ (u0T i) * φ (v0T i) = 1 := by rw [← map_mul, huv1, map_one]
    have hu' : φ (u0T i) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hv' : φ (v0T i) ≠ 0 := right_ne_zero_of_mul_eq_one h1
    have hU0 : φ (WU i) ≠ 0 := fun h0 ↦ hu' (by rw [hu0T]; simp only; rw [map_mul, h0,
      zero_mul])
    have hV0 : φ (WV i) ≠ 0 := fun h0 ↦ hv' (by rw [hv0T]; simp only; rw [map_mul, h0,
      zero_mul])
    have o1 := S₁.regularFinite_of_horner (K := AlgebraicClosure (TE.F m)) (WU i) _
      (hhor _ _ (cUs.getD i []) (hWUv i) (hfacts i).2.2.1) a N hN l hl r hr
    have o2 := S₁.regularFinite_of_horner (K := AlgebraicClosure (TE.F m)) (WV i) _
      (hhor _ _ (cVs.getD i []) (hWVv i) (hfacts i).2.2.2.1) a N hN l hl r hr
    have hou : (φ (u0T i)).order = (φ (WU i)).order := by
      rw [hu0T]; simp only
      rw [map_mul, map_zpow₀, HahnSeries.order_mul hU0 (zpow_ne_zero _ hxne), order_zpow_ls _ hxne,
        hx0, mul_zero, add_zero]
    have hov : (φ (v0T i)).order = (φ (WV i)).order := by
      rw [hv0T]; simp only
      rw [map_mul, map_zpow₀, HahnSeries.order_mul hV0 (zpow_ne_zero _ hxne), order_zpow_ls _ hxne,
        hx0, mul_zero, add_zero]
    have ho := congrArg HahnSeries.order h1
    rw [HahnSeries.order_mul hu' hv', HahnSeries.order_one] at ho
    change 0 ≤ (φ (WU i)).order at o1
    change 0 ≤ (φ (WV i)).order at o2
    omega
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set G : ℕ → ℕ → E₁ := fun i j ↦ ((M1.sem ((gls.getD i []).getD j O1.zero) : TE.F (m + 1)) : E₁)
    with hG
  have hld : ∀ i : Fin k, TE.evθ m hTE (ψ θ) (gls.getD i []) = (u0T i : E₁)′ / (u0T i : E₁) :=
    fun i ↦ by
      have hU0 : TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Us.getD i [])) / TE.evP m (ds.getD i []) ≠ 0 :=
        fun h0 ↦ by
          have := huvE i
          rw [hu0v, h0, zero_mul, zero_mul] at this
          exact zero_ne_one this
      rw [(hfacts i).2.2.2.2, hu0v, ← logDeriv, ← logDeriv,
        Differential.logDeriv_mul _ _ hU0 (zpow_ne_zero _ htsE), logDeriv_zpow' _ htsE]
      have hηE : TE.ev m ((MO Fc ks m).deriv a) = logDeriv (TE.ts m) := by
        rw [logDeriv, TE.deriv_ts_L_exp m hTEm (by omega) hk, TE.sem_MP m hTEm, mul_div_assoc,
          div_self htsE, mul_one]
      rw [hηE, hjE]
      push_cast
      ring
  have hlogu : ∀ i : Fin k, logDeriv (u0T i : E₁) = ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j :=
    fun i ↦ by
      rw [logDeriv, ← hld i, TE.evθ_list_le m hTE (ψ θ) _ n (unitsC0D_spec hU i i.2).2.2.1]
  have hindθ := TE.nkCurveE_ind m hTE Pp qE csE sE tE s2E t2E hck (ψ θ) hθE
  have hindU : ∀ (e0 : ℤ) (a : Fin k → ℤ), (∃ c : TE.F m, S₁.x ^ e0 * ∏ i, (u0T i : E₁) ^ a i =
      algebraMap (TE.F m) E₁ c) → e0 = 0 ∧ a = 0 :=
    TE.indepWC_sound_t m hTE (hTE m (by omega)) (ψ θ) n hn0 hindθ gls
      (fun i hi ↦ (unitsC0D_spec hU i hi).2.2.1) (fun i ↦ (u0T i : E₁)) hu0E hld J D H hJH
  -- the S-units are spanned by `x` and the `uᵢ`
  obtain ⟨N0, hN0, l0, hl0⟩ := S₁.hasBranches_list (K := AlgebraicClosure (TE.F m)) S₁.hasBranches 0
  obtain ⟨qs, hqs, -, hePos, hgcd, hdecS, hcne, hΓ, hbd, hres0, htop, hchain, hlast⟩ :=
    TE.multiShapeR_spec m hTEm Pp segs hms
  have hnpS : ∑ k : Fin (qs + 1),
      (((segs.getD k (segRD Fc ks m)).2.2.2.2).map (TE.MP m hTEm).sem).length = nPlacesR segs := by
    simp only [List.length_map]
    exact sum_fin_getD segs (segRD Fc ks m) (fun sg ↦ sg.2.2.2.2.length) hqs
  have hnp1 := nPlacesR_pos (Fc := Fc) (ks := ks) m Pp segs hms
  have hspan : S₁.UnitsSpan0 (AlgebraicClosure (TE.F m)) u0T := by
    refine S₁.unitsSpan0_multiR hgeo' (fun k ↦ (segs.getD k (segRD Fc ks m)).1) hePos
      (fun k ↦ (segs.getD k (segRD Fc ks m)).2.1) hgcd hdecS
      (fun k ↦ (segs.getD k (segRD Fc ks m)).2.2.1)
      (fun k ↦ (TE.MP m hTEm).sem (segs.getD k (segRD Fc ks m)).2.2.2.1) hcne
      (fun k ↦ loRC segs k) (fun k ↦ ((segs.getD k (segRD Fc ks m)).2.2.2.2).map (TE.MP m hTEm).sem)
      hΓ hbd hres0 htop hchain hlast N0 hN0 l0 hl0 (mI := nPlacesR segs - 1)
      (by rw [hnpS]; omega) ?_ u0T hu00 hfin0 hindU
    rw [S₁.length_of_split hl0, hS₁F]
    have hk1' := hk1
    simp only [hnn] at hk1' ⊢
    omega

  obtain ⟨κ, ℓ₀, hκ, hℓ₀⟩ := S₁.nk_liouvilleEU_span0 (K := AlgebraicClosure (TE.F m))
    (Polynomial.C η₁ * X) hx hK η₁ rfl hnd u0T hspan hu00 hconstC (ψ f) hfT
    hresF s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  set κE : Fin k → E₁ := fun i ↦ algebraMap (TE.F m) E₁ (κ i) with hκE
  have hκE' : ∀ i, (κE i)′ = 0 := fun i ↦ by
    rw [hκE]; simp only; rw [deriv_algebraMap, hκ i, map_zero]
  have hc0 : ∀ i, κE i ∈ Set.range (algebraMap _ E₁) := fun i ↦ TE.hconst _ (hκE' i)
  simp only [Set.mem_range] at hc0
  choose c0 hc0 using hc0
  have hκsum : ∀ w : ℕ → E₁, ∑ j ∈ Finset.range n, (∑ i : Fin k, κE i * G i j) * w j =
      ∑ i : Fin k, κE i * ∑ j ∈ Finset.range n, G i j * w j := fun w ↦ by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- the trace
  obtain ⟨hs0, hτ⟩ := TE.traceW_sound m hTE Pp (ψ θ) hPθE dθ wθ s hs
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  have hκx : ∀ i, κE i ∈ (TE.F m)⟮S₁.x⟯ := fun i ↦ IntermediateField.algebraMap_mem _ (κ i)
  set fc : ℕ → E₁ := fun j ↦ TE.evP m (fp.getD j []) - ∑ i : Fin k, κE i * G i j with hfc
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
    hdx fc (fun j ↦ sub_mem ((TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
      (sum_mem fun i _ ↦ mul_mem (hκx i) ((TE.mem_F_succ).mp (M1.sem ((gls.getD i []).getD j
        O1.zero)).2)))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, fc j * (ψ θ) ^ j = _
      simp only [hfc, sub_mul, Finset.sum_sub_distrib]
      rw [hκsum, ← hψf, hℓ₀]
      simp only [← hlogu, hκE]
      ring)
  rw [hS₁F] at hwe
  -- `τ(uᵢ′/uᵢ) = 0`
  have hτ0 : ∀ i : Fin k, ∑ j ∈ Finset.range n, G i j *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
    intro i
    have h1 := (M1.isZero_iff _).mp (unitsC0D_spec hU i i.2).2.2.2.1
    rw [TE.sem_nkTau m n hTE (gls.getD i []) s] at h1
    have hn' : ((n : ℕ) : TE.F (m + 1)) ≠ 0 := by exact_mod_cast hn0.ne'
    have h2 : ∑ j ∈ Finset.range n, M1.sem ((gls.getD i []).getD j O1.zero) *
        M1.sem (s.getD j O1.zero) = 0 :=
      (mul_eq_zero.mp h1).resolve_right (inv_ne_zero hn')
    have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) h2
    simpa only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
      ZeroMemClass.coe_zero] using this
  have hτf : ∑ j ∈ Finset.range n, fc j * ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) =
      ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) := by
    simp only [hfc, sub_mul, Finset.sum_sub_distrib]
    rw [hκsum, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin k))) fun i _ ↦ by
      rw [hτ0 i, mul_zero], sub_zero]
  rw [hτf] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ =
      ∑ i ∈ s', c i * logDeriv (u i) - ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
    have := hℓ₀.symm.trans heq₁
    rw [eq_sub_iff_add_eq]
    linear_combination this
  refine ⟨?_, ?_⟩
  · ----------------------------------------------------------------------------------------------
    -- the exact part in the lifted tower
    have hvw : v - w ∈ T₁ := sub_mem (hCT v hv) (IntermediateField.algebraMap_mem T₁
      (⟨w, hw⟩ : (TE.F m)⟮S₁.x⟯))
    obtain ⟨Y', hY'm, hY'⟩ := S₁.exists_coords (v - w) hvw
    rw [hS₁F] at hY'
    have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
    have hind : ∀ a : ℕ → TE.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : E₁) * (ψ θ) ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [hlen]; exact TE.nkCurveE_ind m hTE Pp qE csE sE tE s2E t2E hck (ψ θ) hθE
    obtain ⟨hrdeE, homE⟩ := TE.expTEV_specs hmon hdeg m (by rw [hTEn]; exact hn) hc hk
    have hiff := TE.exactTLEVG_correct m hTE (by rw [hTEn, hn]; omega) hk (hTE m (by omega))
      (prdeC Fc ks lv m) hrdeE homE dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind Tc Ti gls res
      hres
    set c' := fun i ↦ if h : i < k then c0 ⟨i, h⟩ else 0 with hc'
    refine hiff.mpr ⟨c', fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [TE.sum_nkRest m hTE n hn0, hTEev (m + 1) q]
    have hcs : ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range k, algebraMap _ E₁ (c' i) * G i j) *
        (ψ θ) ^ j = ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
      have e : ∀ j, ∑ i ∈ Finset.range k, algebraMap _ E₁ (c' i) * G i j =
          ∑ i : Fin k, κE i * G i j := fun j ↦ by
        rw [← Fin.sum_univ_eq_sum_range (fun i ↦ algebraMap _ E₁ (c' i) * G i j)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [hc', dif_pos i.2, Fin.eta, hc0]
      simp only [e]
      rw [hκsum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hlogu]
    rw [hcs]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map (fun i ↦ (c i, u i)) ++
      (List.finRange k).map (fun i ↦ (-κE i, (u0T i : E₁))) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        rw [Finset.mem_toList] at hi
        exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
        exact ⟨by rw [map_neg, hκE' i, neg_zero], hu0E i⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_append, List.sum_append, List.map_map,
        Finset.sum_map_toList, List.map_map, ← Fin.sum_univ_def]
      simp only [Function.comp_def, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform



/-- **The decision with several places at infinity and above `t = 0` for non-constant curves**
(exponential level; Eisenstein certificate, `2n − 2` S-units `uᵢ` with `uᵢ vᵢ = t^{kᵢ}`,
`τ(uᵢ′/uᵢ) = 0`, independent together with `t` by `indepWC`). -/
theorem nk_iffETInf0MRD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (ds : List (GPoly (LC m)))
    (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
    (gls : List (GPoly (LC (m + 1))))
    (hk1 : gls.length + 2 = nPlacesR segs + Pp.length)
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ((MO Fc ks m).deriv a) gls dθ wθ s = true)
    (J D : List ℕ) (H : List (List (LC (m + 1)))) (hJH : indepWC Fc ks m gls J D H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
    (dg0 : List (ℚ × ℚ × LC m))
    (hres : exactTLEVG Fc ks m a (prdeC Fc ks lv m) dg Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gls =
        some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  refine ⟨T.nk_necessaryETInf0MRD hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ Us Vs kk jj ds cUs cVs Es gls hk1
    dθ wθ s hU J D H hJH hθ hgen hs fp Tc Ti res dg Cg Cgi r C Ci dg0 hres, fun h ↦ ?_⟩
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  exact T.nk_sufficientETInf0RD m hTr (by omega) hk (hTr m (by omega)) (prdeC Fc ks lv m) hrde hom
    dg Cg Cgi r C Ci dg0 Pp (by
      unfold multiShapeRC at hms
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
      exact hms.1.1.1.1) θ hθ
    (T.nkCurveE_ind m hTr Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs
    kk jj ds cUs cVs Es gls dθ wθ s hU fp Tc Ti res hres h.1 h.2

end MTower

end Curves.MT

