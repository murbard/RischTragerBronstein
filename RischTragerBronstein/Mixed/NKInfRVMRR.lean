import RischTragerBronstein.Mixed.NKInfRVMR
import RischTragerBronstein.Mixed.NKUnitsInfLogR

/-!
# Several slopes at infinity with residue-free finite poles (logarithmic level)

`nk_iffInfVMRR`: `nk_iffInfVMR` for integrands `∑ bⱼ(t)/D(t) θʲ` whose poles are residue-free
(`resCert`: `Bᵏ ≡ U D mod P`, so `f dx` has no pole above the roots of the squarefree `D`): the
logarithms of a Liouville form are still units (`nk_liouville_units_spanR`), and the exact part is
decided as before (`exactTLVG` answers for any right-hand side).
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

set_option maxHeartbeats 16000000 in
/-- **`⇒`** (several places at infinity, logarithmic level): the logarithmic part of a Liouville
form is `∑ κᵢ uᵢ′/uᵢ + ℓ`. -/
theorem nk_necessaryInfVMRR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (hk1 : gls.length + 1 = nPlacesR segs)
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (J : List ℕ) (H : List (List (LC (m + 1)))) (hJH : indepC Fc ks m gls J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ)
    (hres : exactTLVG Fc ks m η (prdeC Fc ks lv m) dg C Ci r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) gls = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) := by
  classical
  have hn0 : 0 < Pp.length := by
    unfold multiShapeRC at hms
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    exact hms.1.1.1.1
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) / T.evP m D * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFlR m fp D) s with hq
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
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) / TE.evP m D * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_div₀, map_pow, hPE]
  -- the poles are residue-free
  have hPT : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  obtain ⟨hkc, hBU⟩ := T.resCert_sound m hTr Pp fp D kc U θ hPT hcert
  rw [hfpl] at hBU
  set MD := GPoly.toPoly (TE.MP m hTEm) D with hMD
  have hsqD : Squarefree MD := GPoly.squarefreeCheck_sound (TE.MP m hTEm) hsq
  have hD0 : MD ≠ 0 := hsqD.ne_zero
  have hmult : ∀ a : AlgebraicClosure (TE.F m),
      (MD.map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).rootMultiplicity a ≤ 1 := fun a ↦
    Polynomial.rootMultiplicity_le_one_of_separable
      ((PerfectField.separable_iff_squarefree.mpr hsqD).map) a
  have hevQ : ∀ (l : List (GPoly (LC m))) (N0 : ℕ), S₁.evXY (∑ j ∈ Finset.range N0,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (l.getD j [])) * X ^ j) =
      ∑ j ∈ Finset.range N0, TE.evP m (l.getD j []) * (ψ θ) ^ j := by
    intro l N0
    rw [CurveData.evXY, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
      eval_C, eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  set QB : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQB
  set QU : (TE.F m)[X][X] := ∑ j ∈ Finset.range U.length,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (U.getD j [])) * X ^ j with hQU
  have hDv : aeval S₁.x MD = TE.evP m D := TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hBUE : (S₁.evXY QB) ^ kc = S₁.evXY QU * aeval S₁.x MD := by
    rw [hQB, hQU, hevQ, hevQ, hDv]
    have := congrArg ψ hBU
    simp only [map_pow, map_mul, map_sum] at this
    simpa only [hPE] using this
  have hfT : ψ f ∈ T₁ := hLT f
  set Dm : T₁ := ⟨aeval S₁.x MD, S₁.aeval_mem MD⟩ with hDm
  have hfe : (⟨ψ f, hfT⟩ : T₁) = S₁.evT QB / Dm := by
    apply Subtype.ext
    rw [IntermediateField.coe_div, S₁.coe_evT]
    change ψ f = S₁.evXY QB / aeval S₁.x MD
    rw [hQB, hevQ, hψf, hDv, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hresid : ∀ (a : AlgebraicClosure (TE.F m)) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l) (k : ℤ), k < 1 - (N : ℤ) →
      (S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S₁.root_of_mem hl hr) ⟨ψ f, hfT⟩).coeff k = 0 := by
    intro a N hN l hl r hr k hk
    have hNp := Nat.pos_of_ne_zero hN
    set φ := S₁.embG (branchSub N a) (branchSub_injective N hNp a) r (S₁.root_of_mem hl hr)
      with hφ
    have hB := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) QB a N hN l hl r hr
    have hU := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) QU a N hN l hl r hr
    have hdm : φ Dm = branchSub N a MD := S₁.embG_polyX _ _ _ _ MD (S₁.aeval_mem MD)
    have hdd0 : branchSub (K := AlgebraicClosure (TE.F m)) N a MD ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective N hNp a)).mpr hD0
    have hddo := order_branchSub (K := AlgebraicClosure (TE.F m)) N hNp a MD hD0
    have hrel : (φ (S₁.evT QB)) ^ kc = φ (S₁.evT QU) * branchSub N a MD := by
      have e : (S₁.evT QB) ^ kc = S₁.evT QU * Dm :=
        Subtype.ext (by
          rw [IntermediateField.coe_pow, IntermediateField.coe_mul, S₁.coe_evT, S₁.coe_evT]
          exact hBUE)
      have := congrArg φ e
      rw [map_pow, map_mul, hdm] at this
      exact this
    change (φ ⟨ψ f, hfT⟩).coeff k = 0
    rw [hfe, map_div₀, hdm]
    by_cases hb0 : φ (S₁.evT QB) = 0
    · rw [hb0, zero_div]; rfl
    have hu0 : φ (S₁.evT QU) ≠ 0 := fun h0 ↦ by
      rw [h0, zero_mul] at hrel; exact hb0 (pow_eq_zero_iff (by omega) |>.mp hrel)
    have hBo : 0 ≤ (φ (S₁.evT QB)).order := hB
    have hUo : 0 ≤ (φ (S₁.evT QU)).order := hU
    have hord := congrArg HahnSeries.order hrel
    rw [HahnSeries.order_pow, HahnSeries.order_mul hu0 hdd0, hddo, nsmul_eq_mul] at hord
    set μ := (MD.map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).rootMultiplicity a
    have hμ := hmult a
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [div_eq_mul_inv, HahnSeries.order_mul hb0 (inv_ne_zero hdd0), order_inv_nk _ hdd0, hddo]
    have hkc' : (0 : ℤ) < kc := by exact_mod_cast hkc
    push_cast at hord ⊢
    rcases Nat.lt_or_ge μ 1 with h0 | h1
    · have : μ = 0 := by omega
      rw [this] at hord ⊢; push_cast at hord ⊢; linarith
    · have : μ = 1 := by omega
      rw [this] at hord ⊢
      push_cast at hord ⊢
      have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hNp
      have : 1 ≤ (φ (S₁.evT QB)).order := by
        by_contra hlt
        push Not at hlt
        have : (φ (S₁.evT QB)).order ≤ 0 := by omega
        nlinarith
      linarith
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  -- geometric irreducibility and a branch system above infinity
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := TE.nkF_geo_of_eisCk m hTEm Pp qE csE sE tE s2E t2E hck _
  -- the unit `u₀`, its inverse and its logarithmic derivative
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
  set u0T : Fin k → T₁ := fun i ↦ S₁.evT (UP i) with hu0T
  set v0T : Fin k → T₁ := fun i ↦ S₁.evT (VP i) with hv0T
  have hu0v : ∀ i : Fin k, (u0T i : E₁) = TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Us.getD i [])) :=
    fun i ↦ by rw [hu0T]; simp only; rw [S₁.coe_evT, hUP, hevPol]
  have hv0v : ∀ i : Fin k, (v0T i : E₁) = TE.evθ m hTE (ψ θ) (nkFl Fc ks m (Vs.getD i [])) :=
    fun i ↦ by rw [hv0T]; simp only; rw [S₁.coe_evT, hVP, hevPol]
  have huvE : ∀ i : Fin k, (u0T i : E₁) * (v0T i : E₁) = 1 := fun i ↦ by
    rw [hu0v, hv0v]; exact TE.unitC_sound m hTE (ψ θ) Pp _ _ hPθE (unitsC_spec hU i i.2).1
  have huv1 : ∀ i, u0T i * v0T i = 1 := fun i ↦
    Subtype.ext (by rw [IntermediateField.coe_mul, huvE]; rfl)
  have hu00 : ∀ i, u0T i ≠ 0 := fun i ↦ left_ne_zero_of_mul_eq_one (huv1 i)
  have hu0E : ∀ i, (u0T i : E₁) ≠ 0 := fun i h ↦ hu00 i (Subtype.ext h)
  have hfin0 : ∀ i (a : AlgebraicClosure (TE.F m)) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l),
      (S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S₁.root_of_mem hl hr) (u0T i)).order = 0 := by
    intro i a N hN l hl r hr
    set φ := S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S₁.root_of_mem hl hr)
    have h1 : φ (u0T i) * φ (v0T i) = 1 := by rw [← map_mul, huv1, map_one]
    have hu' : φ (u0T i) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hv' : φ (v0T i) ≠ 0 := right_ne_zero_of_mul_eq_one h1
    have o1 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (UP i) a N hN l hl r hr
    have o2 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (VP i) a N hN l hl r hr
    have ho := congrArg HahnSeries.order h1
    rw [HahnSeries.order_mul hu' hv', HahnSeries.order_one] at ho
    change 0 ≤ (φ (u0T i)).order at o1
    change 0 ≤ (φ (v0T i)).order at o2
    omega
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set G : ℕ → ℕ → E₁ := fun i j ↦ ((M1.sem ((gls.getD i []).getD j O1.zero) : TE.F (m + 1)) : E₁)
    with hG
  have hld : ∀ i : Fin k, TE.evθ m hTE (ψ θ) (gls.getD i []) = (u0T i : E₁)′ / (u0T i : E₁) :=
    fun i ↦ by
      obtain ⟨huv, hgl, -, -⟩ := unitsC_spec hU i i.2
      rw [hu0v]
      exact TE.logDerChk_sound m hTE (ψ θ) Pp _ _ _ dθ wθ hPθE
        (TE.unitC_sound m hTE (ψ θ) Pp _ _ hPθE huv) hgl
  have hlogu : ∀ i : Fin k, logDeriv (u0T i : E₁) = ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j :=
    fun i ↦ by
      rw [logDeriv, ← hld i, TE.evθ_list_le m hTE (ψ θ) _ n (unitsC_spec hU i i.2).2.2.1]
  have hindθ := TE.nkCurveE_ind m hTE Pp qE csE sE tE s2E t2E hck (ψ θ) hθE
  have hindU : ∀ a : Fin k → ℤ, (∃ c : TE.F m, ∏ i, (u0T i : E₁) ^ a i =
      algebraMap (TE.F m) E₁ c) → a = 0 :=
    TE.indepC_sound m hTE (ψ θ) n hindθ gls (fun i hi ↦ (unitsC_spec hU i hi).2.2.1)
      (fun i ↦ (u0T i : E₁)) hu0E hld J H hJH
  -- the logarithmic part is `∑ κᵢ uᵢ′/uᵢ + ℓ`
  have hspan : S₁.UnitsSpan (AlgebraicClosure (TE.F m)) u0T := by
    obtain ⟨q, hq, -, hePos, hgcd, hdecS, hcne, hΓ, hbd, hres, htop, hchain, hlast⟩ :=
      TE.multiShapeR_spec m hTEm Pp segs hms
    have hcount : ∑ k : Fin (q + 1),
        (((segs.getD k (segRD Fc ks m)).2.2.2.2).map (TE.MP m hTEm).sem).length = k + 1 := by
      simp only [List.length_map]
      rw [sum_fin_getD segs (segRD Fc ks m) (fun sg ↦ sg.2.2.2.2.length) hq]
      exact hk1.symm
    exact S₁.unitsSpan_multiR hgeo' (fun k ↦ (segs.getD k (segRD Fc ks m)).1) hePos
      (fun k ↦ (segs.getD k (segRD Fc ks m)).2.1) hgcd hdecS
      (fun k ↦ (segs.getD k (segRD Fc ks m)).2.2.1)
      (fun k ↦ (TE.MP m hTEm).sem (segs.getD k (segRD Fc ks m)).2.2.2.1) hcne
      (fun k ↦ loRC segs k) (fun k ↦ ((segs.getD k (segRD Fc ks m)).2.2.2.2).map (TE.MP m hTEm).sem)
      hΓ hbd hres htop hchain hlast hcount u0T hu00 hfin0 hindU
  obtain ⟨κ, ℓ₀, hκ, hℓ₀⟩ := S₁.nk_liouville_units_spanR (K := AlgebraicClosure (TE.F m))
    (Polynomial.C η₁) hx hK hnd u0T hspan hu00 hfin0 hindU
    hconstC (ψ f) hfT hresid s' c u
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
  set fc : ℕ → E₁ := fun j ↦ TE.evP m (fp.getD j []) / TE.evP m D - ∑ i : Fin k, κE i * G i j with hfc
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
    hdx fc (fun j ↦ sub_mem ((TE.mem_F_succ).mp (div_mem (TE.evP_mem m (TE.ev_mem m) _)
      (TE.evP_mem m (TE.ev_mem m) _)))
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
    have h1 := (M1.isZero_iff _).mp (unitsC_spec hU i i.2).2.2.2
    rw [TE.sem_nkTau m n hTE (gls.getD i []) s] at h1
    have hn' : ((n : ℕ) : TE.F (m + 1)) ≠ 0 := by exact_mod_cast hn0.ne'
    have h2 : ∑ j ∈ Finset.range n, M1.sem ((gls.getD i []).getD j O1.zero) *
        M1.sem (s.getD j O1.zero) = 0 :=
      (mul_eq_zero.mp h1).resolve_right (inv_ne_zero hn')
    have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) h2
    simpa only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
      ZeroMemClass.coe_zero] using this
  have hτf : ∑ j ∈ Finset.range n, fc j * ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) =
      ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) / TE.evP m D *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) := by
    simp only [hfc, sub_mul, Finset.sum_sub_distrib]
    rw [hκsum, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin k))) fun i _ ↦ by
      rw [hτ0 i, mul_zero], sub_zero]
  rw [hτf] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) / TE.evP m D *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFlR m hTE fp D j]
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
    have hiff := TE.exactTLVG_correct m hTE (by omega) hk (hTE m (by omega)) (prdeC Fc ks lv m)
      MSEm.rde dg C Ci r (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind Tc Ti gls res hres
    set c' := fun i ↦ if h : i < k then c0 ⟨i, h⟩ else 0 with hc'
    refine hiff.mpr ⟨c', fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [TE.sum_nkRestR m hTE n hn0, hTEev (m + 1) q]
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



/-- **`⇐`** (several places at infinity, non-constant curves, `exactTLV`). -/
theorem nk_sufficientInfVGR (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ)
    (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m)) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) gls = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) := by
  classical
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind' : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact hind
  have hiff := T.exactTLVG_correct m h1 hm hk htr rde hrde dg C Ci r (nkPC Fc ks m Pp) _ θ hP hind' Tc Ti
    gls res hres
  obtain ⟨c, Y, hY⟩ := hiff.mp hr
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set u : ℕ → L := fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) with hu
  have hui : ∀ i < gls.length, u i ≠ 0 ∧ T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i := by
    intro i hi
    obtain ⟨huv, hgl, -, -⟩ := unitsC_spec hU i hi
    have huvL := T.unitC_sound m h1 θ Pp _ _ hP huv
    exact ⟨left_ne_zero_of_mul_eq_one huvL, T.logDerChk_sound m h1 θ Pp _ _ _ dθ wθ hP huvL hgl⟩
  have hg : ∑ j ∈ Finset.range Pp.length, (∑ i ∈ Finset.range gls.length, algebraMap Cc L (c i) *
      ((M1.sem ((gls.getD i []).getD j O1.zero) : T.F (m + 1)) : L)) * θ ^ j =
      ∑ i ∈ Finset.range gls.length, algebraMap Cc L (c i) * logDeriv (u i) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [logDeriv, ← (hui i hi').2, T.evθ_list_le m h1 θ _ Pp.length (unitsC_spec hU i hi').2.2.1,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlen] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRestR m h1 Pp.length hn0] at hY
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ +
          ((List.range gls.length).map fun i ↦ algebraMap Cc L (c i) * logDeriv (u i)).sum by
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, hY]; ring]
  refine (hq.add_in (hasElementaryIntegralIn_deriv _)).add_in ?_
  exact hasElementaryIntegralIn_logSum (fun i ↦ algebraMap Cc L (c i)) u (List.range gls.length)
    (fun i hi ↦ ⟨by rw [deriv_algebraMap, T.hC, map_zero], (hui i (List.mem_range.mp hi)).1⟩)

/-- **The decision with several places at infinity for non-constant curves** (logarithmic
level; Eisenstein certificate, `n − 1` units `uᵢ` with `τ(uᵢ′/uᵢ) = 0`, independent by
`indepC`). -/
theorem nk_iffInfVMRR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (hk1 : gls.length + 1 = nPlacesR segs)
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (J : List ℕ) (H : List (List (LC (m + 1)))) (hJH : indepC Fc ks m gls J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ)
    (hres : exactTLVG Fc ks m η (prdeC Fc ks lv m) dg C Ci r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) gls =
        some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) := by
  refine ⟨T.nk_necessaryInfVMRR hmon hdeg m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ Us Vs gls hk1 dθ wθ
    s hU J H hJH hθ hgen hs fp D hsq kc U hcert hfpl Tc Ti res dg C Ci r hres, fun h ↦ ?_⟩
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  exact T.nk_sufficientInfVGR m hTr (by omega) hk (hTr m (by omega)) (prdeC Fc ks lv m) MSm.rde dg C Ci r
    Pp (by
      unfold multiShapeRC at hms
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
      exact hms.1.1.1.1) θ hθ (T.nkCurveE_ind m hTr Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hU
    fp D Tc Ti res hres h.1 h.2

end MTower

end Curves.MT
