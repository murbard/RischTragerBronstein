import RischTragerBronstein.Mixed.NKLogDecideTV
import RischTragerBronstein.Mixed.NKLogRes

/-!
# A single place at infinity with residue-free finite poles, with `exactTV`

`nk_iffTVR`: `nk_iffTV` for integrands `∑ bⱼ(t)/D(t) θʲ` with residue-free poles (`resCert`): the
logarithmic part lies in `Fₘ` (`nk_liouvilleR`), and `exactTV` answers for any right-hand side.
The constructive counterpart of `nk_iffR` (whose exact part uses `exactG`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Differential

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`⇐`**: an exact `f − τ(f)/n` and an elementary `τ(f)/n` give an elementary `f`. -/
theorem nk_sufficientTVR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (D : GPoly (LC m)) (dg : List (FRep (LC m))) (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTV Fc ks m η (prdeC Fc ks lv m) dg r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hn0 := (T.nkShape_spec m hTr.of_succ Pp hsh).1
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact T.nkCurve_ind m hTr Pp hsh θ hθ
  have hiff := T.exactTV_correct hTr (by omega) hk (hTr m (by omega)) (prdeC Fc ks lv m) MSm.rde dg r
    (nkPC Fc ks m Pp) _ θ hP hind Tc Ti res hres
  obtain ⟨Y, hY⟩ := hiff.mp hr
  rw [hlen, T.sum_nkRestR m hTr Pp.length hn0] at hY
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ by rw [hY]; ring]
  exact hq.add_in (hasElementaryIntegralIn_deriv _)

set_option maxHeartbeats 16000000 in
/-- **`⇒`**: an elementary `f` has an exact `f − τ(f)/n` and an elementary `τ(f)/n` (the
logarithmic part of a Liouville form lies in `Fₘ`, and `τ` is `n` on `Fₘ`). -/
theorem nk_necessaryTVR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (dg : List (FRep (LC m))) (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTV Fc ks m η (prdeC Fc ks lv m) dg r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) := by
  classical
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
  set S₁ := TE.nkCurve m hTE Pp hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec m hTEm Pp hsh
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
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  obtain ⟨ℓ₀, hℓ₀⟩ := S₁.nk_liouvilleR (K := AlgebraicClosure (TE.F m)) (Polynomial.C η₁) hx hK hnd
    n _ hS₁F hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 hconstC (ψ f) hfT hresid s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  -- the trace
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  obtain ⟨hs0, hτ⟩ := TE.traceC_sound m hTE Pp (ψ θ) hPθE s hs
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
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
    hdx (fun j ↦ TE.evP m (fp.getD j []) / TE.evP m D) (fun j ↦ (TE.mem_F_succ).mp
      (div_mem (TE.evP_mem m (TE.ev_mem m) _) (TE.evP_mem m (TE.ev_mem m) _)))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) / TE.evP m D * (ψ θ) ^ j = _
      rw [← hψf]; exact hℓ₀)
  rw [hS₁F] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) / TE.evP m D *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFlR m hTE fp D j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ = ∑ i ∈ s', c i * logDeriv (u i) := by
    have := hℓ₀.symm.trans heq₁
    exact add_left_cancel this
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
      rw [hlen]; exact TE.nkCurve_ind m hTE Pp hsh (ψ θ) hθE
    have hiff := TE.exactTV_correct hTE (by omega) hk (hTE m (by omega)) (prdeC Fc ks lv m) MSEm.rde dg r
      (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind Tc Ti res hres
    refine hiff.mpr ⟨fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen, TE.sum_nkRestR m hTE n hsp.1, hTEev (m + 1) q]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map fun i ↦ (c i, u i) with hl0
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

/-- **The logarithmic part over a non-Kummer extension of a logarithmic level**: for
`θⁿ + ∑ aᵢ(t) θⁱ = 0` with a single place at infinity and `f = ∑ bⱼ(t) θʲ`, `f` has an elementary
integral iff `f − τ(f)/n` is exact (`exactC`) and `τ(f)/n ∈ Fₘ₊₁` has one. -/
theorem nk_iffTVR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp fp D kc U = true) (hfpl : fp.length = Pp.length)
    (dg : List (FRep (LC m))) (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTV Fc ks m η (prdeC Fc ks lv m) dg r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFlR m fp D) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) / T.evP m D * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m fp D) s)) :=
  ⟨T.nk_necessaryTVR hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp D hsq kc U hcert hfpl dg r Tc Ti res hres,
    fun h ↦ T.nk_sufficientTVR hmon hdeg m hn hc hk Pp hsh θ hθ s fp D dg r Tc Ti res hres h.1 h.2⟩

end MTower

end Curves.MT
