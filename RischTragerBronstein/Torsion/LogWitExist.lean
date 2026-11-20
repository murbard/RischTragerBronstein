import RischTragerBronstein.Torsion.RaiseValid
import RischTragerBronstein.Torsion.LinDescent
import RischTragerBronstein.Torsion.Exact
import RischTragerBronstein.Curves.ReprPoles
import RischTragerBronstein.Curves.ProcLogSem4
import RischTragerBronstein.Curves.Abel
import RischTragerBronstein.Algebraic.SuperDecide

/-!
# Existence of logarithmic witnesses (in progress)

Toward **`CertExists`** in the torsion case: when the residue divisor coordinates are torsion (in
particular for every elementary integrand, by `curve_abel`), witnesses passing `witOK` exist.

* `witOK_of_facts`: the converse of `witOK_spec`;
* `res_fE_regular`: along every branch above a point where `D ≠ 0`, the residue of `f dX` vanishes.
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Facts

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **The converse of `witOK_spec`.** -/
lemma CurveProb.witOK_of_facts (P : CurveProb F) (w : LogWit F) (j : Fin (dim F))
    (h : P.WitFacts w j) : P.witOK w j = true := by
  obtain ⟨hm, hQ, hfin, hinf, hcov⟩ := h
  simp only [CurveProb.witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true]
  refine ⟨⟨⟨⟨hm, ?_⟩, hfin⟩, hinf⟩, hcov⟩
  cases h0 : isZero w.Q
  · rfl
  · exact absurd ((isZero_iff _).mp h0) hQ

end Facts

section OrdComplete

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

/-- **`ordWFin` finds the order below the precision.** -/
theorem ordWFin_of_order (ψ : F →+* K) (W : BPoly F) (a : F) (c : BranchCert F) (yt : CPoly F)
    (ρ : PowerSeries K)
    (hy : (PowerSeries.X : PowerSeries K) ^ c.prec ∣ ρ - thetaT ψ (toPoly yt)) (o : ℕ)
    (ho : o < c.prec)
    (hz : ∀ t < o, PowerSeries.coeff t (((toB W).map (thetaN ψ a c.N)).eval ρ) = 0)
    (hne : PowerSeries.coeff o (((toB W).map (thetaN ψ a c.N)).eval ρ) ≠ 0) :
    ordWFin W a c yt = some o := by
  set V := bivEval W (shiftC a c.N) yt with hV
  have hdv : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      ((toB W).map (thetaN ψ a c.N)).eval ρ - thetaT ψ (toPoly V) := by
    rw [hV, thetaT_bivEval]; exact hy.trans (sub_dvd_eval_sub _ _ _)
  have hco : ∀ t < c.prec, ψ (V.getD t 0) =
      PowerSeries.coeff t (((toB W).map (thetaN ψ a c.N)).eval ρ) := fun t ht ↦ by
    have := (PowerSeries.X_pow_dvd_iff.mp hdv) t ht
    rw [map_sub, coeff_thetaT, sub_eq_zero] at this
    exact this.symm
  have h0 : ∀ t < o, V.getD t 0 = 0 := fun t ht ↦ ψ.injective (by
    rw [hco t (by omega), hz t ht, map_zero])
  have h1 : V.getD o 0 ≠ 0 := fun h ↦ hne (by rw [← hco o ho, h, map_zero])
  have hord : ordC V = o := ordC_eq_of h0 h1
  have hlen : o < V.length := by
    by_contra hle; exact h1 (List.getD_eq_default _ _ (by omega))
  simp only [ordWFin, ← hV, hord]
  rw [if_pos ⟨ho, hlen⟩]

/-- **`ordWInf` finds the order below the precision.** -/
theorem ordWInf_of_order (ψ : F →+* K) (W : BPoly F) (k : ℕ) (c : BranchCert F) (wt : CPoly F)
    (w : PowerSeries K)
    (hw : (PowerSeries.X : PowerSeries K) ^ c.prec ∣ w - thetaT ψ (toPoly wt)) (o : ℕ)
    (ho : o < c.prec)
    (hz : ∀ t < o, PowerSeries.coeff t
      (((toB (invB W k (invDeg W k))).map (thetaN ψ 0 c.N)).eval w) = 0)
    (hne : PowerSeries.coeff o (((toB (invB W k (invDeg W k))).map (thetaN ψ 0 c.N)).eval w) ≠ 0) :
    ordWInf W k c wt = some (-((c.N * invDeg W k : ℕ) : ℤ) + o) := by
  set V := bivEval (invB W k (invDeg W k)) (shiftC 0 c.N) wt with hV
  have hdv : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      ((toB (invB W k (invDeg W k))).map (thetaN ψ 0 c.N)).eval w - thetaT ψ (toPoly V) := by
    rw [hV, thetaT_bivEval]; exact hw.trans (sub_dvd_eval_sub _ _ _)
  have hco : ∀ t < c.prec, ψ (V.getD t 0) = PowerSeries.coeff t
      (((toB (invB W k (invDeg W k))).map (thetaN ψ 0 c.N)).eval w) := fun t ht ↦ by
    have := (PowerSeries.X_pow_dvd_iff.mp hdv) t ht
    rw [map_sub, coeff_thetaT, sub_eq_zero] at this
    exact this.symm
  have h0 : ∀ t < o, V.getD t 0 = 0 := fun t ht ↦ ψ.injective (by
    rw [hco t (by omega), hz t ht, map_zero])
  have h1 : V.getD o 0 ≠ 0 := fun h ↦ hne (by rw [← hco o ho, h, map_zero])
  have hord : ordC V = o := ordC_eq_of h0 h1
  have hlen : o < V.length := by
    by_contra hle; exact h1 (List.getD_eq_default _ _ (by omega))
  simp only [ordWInf, ← hV, hord]
  rw [if_pos ⟨ho, hlen⟩]

end OrdComplete

section Assemble

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **A witness passes `witOK` when its exact orders along the certified branches are the
prescribed ones** (orders read over `F` along exact roots through the approximations). -/
theorem witOK_of_orders {K : Type*} [Field K] (ψ : F →+* K) (P : CurveProb F) (w : LogWit F) (j : Fin (dim F)) (hm : 0 < w.m)
    (hQ : toPoly w.Q ≠ 0)
    (hfin : ∀ ac ∈ P.pts, ∀ yt ∈ ac.2.ys, ∃ ρ : PowerSeries K,
      (PowerSeries.X : PowerSeries K) ^ ac.2.prec ∣ ρ - thetaT ψ (toPoly yt) ∧
      ∃ o : ℕ, o < ac.2.prec ∧
        (∀ t < o, PowerSeries.coeff t (((toB w.W).map (thetaN ψ ac.1 ac.2.N)).eval ρ) = 0) ∧
        PowerSeries.coeff o (((toB w.W).map (thetaN ψ ac.1 ac.2.N)).eval ρ) ≠ 0 ∧
        (((o : ℤ) - ordQFin w.Q ac.1 ac.2.N : ℚ) = w.m * coord j (P.resFin ac.1 ac.2 yt)))
    (hinf : ∀ wt ∈ P.inf.ys, ∃ ρ : PowerSeries K,
      (PowerSeries.X : PowerSeries K) ^ P.inf.prec ∣ ρ - thetaT ψ (toPoly wt) ∧
      ∃ o : ℕ, o < P.inf.prec ∧
        (∀ t < o, PowerSeries.coeff t
          (((toB (invB w.W P.k (invDeg w.W P.k))).map (thetaN ψ 0 P.inf.N)).eval ρ) = 0) ∧
        PowerSeries.coeff o
          (((toB (invB w.W P.k (invDeg w.W P.k))).map (thetaN ψ 0 P.inf.N)).eval ρ) ≠ 0 ∧
        (((-((P.inf.N * invDeg w.W P.k : ℕ) : ℤ) + o) + ((P.inf.N * degT w.Q : ℕ) : ℤ) : ℚ) =
          w.m * coord j (P.resInf wt)))
    (hcov : coverCheck (mul (normRC P.Fc w.W P.n P.k) w.Q) (P.pts.map Prod.fst) = true) :
    P.witOK w j = true := by
  refine P.witOK_of_facts w j ⟨hm, hQ, fun ac hac yt hyt ↦ ?_, fun wt hwt ↦ ?_, hcov⟩
  · obtain ⟨ρ, hρ, o, ho, hz, hne, heq⟩ := hfin ac hac yt hyt
    simp only [CurveProb.witFinOK, ordWFin_of_order ψ w.W ac.1 ac.2 yt ρ hρ o ho hz hne,
      decide_eq_true_eq]
    exact heq
  · obtain ⟨ρ, hρ, o, ho, hz, hne, heq⟩ := hinf wt hwt
    simp only [CurveProb.witInfOK, ordWInf_of_order ψ w.W P.k P.inf wt ρ hρ o ho hz hne,
      decide_eq_true_eq]
    push_cast at heq ⊢
    exact heq

end Assemble

section Regular

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [CharZero C]
  [CharZero K] [CharZero L]

namespace CurveData

variable (S : CurveData C L)

/-- **No residue where the integrand is regular**: along a branch above `a` with `D(a) ≠ 0`. -/
theorem res_fE_regular {F : Type*} [Field F] [DecidableEq F] (P : CurveProb F) (ψ₀ : F →+* C)
    (hD0 : toPoly P.D ≠ 0) (a : K)
    (hDa : ((toPoly P.D).map ψ₀ |>.map (algebraMap C K)).eval a ≠ 0) (N : ℕ) (hN : 0 < N)
    (r : LaurentSeries K) (hr : (S.F.map (branchSub N a)).eval r = 0) :
    LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N hN a) r hr (S.fE P ψ₀) *
      LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))) = 0 := by
  refine res_eq_zero_of_order _ ?_
  set g := branchSub (C := C) (K := K) N a
  have hg := branchSub_injective (C := C) (K := K) N hN a
  have hDψ : (toPoly P.D).map ψ₀ ≠ 0 := by rw [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact hD0
  have hfD : (S.fE P ψ₀ : L) * aeval S.x ((toPoly P.D).map ψ₀) =
      S.evXY ((toB P.A).map (mapRingHom ψ₀)) := div_mul_cancel₀ _ (S.aeval_x_ne_zero _ hDψ)
  have hW := S.eval_W_branch g hg r hr (S.fE P ψ₀) _ _ hfD
  have hgD : (g ((toPoly P.D).map ψ₀)).order = 0 :=
    CurveData.order_branchSub_eq_zero _ a N hN hDa
  have hgD0 : g ((toPoly P.D).map ψ₀) ≠ 0 := (map_ne_zero_iff _ hg).mpr hDψ
  have hAr : 0 ≤ ((((toB P.A).map (mapRingHom ψ₀)).map g).eval r).order :=
    order_nonneg_of_lowerBd _ (CurveData.lowerBd_eval _ r 0 le_rfl (S.fin_root_lowerBd N a r hr) 0
      fun i ↦ by rw [zero_mul, sub_zero, coeff_map]; exact CurveData.lowerBd_branchSub_nonneg N a _)
  have hdX : 0 ≤ (LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))).order := by
    rw [SuperData.derivation_branchX N hN a]
    have h0 : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [order_single h0]; omega
  set e := S.embG g hg r hr (S.fE P ψ₀)
  by_cases he : e = 0
  · rw [he, zero_mul, order_zero]
  by_cases hd : LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K)) = 0
  · rw [hd, mul_zero, order_zero]
  rw [order_mul he hd]
  have : (((toB P.A).map (mapRingHom ψ₀)).map g).eval r ≠ 0 := by
    rw [hW]; exact mul_ne_zero he hgD0
  have ho : ((((toB P.A).map (mapRingHom ψ₀)).map g).eval r).order = e.order := by
    rw [hW, order_mul he hgD0, hgD, add_zero]
  linarith

end CurveData

end Regular

end Curves
