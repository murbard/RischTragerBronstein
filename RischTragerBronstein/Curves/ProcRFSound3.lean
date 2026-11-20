import RischTragerBronstein.Curves.ProcRFSound2

/-!
# The rows versus simple poles along a certified branch

Along a certified branch (finite, or above infinity), for `v = ∑ c_b b`:
`φ(f) dX̂/dT − (φ v)′` has at most a simple pole **iff** the rows at that branch are satisfied by
`c` (`certFin_simple`/`rowFin_of_simple`, `certInf_simple`/`rowInf_of_simple`).
Below the smallest row index the coefficients vanish by the pole bounds of `phi_repr`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Cert

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L] [Field K]
  [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma lb_phiFin (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (a : F) (N : ℕ) (hN : 0 < N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0)
    (yt : CPoly F) (prec : ℕ)
    (hy : (PowerSeries.X : PowerSeries K) ^ prec ∣ Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (z : C⟮S.x⟯⟮S.y⟯) (W : BPoly F) (Q : CPoly F)
    (hz : (z : L) * aeval S.x ((toPoly Q).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀)))
    (hμ : ordC (compC Q (shiftC a N)) < (compC Q (shiftC a N)).length) :
    LowerBd (S.embG (branchSub N (algebraMap C K (ψ₀ a))) (branchSub_injective N hN _)
      (HahnSeries.ofPowerSeries ℤ K Y) hY z) (-(ordC (compC Q (shiftC a N)) : ℤ)) := by
  obtain ⟨V, hV, -⟩ := S.phi_repr Fc ψ₀ hSF a N hN Y hY yt prec hy z W Q hz hμ
  rw [hV]
  have := (lowerBd_single (-(ordC (compC Q (shiftC a N)) : ℤ)) (1 : K)).mul (lowerBd_ofPS V)
  rwa [add_zero] at this

lemma lb_phiInf (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (k N : ℕ) (hN : 0 < N) (w : PowerSeries K)
    (hY : (S.F.map (infSub N)).eval
      (single (-((k * N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F) (prec : ℕ)
    (hw : (PowerSeries.X : PowerSeries K) ^ prec ∣ w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt))
    (z : C⟮S.x⟯⟮S.y⟯) (W : BPoly F) (Q : CPoly F)
    (hz : (z : L) * aeval S.x ((toPoly Q).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀)))
    (DW : ℕ) (hWok : InvOK k DW 0 W) (hQ : 0 < Q.length) (hQl : Q.getD (Q.length - 1) 0 ≠ 0) :
    LowerBd (S.embG (infSub N) (infSub_injective N hN)
        (single (-((k * N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY z)
      (-((N * DW : ℕ) : ℤ) + ((N * (Q.length - 1) : ℕ) : ℤ)) := by
  obtain ⟨V, hV, -⟩ := S.phi_repr_inf Fc ψ₀ hSF k N hN w hY wt prec hw z W Q hz DW hWok hQ hQl
  rw [hV]
  have := (lowerBd_single (-((N * DW : ℕ) : ℤ) + ((N * (Q.length - 1) : ℕ) : ℤ)) (1 : K)).mul
    (lowerBd_ofPS V)
  rwa [add_zero] at this

/-- A lower bound for `φ(∑ c_b b)` from lower bounds of the basis elements. -/
lemma lb_lcomb (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C K c))
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (nb : ℕ) (cv : ℕ → C)
    (bE : ℕ → C⟮S.x⟯⟮S.y⟯) (m : ℤ) (hbd : ∀ b < nb, LowerBd (S.embG g hg Y hY (bE b)) m) :
    LowerBd (S.embG g hg Y hY (∑ b ∈ Finset.range nb, S.cst (cv b) * bE b)) m := by
  rw [map_sum]
  refine lowerBd_sum _ _ fun b hb ↦ ?_
  rw [map_mul, S.embG_cst _ _ hgC]
  have := (lowerBd_C (algebraMap C K (cv b))).mul (hbd b (Finset.mem_range.mp hb))
  rwa [zero_add] at this

/-- **Rows ⇒ simple poles** along a certified finite branch. -/
theorem certFin_simple (P : CurveProb F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (a : F) (c : BranchCert F) (hN : 0 < c.N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub c.N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0) (yt : CPoly F)
    (hy : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (hpr : P.muFin a c.N < c.prec ∧ P.mufFin a c.N < c.prec + c.N ∧
      P.muFin a c.N < (P.QFin a c.N).length ∧ P.mufFin a c.N < (P.QfFin a c.N).length)
    (f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀)))
    (bE : ℕ × ℕ → C⟮S.x⟯⟮S.y⟯)
    (hbE : ∀ ie, (bE ie : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)))
    (cv : ℕ → C)
    (hrows : ∀ j : ℤ, P.jminFin a c ≤ j → j ≤ -2 →
      ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ ((P.rowFinAt a c yt j).1.getD b 0) =
        ψ₀ (P.rowFinAt a c yt j).2) :
    LowerBd (S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
        (HahnSeries.ofPowerSeries ℤ K Y) hY f *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ₀ a)) + single (c.N : ℤ) (1 : K)) -
      LaurentSeries.derivation (S.embG (branchSub c.N (algebraMap C K (ψ₀ a)))
        (branchSub_injective c.N hN _) (HahnSeries.ofPowerSeries ℤ K Y) hY
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1) := by
  obtain ⟨hμ, hμf, hQl, hQfl⟩ := hpr
  intro j hj
  by_cases hjm : P.jminFin a c ≤ j
  · rw [S.rowFin_sem P ψ₀ hSF a c hN Y hY yt hy hμ hμf hQl hQfl f hf bE hbE cv _ rfl j hjm
      (by omega), sub_eq_zero]
    have := congrArg (algebraMap C K) (hrows j hjm (by omega))
    rw [map_sum] at this
    simp only [RingHom.comp_apply]
    rw [← this]
    simp only [map_mul]
  · -- below `jmin`: the pole bounds
    have hf' := S.lb_phiFin P.Fc ψ₀ hSF a c.N hN Y hY yt c.prec hy f P.A P.D hf hQfl
    have hv' := S.lb_lcomb _ (branchSub_injective c.N hN _) (fun c' ↦ branchSub_C' _ _ c') _ hY
      P.basisIdx.length cv (fun b ↦ bE (P.basisIdx.getD b (0, 0)))
      (-(P.muFin a c.N : ℤ)) fun b _ ↦
        S.lb_phiFin P.Fc ψ₀ hSF a c.N hN Y hY yt c.prec hy _ _ _ (hbE _) hQl
    have h1 := hf'.mul (lowerBd_single ((c.N : ℤ) - 1) (c.N : K))
    have h2 := hv'.derivative
    rw [← LaurentSeries.derivation_apply] at h2
    rw [SuperData.derivation_branchX c.N hN]
    have h3 := (h1.mono (m' := P.jminFin a c) (by
      simp only [CurveProb.jminFin, CurveProb.mufFin, CurveProb.QfFin]; omega)).sub
      (h2.mono (m' := P.jminFin a c) (by
        simp only [CurveProb.jminFin, CurveProb.muFin, CurveProb.QFin]; omega))
    exact h3 j (by omega)

/-- **Simple poles ⇒ rows** along a certified finite branch. -/
theorem rowFin_of_simple (P : CurveProb F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (a : F) (c : BranchCert F) (hN : 0 < c.N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub c.N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0) (yt : CPoly F)
    (hy : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (hpr : P.muFin a c.N < c.prec ∧ P.mufFin a c.N < c.prec + c.N ∧
      P.muFin a c.N < (P.QFin a c.N).length ∧ P.mufFin a c.N < (P.QfFin a c.N).length)
    (f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀)))
    (bE : ℕ × ℕ → C⟮S.x⟯⟮S.y⟯)
    (hbE : ∀ ie, (bE ie : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)))
    (cv : ℕ → C)
    (hlb : LowerBd (S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
        (HahnSeries.ofPowerSeries ℤ K Y) hY f *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ₀ a)) + single (c.N : ℤ) (1 : K)) -
      LaurentSeries.derivation (S.embG (branchSub c.N (algebraMap C K (ψ₀ a)))
        (branchSub_injective c.N hN _) (HahnSeries.ofPowerSeries ℤ K Y) hY
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1))
    (j : ℤ) (hj1 : P.jminFin a c ≤ j) (hj2 : j ≤ -2) :
    ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ ((P.rowFinAt a c yt j).1.getD b 0) =
      ψ₀ (P.rowFinAt a c yt j).2 := by
  obtain ⟨hμ, hμf, hQl, hQfl⟩ := hpr
  have h := hlb j (by omega)
  rw [S.rowFin_sem P ψ₀ hSF a c hN Y hY yt hy hμ hμf hQl hQfl f hf bE hbE cv _ rfl j hj1 hj2,
    sub_eq_zero] at h
  apply (algebraMap C K).injective
  rw [map_sum]
  simp only [RingHom.comp_apply] at h
  rw [h]
  simp only [map_mul]

/-- **Rows ⇒ simple poles** along a certified branch above infinity. -/
theorem certInf_simple (P : CurveProb F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hN : 0 < P.inf.N) (w : PowerSeries K)
    (hY : (S.F.map (infSub P.inf.N)).eval
      (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F)
    (hw : (PowerSeries.X : PowerSeries K) ^ P.inf.prec ∣
      w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt))
    (hsb : -P.sbInf ≤ P.inf.prec) (hsf : (P.inf.N : ℤ) - P.sfInf < P.inf.prec)
    (hR0 : 0 < (trim P.R0).length) (hD0 : 0 < (trim P.D).length)
    (hAok : InvOK P.k P.DA 0 P.A)
    (hBok : ∀ b : ℕ, b < P.basisIdx.length → InvOK P.k P.DWb 0
      (basisB (F := F) (P.basisIdx.getD b (0, 0)).1 (P.basisIdx.getD b (0, 0)).2))
    (f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀)))
    (bE : ℕ × ℕ → C⟮S.x⟯⟮S.y⟯)
    (hbE : ∀ ie, (bE ie : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)))
    (cv : ℕ → C)
    (hrows : ∀ j : ℤ, P.jminInf ≤ j → j ≤ -2 →
      ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ ((P.rowInfAt wt j).1.getD b 0) =
        ψ₀ (P.rowInfAt wt j).2) :
    LowerBd (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY f *
        LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : K)) -
      LaurentSeries.derivation (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1) := by
  intro j hj
  by_cases hjm : P.jminInf ≤ j
  · rw [S.rowInf_sem P ψ₀ hSF hN w hY wt hw hsb hsf hR0 hD0 hAok hBok f hf bE hbE cv _ rfl j
      (by omega), sub_eq_zero]
    have := congrArg (algebraMap C K) (hrows j hjm (by omega))
    rw [map_sum] at this
    simp only [RingHom.comp_apply]
    rw [← this]
    simp only [map_mul]
  · have hfD : (f : L) * aeval S.x ((toPoly (trim P.D)).map ψ₀) =
        S.evXY ((toB P.A).map (mapRingHom ψ₀)) := by rw [toPoly_trim]; exact hf
    have hf' := S.lb_phiInf P.Fc ψ₀ hSF P.k P.inf.N hN w hY wt P.inf.prec hw f P.A (trim P.D)
      hfD P.DA hAok hD0 (getD_trim_last _ hD0)
    have hv' := S.lb_lcomb _ (infSub_injective P.inf.N hN) (fun c' ↦ is_C _ c') _ hY
      P.basisIdx.length cv (fun b ↦ bE (P.basisIdx.getD b (0, 0)))
      (-((P.inf.N * P.DWb : ℕ) : ℤ) + ((P.inf.N * ((trim P.R0).length - 1) : ℕ) : ℤ))
      fun b hb ↦ S.lb_phiInf P.Fc ψ₀ hSF P.k P.inf.N hN w hY wt P.inf.prec hw _ _ (trim P.R0)
        (by rw [toPoly_trim]; exact hbE _) P.DWb (hBok b hb) hR0 (getD_trim_last _ hR0)
    have h1 := hf'.mul (lowerBd_single (-(P.inf.N : ℤ) - 1) (-(P.inf.N : K)))
    have h2 := hv'.derivative
    rw [← LaurentSeries.derivation_apply] at h2
    rw [SuperData.derivation_infX]
    have h3 := (h1.mono (m' := P.jminInf) (by
      simp only [CurveProb.jminInf, CurveProb.sfInf, degT]; omega)).sub
      (h2.mono (m' := P.jminInf) (by
        simp only [CurveProb.jminInf, CurveProb.sbInf, degT]; omega))
    exact h3 j (by omega)

/-- **Simple poles ⇒ rows** along a certified branch above infinity. -/
theorem rowInf_of_simple (P : CurveProb F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hN : 0 < P.inf.N) (w : PowerSeries K)
    (hY : (S.F.map (infSub P.inf.N)).eval
      (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F)
    (hw : (PowerSeries.X : PowerSeries K) ^ P.inf.prec ∣
      w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt))
    (hsb : -P.sbInf ≤ P.inf.prec) (hsf : (P.inf.N : ℤ) - P.sfInf < P.inf.prec)
    (hR0 : 0 < (trim P.R0).length) (hD0 : 0 < (trim P.D).length)
    (hAok : InvOK P.k P.DA 0 P.A)
    (hBok : ∀ b : ℕ, b < P.basisIdx.length → InvOK P.k P.DWb 0
      (basisB (F := F) (P.basisIdx.getD b (0, 0)).1 (P.basisIdx.getD b (0, 0)).2))
    (f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀)))
    (bE : ℕ × ℕ → C⟮S.x⟯⟮S.y⟯)
    (hbE : ∀ ie, (bE ie : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)))
    (cv : ℕ → C)
    (hlb : LowerBd (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY f *
        LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : K)) -
      LaurentSeries.derivation (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1))
    (j : ℤ) (hj2 : j ≤ -2) :
    ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ ((P.rowInfAt wt j).1.getD b 0) =
      ψ₀ (P.rowInfAt wt j).2 := by
  have h := hlb j (by omega)
  rw [S.rowInf_sem P ψ₀ hSF hN w hY wt hw hsb hsf hR0 hD0 hAok hBok f hf bE hbE cv _ rfl j hj2,
    sub_eq_zero] at h
  apply (algebraMap C K).injective
  rw [map_sum]
  simp only [RingHom.comp_apply] at h
  rw [h]
  simp only [map_mul]

end CurveData

end Cert

end Curves
