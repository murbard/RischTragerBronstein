import RischTragerBronstein.Curves.ProcRFSem2

/-!
# The rows along certified branches

`rowFin_sem`: along a certified finite branch, for `j ∈ [jmin, −2]` the `T^j` coefficient of
`φ(f) dX̂/dT − (φ v)′` (for `v = ∑ c_b b`) is the computed row evaluated at `c`.
`rowInf_sem`: the same above infinity. `resFin_sem`, `resInf_sem`: the residues.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Sem3

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L] [Field K]
  [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- A constant as an element of `C⟮x⟯⟮y⟯`. -/
def cst (c : C) : C⟮S.x⟯⟮S.y⟯ :=
  ⟨algebraMap C L c, IntermediateField.algebraMap_mem _
    (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮S.x⟯)⟩

lemma embG_cst (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C K c))
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (c : C) :
    S.embG g hg Y hY (S.cst c) = HahnSeries.C (algebraMap C K c) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have e : S.cst c = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ (Polynomial.C c)) :=
    Subtype.ext (by
      show algebraMap C L c = ((algebraMap C[X] C⟮S.x⟯ (Polynomial.C c) : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple, aeval_C])
  rw [e, S.embG_algebraMap, S.embXG_algebraMap, hgC]

lemma branchSub_C' (N : ℕ) (a : K) (c : C) :
    branchSub N a (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := bs_C N a c

lemma coeff_C_mul' (c : K) (z : LaurentSeries K) (j : ℤ) :
    (HahnSeries.C c * z).coeff j = c * z.coeff j := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/-- **The finite row identity.** -/
theorem rowFin_sem (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (a : F) (c : BranchCert F) (hN : 0 < c.N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub c.N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0) (yt : CPoly F)
    (hy : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (hμ : P.muFin a c.N < c.prec) (hμf : P.mufFin a c.N < c.prec + c.N)
    (hQl : P.muFin a c.N < (P.QFin a c.N).length) (hQfl : P.mufFin a c.N < (P.QfFin a c.N).length)
    (f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀)))
    (bE : ℕ × ℕ → C⟮S.x⟯⟮S.y⟯)
    (hbE : ∀ ie, (bE ie : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)))
    (cv : ℕ → C) (v : C⟮S.x⟯⟮S.y⟯)
    (hv : v = ∑ b ∈ Finset.range P.basisIdx.length, S.cst (cv b) * bE (P.basisIdx.getD b (0, 0)))
    (j : ℤ) (hj1 : P.jminFin a c ≤ j) (hj2 : j ≤ -2) :
    (S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
        (HahnSeries.ofPowerSeries ℤ K Y) hY f *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ₀ a)) + single (c.N : ℤ) (1 : K)) -
      LaurentSeries.derivation (S.embG (branchSub c.N (algebraMap C K (ψ₀ a)))
        (branchSub_injective c.N hN _) (HahnSeries.ofPowerSeries ℤ K Y) hY v)).coeff j =
      (algebraMap C K).comp ψ₀ (P.rowFinAt a c yt j).2 -
        ∑ b ∈ Finset.range P.basisIdx.length,
          algebraMap C K (cv b) * (algebraMap C K).comp ψ₀ ((P.rowFinAt a c yt j).1.getD b 0) := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set φ := S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
    (HahnSeries.ofPowerSeries ℤ K Y) hY with hφ
  rw [SuperData.derivation_branchX c.N hN, HahnSeries.coeff_sub, mul_comm, coeff_single_mul',
    coeff_derivation]
  -- the `f` part
  have hfc := S.coeff_phi_fin (P.Fc) ψ₀ hSF a c.N hN Y hY yt c.prec hy f P.A P.D hf hQfl
    (j - ((c.N : ℤ) - 1)) (by
      have : (P.mufFin a c.N : ℤ) < c.prec + c.N := by exact_mod_cast hμf
      simp only [CurveProb.mufFin, CurveProb.QfFin] at this ⊢; omega)
  -- the `v` part
  have hvc : (φ v).coeff (j + 1) = ∑ b ∈ Finset.range P.basisIdx.length,
      algebraMap C K (cv b) * ψ (gi (P.VbFin a c yt (P.basisIdx.getD b (0, 0)))
        (j + 1 + P.muFin a c.N)) := by
    rw [hv, map_sum, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [map_mul, S.embG_cst _ _ (fun c' ↦ branchSub_C' _ _ c'), coeff_C_mul']
    congr 1
    exact S.coeff_phi_fin (P.Fc) ψ₀ hSF a c.N hN Y hY yt c.prec hy _ _ _ (hbE _) hQl (j + 1) (by
      have : (P.muFin a c.N : ℤ) < c.prec := by exact_mod_cast hμ
      simp only [CurveProb.muFin, CurveProb.QFin] at this ⊢; omega)
  have hrow2 : ψ (P.rowFinAt a c yt j).2 = (c.N : K) * ψ (gi (P.VfFin a c yt)
      (j - ((c.N : ℤ) - 1) + P.mufFin a c.N)) := by
    simp only [CurveProb.rowFinAt, map_mul, map_natCast]
    congr 3; ring
  have hrow1 : ∀ b ∈ Finset.range P.basisIdx.length, ψ ((P.rowFinAt a c yt j).1.getD b 0) =
      ((j + 1 : ℤ) : K) * ψ (gi (P.VbFin a c yt (P.basisIdx.getD b (0, 0)))
        (j + 1 + P.muFin a c.N)) := by
    intro b hb
    have hb' := Finset.mem_range.mp hb
    simp only [CurveProb.rowFinAt]
    rw [List.getD_eq_getElem _ _ (by simpa using hb'), List.getElem_map, map_mul, map_intCast,
      List.getD_eq_getElem _ _ hb']
  have hsumR : ∑ b ∈ Finset.range P.basisIdx.length,
      algebraMap C K (cv b) * ψ ((P.rowFinAt a c yt j).1.getD b 0) =
      ((j + 1 : ℤ) : K) * ∑ b ∈ Finset.range P.basisIdx.length, algebraMap C K (cv b) *
        ψ (gi (P.VbFin a c yt (P.basisIdx.getD b (0, 0))) (j + 1 + P.muFin a c.N)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb ↦ by rw [hrow1 b hb]; ring
  rw [hfc, hvc, hsumR, hrow2]
  simp only [CurveProb.VfFin, CurveProb.UfFin, CurveProb.mufFin, CurveProb.QfFin]
  rfl

lemma getD_trim_last (p : CPoly F) (h : 0 < (trim p).length) :
    (trim p).getD ((trim p).length - 1) 0 ≠ 0 := by
  obtain ⟨-, h1, h2⟩ := natDegree_toPoly_of_trim_ne_nil (List.ne_nil_of_length_pos h)
  rw [← h1, ← toPoly_trim, coeff_toPoly] at h2
  exact h2

/-- **The row identity above infinity.** -/
theorem rowInf_sem (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
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
    (cv : ℕ → C) (v : C⟮S.x⟯⟮S.y⟯)
    (hv : v = ∑ b ∈ Finset.range P.basisIdx.length, S.cst (cv b) * bE (P.basisIdx.getD b (0, 0)))
    (j : ℤ) (hj2 : j ≤ -2) :
    (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY f *
        LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : K)) -
      LaurentSeries.derivation (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY v)).coeff j =
      (algebraMap C K).comp ψ₀ (P.rowInfAt wt j).2 -
        ∑ b ∈ Finset.range P.basisIdx.length,
          algebraMap C K (cv b) * (algebraMap C K).comp ψ₀ ((P.rowInfAt wt j).1.getD b 0) := by
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set φ := S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
    (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY with hφ
  rw [SuperData.derivation_infX, HahnSeries.coeff_sub, mul_comm, coeff_single_mul',
    coeff_derivation]
  have hfD : (f : L) * aeval S.x ((toPoly (trim P.D)).map ψ₀) =
      S.evXY ((toB P.A).map (mapRingHom ψ₀)) := by rw [toPoly_trim]; exact hf
  have hfc := S.coeff_phi_inf P.Fc ψ₀ hSF P.k P.inf.N hN w hY wt P.inf.prec hw f P.A (trim P.D)
    hfD P.DA hAok hD0 (getD_trim_last _ hD0) (j - (-(P.inf.N : ℤ) - 1)) (by
      simp only [CurveProb.sfInf, degT] at hsf; push_cast at hsf ⊢; omega)
  have hvc : (φ v).coeff (j + 1) = ∑ b ∈ Finset.range P.basisIdx.length,
      algebraMap C K (cv b) * ψ (gi (P.VbInf wt (P.basisIdx.getD b (0, 0))) (j + 1 - P.sbInf)) := by
    rw [hv, map_sum, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [map_mul, S.embG_cst _ _ (fun c' ↦ is_C _ c'), coeff_C_mul']
    congr 1
    have hbR : (bE (P.basisIdx.getD b (0, 0)) : L) * aeval S.x ((toPoly (trim P.R0)).map ψ₀) =
        S.evXY ((toB (basisB (P.basisIdx.getD b (0, 0)).1
          (P.basisIdx.getD b (0, 0)).2)).map (mapRingHom ψ₀)) := by
      rw [toPoly_trim]; exact hbE _
    rw [S.coeff_phi_inf P.Fc ψ₀ hSF P.k P.inf.N hN w hY wt P.inf.prec hw _ _ (trim P.R0) hbR
      P.DWb (hBok b (Finset.mem_range.mp hb)) hR0 (getD_trim_last _ hR0) (j + 1) (by
        simp only [CurveProb.sbInf, degT] at hsb; push_cast at hsb ⊢; omega)]
    simp only [CurveProb.VbInf, CurveProb.sbInf, degT]
    congr 2; push_cast; ring
  have hrow2 : ψ (P.rowInfAt wt j).2 = -(P.inf.N : K) * ψ (gi (P.VfInf wt)
      (j + P.inf.N + 1 - P.sfInf)) := by
    simp only [CurveProb.rowInfAt, map_mul, map_neg, map_natCast]
  have hrow1 : ∀ b ∈ Finset.range P.basisIdx.length, ψ ((P.rowInfAt wt j).1.getD b 0) =
      ((j + 1 : ℤ) : K) * ψ (gi (P.VbInf wt (P.basisIdx.getD b (0, 0))) (j + 1 - P.sbInf)) := by
    intro b hb
    have hb' := Finset.mem_range.mp hb
    simp only [CurveProb.rowInfAt]
    rw [List.getD_eq_getElem _ _ (by simpa using hb'), List.getElem_map, map_mul, map_intCast,
      List.getD_eq_getElem _ _ hb']
  have hsumR : ∑ b ∈ Finset.range P.basisIdx.length,
      algebraMap C K (cv b) * ψ ((P.rowInfAt wt j).1.getD b 0) =
      ((j + 1 : ℤ) : K) * ∑ b ∈ Finset.range P.basisIdx.length, algebraMap C K (cv b) *
        ψ (gi (P.VbInf wt (P.basisIdx.getD b (0, 0))) (j + 1 - P.sbInf)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb ↦ by rw [hrow1 b hb]; ring
  rw [hfc, hvc, hsumR, hrow2]
  simp only [CurveProb.VfInf, CurveProb.sfInf, degT]
  have e : j - (-(P.inf.N : ℤ) - 1) + ((P.inf.N * P.DA : ℕ) : ℤ) -
      ((P.inf.N * ((trim P.D).length - 1) : ℕ) : ℤ) =
      j + P.inf.N + 1 - (-((P.inf.N * P.DA : ℕ) : ℤ) +
        ((P.inf.N * ((trim P.D).length - 1) : ℕ) : ℤ)) := by ring
  rw [e]

/-- **The residue along a certified finite branch.** -/
theorem resFin_sem (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (a : F) (c : BranchCert F) (hN : 0 < c.N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub c.N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0) (yt : CPoly F)
    (hy : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt))
    (hμf : P.mufFin a c.N < c.prec + c.N) (hQfl : P.mufFin a c.N < (P.QfFin a c.N).length)
    (f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀))) :
    LaurentSeries.res (S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
        (HahnSeries.ofPowerSeries ℤ K Y) hY f *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ₀ a)) + single (c.N : ℤ) (1 : K))) =
      (algebraMap C K).comp ψ₀ (P.resFin a c yt) := by
  rw [LaurentSeries.res, SuperData.derivation_branchX c.N hN, mul_comm, coeff_single_mul']
  rw [S.coeff_phi_fin (P.Fc) ψ₀ hSF a c.N hN Y hY yt c.prec hy f P.A P.D hf hQfl
    (-1 - ((c.N : ℤ) - 1)) (by
      have : (P.mufFin a c.N : ℤ) < c.prec + c.N := by exact_mod_cast hμf
      simp only [CurveProb.mufFin, CurveProb.QfFin] at this ⊢; omega)]
  simp only [CurveProb.resFin, CurveProb.VfFin, CurveProb.UfFin, CurveProb.mufFin,
    CurveProb.QfFin, map_mul, map_natCast]
  congr 2
  ring

/-- **The residue along a certified branch above infinity.** -/
theorem resInf_sem (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hN : 0 < P.inf.N) (w : PowerSeries K)
    (hY : (S.F.map (infSub P.inf.N)).eval
      (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F)
    (hw : (PowerSeries.X : PowerSeries K) ^ P.inf.prec ∣
      w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt))
    (hsf : (P.inf.N : ℤ) - P.sfInf < P.inf.prec) (hD0 : 0 < (trim P.D).length)
    (hAok : InvOK P.k P.DA 0 P.A) (f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀))) :
    LaurentSeries.res (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY f *
        LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : K))) =
      (algebraMap C K).comp ψ₀ (P.resInf wt) := by
  have hfD : (f : L) * aeval S.x ((toPoly (trim P.D)).map ψ₀) =
      S.evXY ((toB P.A).map (mapRingHom ψ₀)) := by rw [toPoly_trim]; exact hf
  rw [LaurentSeries.res, SuperData.derivation_infX, mul_comm, coeff_single_mul']
  rw [S.coeff_phi_inf P.Fc ψ₀ hSF P.k P.inf.N hN w hY wt P.inf.prec hw f P.A (trim P.D)
    hfD P.DA hAok hD0 (getD_trim_last _ hD0) (-1 - (-(P.inf.N : ℤ) - 1)) (by
      simp only [CurveProb.sfInf, degT] at hsf; push_cast at hsf ⊢; omega)]
  simp only [CurveProb.resInf, CurveProb.VfInf, CurveProb.sfInf, degT, map_mul, map_neg,
    map_natCast]
  congr 3
  push_cast; ring

end CurveData

end Sem3

end Curves
