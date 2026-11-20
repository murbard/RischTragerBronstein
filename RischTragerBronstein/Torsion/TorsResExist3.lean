import RischTragerBronstein.Torsion.TorsResExist2

/-!
# Residue data at places from a valid problem (2): infinity

`inf_roots_F_approx`: the roots above infinity (`inf_roots_F`) together with their approximations by
the certificate of the problem; `sum_res_inf_eq_zero`: if every computed residue at infinity
vanishes, so does the sum of the residues along the roots above infinity.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Inf

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)

include hSF hV in
/-- **The roots above infinity with their approximations.** -/
theorem inf_roots_F_approx :
    ∃ w : Fin P.n → PowerSeries F,
      (∀ k : Fin P.n, (PowerSeries.X : PowerSeries F) ^ P.inf.prec ∣
        w k - thetaT (RingHom.id F) (toPoly (P.inf.ys.getD k []))) ∧
      (∀ k, (S.F.map (infSub (K := C) P.inf.N)).eval (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) *
        ofPowerSeries ℤ C (PowerSeries.map ψ (w k))) = 0) ∧
      Function.Injective w := by
  classical
  set N := P.inf.N
  have hN := hV.infN
  obtain ⟨w, happ, hinj, hsplit⟩ := certCheck_spec (C := F) (K := F) (invB P.Fc P.k (P.k * P.n)) P.n
    hV.mon' hV.deg' 0 P.inf hV.certInf (RingHom.id F)
  have hidF : (algebraMap F F).comp (RingHom.id F) = RingHom.id F := RingHom.ext fun _ ↦ rfl
  refine ⟨w, fun k ↦ by simpa [hidF] using happ k, fun k ↦ ?_, hinj⟩
  have hrootF : ((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN (RingHom.id F) 0 N)).eval
      (w k) = 0 := by
    have h1 : ((((toB (invB P.Fc P.k (P.k * P.n))).map (mapRingHom (RingHom.id F))).map
        (branchSub (C := F) (K := F) N (algebraMap F F (RingHom.id F 0))))).eval
        (ofPowerSeries ℤ F (w k)) = 0 := by
      rw [hsplit, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    have hG : ((toB (invB P.Fc P.k (P.k * P.n))).map (mapRingHom (RingHom.id F))).map
        (branchSub (C := F) (K := F) N (algebraMap F F (RingHom.id F 0))) =
        ((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN (RingHom.id F) 0 N)).map
          (ofPowerSeries ℤ F) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      refine RingHom.ext fun Q ↦ ?_
      have := ofPS_thetaN (C := F) (K := F) (RingHom.id F) 0 N Q
      rw [hidF] at this
      simpa using this.symm
    rw [hG, eval_map, eval₂_at_apply] at h1
    exact HahnSeries.ofPowerSeries_injective (by rw [h1, map_zero])
  have hψ : (algebraMap C C).comp ψ = ψ := RingHom.ext fun _ ↦ rfl
  have h2 : PowerSeries.map ψ
      (((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN (RingHom.id F) 0 N)).eval (w k)) =
      ((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN ψ 0 N)).eval (PowerSeries.map ψ (w k)) := by
    rw [eval_map, hom_eval₂, eval_map]
    congr 1
    exact RingHom.ext fun Q ↦ by simpa using map_thetaN ψ 0 N Q
  rw [hrootF, map_zero] at h2
  have := eval_invB (K := C) ψ N hN P.k (P.k * P.n) (PowerSeries.map ψ (w k)) P.Fc hV.okF
  rw [hψ] at this
  rw [hSF, this, ← h2, map_zero, mul_zero]

include hSF hV in
/-- The roots above infinity form a complete system. -/
theorem inf_split_approx (w : Fin P.n → PowerSeries F)
    (hroot : ∀ k, (S.F.map (infSub (K := C) P.inf.N)).eval (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) *
        ofPowerSeries ℤ C (PowerSeries.map ψ (w k))) = 0) (hinj : Function.Injective w) :
    S.F.map (infSub (K := C) P.inf.N) = ∏ k : Fin S.F.natDegree, (X - Polynomial.C
      (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) *
        ofPowerSeries ℤ C (PowerSeries.map ψ (w (Fin.cast (S.natDegree_F_eq P ψ hSF hV) k))))) := by
  classical
  have hn := S.natDegree_F_eq P ψ hSF hV
  set r : Fin S.F.natDegree → LaurentSeries C := fun k ↦
    single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) *
      ofPowerSeries ℤ C (PowerSeries.map ψ (w (Fin.cast hn k))) with hr
  have hinjr : Function.Injective r := by
    intro k l hkl
    have h0 : single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) ≠ 0 := single_ne_zero one_ne_zero
    have h1 := HahnSeries.ofPowerSeries_injective (mul_left_cancel₀ h0 hkl)
    have h2 : w (Fin.cast hn k) = w (Fin.cast hn l) := by
      ext t
      have := congrArg (PowerSeries.coeff t) h1
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at this
      exact ψ.injective this
    exact Fin.cast_injective hn (hinj h2)
  exact eq_prod_of_distinct_roots _ (S.monic.map _) (by rw [S.monic.natDegree_map]) r hinjr
    fun k ↦ hroot _

include hSF hV in
/-- **Vanishing computed residues at infinity give vanishing residues.** -/
theorem res_inf_root (w : Fin P.n → PowerSeries F)
    (happ : ∀ k : Fin P.n, (PowerSeries.X : PowerSeries F) ^ P.inf.prec ∣
        w k - thetaT (RingHom.id F) (toPoly (P.inf.ys.getD k [])))
    (hroot : ∀ k, (S.F.map (infSub (K := C) P.inf.N)).eval (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) *
        ofPowerSeries ℤ C (PowerSeries.map ψ (w k))) = 0)
    (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0) (k : Fin P.n) :
    LaurentSeries.res (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hV.infN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) * ofPowerSeries ℤ C (PowerSeries.map ψ (w k)))
        (hroot k) (S.fE P ψ) * LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : C))) = 0 := by
  have hw : (PowerSeries.X : PowerSeries C) ^ P.inf.prec ∣
      PowerSeries.map ψ (w k) - thetaT ((algebraMap C C).comp ψ) (toPoly (P.inf.ys.getD k [])) := by
    obtain ⟨q, hq⟩ := happ k
    refine ⟨PowerSeries.map ψ q, ?_⟩
    have := congrArg (PowerSeries.map ψ) hq
    rw [map_sub, map_mul, map_pow, PowerSeries.map_X] at this
    rw [← this]
    congr 1
    ext i
    simp [coeff_thetaT, thetaT_apply, Polynomial.coeff_coe]
  have h := S.resInf_sem (K := C) P ψ hSF hV.infN (PowerSeries.map ψ (w k)) (hroot k) _ hw hV.sf
    hV.Dl hV.okA (S.fE P ψ) (S.fE_spec P ψ hV)
  rw [h]
  have hmem : P.inf.ys.getD k [] ∈ P.inf.ys := by
    have hlen : P.inf.ys.length = P.n := by
      have := hV.certInf
      simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1.2
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
    exact List.getElem_mem _
  rw [hinf0 _ hmem, map_zero]

end CurveData

end Inf

end Curves
