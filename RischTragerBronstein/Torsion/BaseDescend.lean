import RischTragerBronstein.Torsion.BasePts
import RischTragerBronstein.Torsion.NonSpec7

/-!
# Base points over the coefficient field from base points over `C`

**`base_descend_core`**: non-special base fibres over an algebraically closed `C ⊇ F` (for some
integral basis of the curve over `C`) whose coordinates come from `F` are non-special fibres over
`F` for every other integral basis over `F` (non-speciality is independent of the integral basis,
`kerSp_transfer`, and descends to subfields, `kerSp_descend`).

**`hbase_of_C`**: the hypothesis `hbase` of `exists_torsOKP_of_base` from such base fibres
avoiding the special points.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Core

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [Algebra C L]

/-- **Descent and transfer of non-special base fibres.** -/
theorem base_descend_core (S : CurveData C L) (ψ : F →+* C)
    {B0 : Fin S.F.natDegree → C[X][X]} {D0 : C[X]} {δ0 : Fin S.F.natDegree → ℕ}
    (hB0 : S.IsIntBasis C B0 D0 δ0) (hn : 0 < S.F.natDegree) (hB00 : B0 ⟨0, hn⟩ = Polynomial.C D0)
    {g : ℕ} (f0 : Fin g → AdmFib B0) (hns0 : kerSp δ0 g g f0 (fun _ ↦ ⟨0, hn⟩) ≤ C ∙ e0 hn f0)
    (hD0x : ∀ l, D0.eval (f0 l).x ≠ 0)
    (xF : Fin g → F) (hxF : ∀ l, ψ (xF l) = (f0 l).x)
    (yF : Fin g → Fin S.F.natDegree → F) (hyF : ∀ l k, ψ (yF l k) = (f0 l).ys k)
    (n : ℕ) (hnS : n = S.F.natDegree) (Bc : List (BPoly F)) (Dc : CPoly F) (δL : List ℕ)
    (hIB : S.IsIntBasis C (fun j : Fin S.F.natDegree ↦ (toB (Bc.getD j [])).map (mapRingHom ψ))
      ((toPoly Dc).map ψ) (fun j ↦ δL.getD j 0))
    (hnorm : Bc.getD 0 [] = [Dc]) (hDx : ∀ l, Kron.evalC Dc (xF l) ≠ 0)
    (hdetx : ∀ l, ((Matrix.of fun (i j : Fin n) ↦ (toB (Bc.getD j [])).coeff i).det).eval (xF l) ≠ 0) :
    ∃ (hn' : 0 < n) (f : Fin g → AdmFib (fun j : Fin n ↦ toB (Bc.getD j []))),
      (∀ l, (f l).x = xF l) ∧ (∀ l k, ψ ((f l).ys k) = (f0 l).ys (Fin.cast hnS k)) ∧
      kerSp (fun j ↦ δL.getD j 0) g g f (fun _ ↦ ⟨0, hn'⟩) ≤ F ∙ e0 hn' f := by
  classical
  subst hnS
  -- the fibres over `F`
  have hdegB : ∀ j : Fin S.F.natDegree, (toB (Bc.getD j [])).natDegree < S.F.natDegree := fun j ↦ by
    have := hIB.deg j
    rwa [natDegree_map_eq_of_injective (Polynomial.map_injective _ ψ.injective)] at this
  have hyinj : ∀ l, Function.Injective (yF l) := fun l k k' h ↦ by
    have := congrArg ψ h
    rw [hyF, hyF] at this
    exact ys_nodup_of_det (f0 l) this
  have hdetF : ∀ l, (Matrix.of fun (k j : Fin S.F.natDegree) ↦
      evalW (toB (Bc.getD j [])) (xF l) (yF l k)).det ≠ 0 := fun l ↦ by
    rw [det_evalW _ hdegB]
    refine mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (hyinj l)) ?_
    have := RingHom.map_det (evalRingHom (xF l))
      (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (toB (Bc.getD j [])).coeff i)
    rw [coe_evalRingHom] at this
    rw [show (Matrix.of fun (i j : Fin S.F.natDegree) ↦ ((toB (Bc.getD j [])).coeff i).eval (xF l)) =
      (evalRingHom (xF l)).mapMatrix (Matrix.of fun (i j : Fin S.F.natDegree) ↦
        (toB (Bc.getD j [])).coeff i) by ext; simp, ← this]
    exact hdetx l
  set fF : Fin g → AdmFib (fun j : Fin S.F.natDegree ↦ toB (Bc.getD j [])) :=
    fun l ↦ ⟨xF l, yF l, hdetF l⟩ with hfF
  -- non-speciality over `C` for the target basis
  have hB0T : (fun j : Fin S.F.natDegree ↦ (toB (Bc.getD j [])).map (mapRingHom ψ)) ⟨0, hn⟩ =
      Polynomial.C ((toPoly Dc).map ψ) := by
    simp only [hnorm]
    rw [toB_cons, toB_nil, mul_zero, add_zero, Polynomial.map_C]; rfl
  have hns : kerSp (fun j ↦ δL.getD j 0) g g (fun l ↦ (fF l).map ψ) (fun _ ↦ ⟨0, hn⟩) ≤
      C ∙ e0 hn (fun l ↦ (fF l).map ψ) :=
    CurveData.kerSp_transfer hn hB0 hIB hB00 hB0T g g f0 (fun l ↦ (fF l).map ψ) (fun l ↦ (hxF l).symm)
      (fun l ↦ funext fun k ↦ (hyF l k).symm) hD0x
      (fun l ↦ by
        rw [← hxF, eval_map, eval₂_at_apply, ← Kron.evalC_eq]
        exact (map_ne_zero ψ).mpr (hDx l))
      (fun _ ↦ ⟨0, hn⟩) hns0
  refine ⟨hn, fF, fun l ↦ rfl, fun l k ↦ hyF l k, ?_⟩
  exact kerSp_descend ψ (fun j ↦ δL.getD j 0) hn g g fF (fun _ ↦ ⟨0, hn⟩) hns

end Core

section Hbase

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [Algebra C L]

/-- **Base fibres over `F` for every global certificate** from non-special base fibres over `C`
with coordinates in `F`, away from the special points. -/
theorem hbase_of_C (S : CurveData C L) (ψ : F →+* C) (P : CurveProb F) (hV : P.ValidFacts)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ))
    {B0 : Fin S.F.natDegree → C[X][X]} {D0 : C[X]} {δ0 : Fin S.F.natDegree → ℕ}
    (hB0 : S.IsIntBasis C B0 D0 δ0) (hn : 0 < S.F.natDegree) (hB00 : B0 ⟨0, hn⟩ = Polynomial.C D0)
    {g : ℕ} (hg0 : 0 < g) (hsum0 : ∑ j, δ0 j + 1 = g + S.F.natDegree)
    (f0 : Fin g → AdmFib B0) (hinj0 : Function.Injective fun l ↦ (f0 l).x)
    (hns0 : kerSp δ0 g g f0 (fun _ ↦ ⟨0, hn⟩) ≤ C ∙ e0 hn f0) (hD0x : ∀ l, D0.eval (f0 l).x ≠ 0)
    (hroot0 : ∀ l k, evalW S.F (f0 l).x ((f0 l).ys k) = 0)
    (hsimple0 : ∀ l k, evalW (derivative S.F) (f0 l).x ((f0 l).ys k) ≠ 0)
    (xF : Fin g → F) (hxF : ∀ l, ψ (xF l) = (f0 l).x)
    (yF : Fin g → Fin S.F.natDegree → F) (hyF : ∀ l k, ψ (yF l k) = (f0 l).ys k)
    (havoid : ∀ l, ∀ ac ∈ P.pts, xF l ≠ ac.1) :
    ∀ T : GlobalCert F, T.globalCheck = true → T.Fc = P.Fc → T.n = P.n →
      T.I.pts.map Prod.fst = P.pts.map Prod.fst →
      ∃ g', 0 < g' ∧ (∑ j ∈ Finset.range T.n, T.I.δL.getD j 0) + 1 = g' + T.n ∧
      ∃ (hn0 : 0 < T.n) (f : Fin g' → AdmFib (fun j : Fin T.n ↦ toB (T.I.Bc.getD j []))),
        Function.Injective (fun l ↦ (f l).x) ∧
        (∀ l k, evalB T.Fc (f l).x ((f l).ys k) = 0) ∧
        (∀ l k, evalB (derivYB T.Fc) (f l).x ((f l).ys k) ≠ 0) ∧
        (∀ l, Kron.evalC T.I.Dc (f l).x ≠ 0) ∧
        kerSp (fun j ↦ T.I.δL.getD j 0) g' g' f (fun _ ↦ ⟨0, hn0⟩) ≤ F ∙ e0 hn0 f ∧
        ∀ l, ∀ ac ∈ P.pts, (f l).x ≠ ac.1 := by
  classical
  intro T hT hTF hTn hTpts
  have hTf := globalCheck_spec hT
  have hSF' : S.F = (toB T.Fc).map (mapRingHom ψ) := by rw [hTF]; exact hSF
  have hnS : T.n = S.F.natDegree := by
    rw [hSF', natDegree_map_eq_of_injective (Polynomial.map_injective _ ψ.injective),
      hTf.shape.2.2.1]
  have hIB := ibCheckR_spec (K := C) S T.Fc ψ hSF' T.n T.k hnS T.I T.G hTf.ib
    (dvd_of_eq hTf.G_eq.symm)
  have hnorm : T.I.Bc.getD 0 [] = [T.I.Dc] := by
    have := hTf.norm
    simp only [normCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  -- the fibres avoid the zeros of the cover polynomial
  have hcov : coverCheck T.G (T.I.pts.map Prod.fst) = true := by
    have hib := globalCheck_ib hT
    simp only [ibCheck, Bool.and_eq_true] at hib
    exact hib.1.1.2
  have hGx : ∀ l, (toPoly T.G).eval (xF l) ≠ 0 := fun l h0 ↦ by
    obtain ⟨a, ha, hax⟩ := coverCheck_spec _ _ hcov (RingHom.id F) (xF l) (by
      rw [Polynomial.map_id]; exact h0)
    rw [hTpts] at ha
    obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp ha
    exact havoid l ac hac hax
  have hGx' := hGx
  simp only [hTf.G_eq, eval_mul] at hGx'
  have hDx : ∀ l, Kron.evalC T.I.Dc (xF l) ≠ 0 := fun l h ↦ hGx' l (by
    rw [← Kron.evalC_eq, h, mul_zero, zero_mul])
  have hdetx : ∀ l, ((Matrix.of fun (i j : Fin T.n) ↦ (toB (T.I.Bc.getD j [])).coeff i).det).eval
      (xF l) ≠ 0 := fun l h ↦ hGx' l (by rw [h, mul_zero])
  obtain ⟨hn', f, hfx, hfy, hker⟩ := base_descend_core S ψ hB0 hn hB00 f0 hns0 hD0x xF hxF yF hyF
    T.n hnS T.I.Bc T.I.Dc T.I.δL hIB hnorm hDx hdetx
  refine ⟨g, hg0, ?_, hn', f, fun l l' h ↦ hinj0 (by
      simp only at h ⊢; rw [← hxF, ← hxF, ← hfx, ← hfx, h]), fun l k ↦ ?_, fun l k ↦ ?_,
    fun l ↦ by rw [hfx]; exact hDx l, hker, fun l ac hac ↦ by rw [hfx]; exact havoid l ac hac⟩
  · have := CurveData.sum_delta_eq hB0 hIB
    rw [hnS, ← Fin.sum_univ_eq_sum_range (fun j ↦ T.I.δL.getD j 0), ← this, hsum0]
  · apply ψ.injective
    rw [map_zero, evalB_eq, ← GTors.evalW_mapG, ← hSF', hfy, hfx, hxF]
    exact hroot0 l _
  · intro h0
    have := congrArg ψ h0
    rw [map_zero, evalB_eq, toB_derivYB, ← GTors.evalW_mapG, ← Polynomial.derivative_map, ← hSF', hfy,
      hfx, hxF] at this
    exact hsimple0 l _ this

end Hbase

end Curves
