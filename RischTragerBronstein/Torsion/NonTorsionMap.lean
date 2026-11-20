import RischTragerBronstein.Torsion.NonTorsionCert

/-!
# Non-torsion over any extension of the coefficient field

`not_torsion_of_cert_map`: the certificates of `not_torsion_of_cert` (over a computable field
`F`) prove non-torsion on every curve `F(x, y) = 0` over a field `C ⊇ F` (e.g. an algebraically
closed field of constants): the principality test is invariant under field extension
(`princTest_transport`), and the curve over `F` itself is irreducible (`irr_all`).
-/

open Polynomial IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section NTM

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- **Non-torsion over any extension.** -/
theorem not_torsion_of_cert_map {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb]
    [Algebra C Kb] [IsAlgClosed Kb] (S : CurveData C L) (ι : F →+* C) (T : GlobalCert F)
    (hSF : S.F = (toB T.Fc).map (mapRingHom ι)) (hT : T.globalCheck = true) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincCheck T.n ((Pp.mp * Pq.mp) * T.cdeg) Pb T.I.δL T.I.Bc T.I.Dc T.αL T.cΓ
      (T.ΓL.map (·.map ((Pp.mp * Pq.mp) * ·))) Lm = true) :
    ∀ M : ℕ, 0 < M → ¬ ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGEU (K := Kb) (fun j : Fin T.αL.length ↦ ι (T.αL.getD j 0))
        (fun j (k : Fin S.F.natDegree) ↦ ι ((T.yL.getD j []).getD k 0))
        (fun j k ↦ M * (T.ΓL.getD j []).getD k 0) (M * T.cdeg) γ := by
  classical
  have hTf := globalCheck_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  -- the curve over `F`
  have hirr : Irreducible ((toB T.Fc).map (algebraMap F[X] (RatFunc F))) :=
    (irr_all Rp φp hRp T hTf Pp (primeCheck_spec Rp hPp)).2.2
  set S0 := stdCurve (toB T.Fc) hmon (by rw [hdeg]; exact hn0) hirr with hS0
  have hS0n : S0.F.natDegree = T.n := by show (toB T.Fc).natDegree = T.n; exact hdeg
  have hnS : S.F.natDegree = S0.F.natDegree := by
    rw [hS0n, hSF, hmon.natDegree_map, hdeg]
  have hNT := not_torsion_of_cert (Kb := AlgebraicClosure F) S0 T rfl hT hpq Rp φp hRp Pp hPp
    Rq φq hRq Pq hPq Pb Lm htest
  intro M hM ⟨γ, hγ0, hγ⟩
  apply hNT M hM
  -- the integral bases
  have hB0 : S0.IsIntBasis (AlgebraicClosure F) (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
      (fun j ↦ T.I.δL.getD j 0) := by
    have := ibCheckR_spec (K := AlgebraicClosure F) S0 T.Fc (RingHom.id F)
      (by rw [Polynomial.mapRingHom_id, Polynomial.map_id]; rfl) T.n T.k hS0n.symm T.I T.G hTf.ib
      (dvd_of_eq hTf.G_eq.symm)
    simpa only [Polynomial.mapRingHom_id, Polynomial.map_id] using this
  have hBS : S.IsIntBasis Kb (fun j ↦ (toB (T.I.Bc.getD j [])).map (mapRingHom ι))
      ((toPoly T.I.Dc).map ι) (fun j ↦ T.I.δL.getD j 0) :=
    ibCheckR_spec S T.Fc ι hSF T.n T.k (by rw [hnS, hS0n]) T.I T.G hTf.ib (dvd_of_eq hTf.G_eq.symm)
  -- the branches at the points of `Γ` over `F`
  obtain ⟨hyl, hαnd, hptK⟩ := ptCheck_spec (RingHom.id F) (n := S0.F.natDegree) hmon (hdeg.trans hS0n.symm)
    (by rw [hS0n]; exact hTf.pt)
  have hY0 : ∀ j : Fin T.αL.length, ∃ Y : Fin S0.F.natDegree → PowerSeries F,
      (∀ k, PowerSeries.constantCoeff (Y k) = (T.yL.getD j []).getD k 0) ∧
      S0.F.map (branchSub (C := F) (K := F) 1 (T.αL.getD j 0)) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ F (Y k))) := by
    intro j
    obtain ⟨Y, hYc, hYs, -⟩ := (hptK j j.2).2
    refine ⟨Y, hYc, ?_⟩
    rw [Polynomial.mapRingHom_id, Polynomial.map_id, RingHom.id_apply] at hYs
    exact hYs
  choose Y0 hY0c hsp using hY0
  have hylen : ∀ j : Fin T.αL.length, (T.yL.getD j []).length = S0.F.natDegree :=
    fun j ↦ (hptK j j.2).1.1
  have hyinj : ∀ j : Fin T.αL.length, Function.Injective fun k : Fin S0.F.natDegree ↦
      (T.yL.getD j []).getD k 0 := fun j k k' h ↦ by
    by_contra hne
    exact nodup_getD_ne (hptK j j.2).1.2 (by rw [hylen]; exact k.2) (by rw [hylen]; exact k'.2)
      (Fin.val_ne_of_ne hne) 0 h
  -- the mapped branches over `C`
  set Y0' : Fin T.αL.length → Fin S.F.natDegree → PowerSeries C :=
    fun j k ↦ PowerSeries.map ι (Y0 j (Fin.cast hnS k)) with hY0'
  have hY0'c : ∀ j k, PowerSeries.constantCoeff (Y0' j k) = ι ((T.yL.getD j []).getD k 0) :=
    fun j k ↦ by
      rw [hY0', ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hY0c]
      rfl
  have hsp' : ∀ j : Fin T.αL.length, S.F.map (branchSub (C := C) (K := C) 1 (ι (T.αL.getD j 0))) =
      ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ C (Y0' j k))) := by
    intro j
    refine (congrArg (fun Q : C[X][X] ↦ Q.map (branchSub (C := C) (K := C) 1 (ι (T.αL.getD j 0))))
      hSF).trans ?_
    rw [split_map ι (toB T.Fc) 1 _ _ (hsp j),
      ← prod_cast hnS (fun k ↦ X - Polynomial.C (lmap ι (HahnSeries.ofPowerSeries ℤ F (Y0 j k))))]
    exact Finset.prod_congr rfl fun k _ ↦ by rw [lmap_ofPS]
  have hyinj' : ∀ j : Fin T.αL.length, Function.Injective fun k : Fin S.F.natDegree ↦
      ι ((T.yL.getD j []).getD k 0) := fun j k k' h ↦ by
    have := hyinj j (a₁ := Fin.cast hnS k) (a₂ := Fin.cast hnS k')
      (ι.injective (by simpa only [Fin.val_cast] using h))
    exact Fin.ext (by simpa using congrArg Fin.val this)
  -- from the principal function over `C` to the test over `F`
  have htestC := (S.principal_iff_test_unram hBS (fun j : Fin T.αL.length ↦ ι (T.αL.getD j 0))
    (fun (j : Fin T.αL.length) (k : Fin S.F.natDegree) ↦ ι ((T.yL.getD j []).getD k 0)) Y0' hY0'c
    hsp' hyinj' (fun (j : Fin T.αL.length) (k : Fin S.F.natDegree) ↦ M * (T.ΓL.getD j []).getD k 0)
    (M * T.cdeg)).mp ⟨γ, hγ0, hγ⟩
  have hσ : ∀ (q : Fin T.αL.length × Fin S0.F.natDegree) i,
      LowerBd (basisSer (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc) 1 (T.αL.getD q.1 0)
        (HahnSeries.ofPowerSeries ℤ F (Y0 q.1 q.2)) i) 0 :=
    fun q i ↦ S0.basisSer_lowerBd_unram hB0 _ (Y0 q.1) (hsp q.1) q.2 i
  have htestF := (princTest_transport S0 S ι hnS (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
    (fun j ↦ T.I.δL.getD j 0) (fun j ↦ (toB (T.I.Bc.getD j [])).map (mapRingHom ι))
    ((toPoly T.I.Dc).map ι) (fun _ ↦ rfl) rfl (fun j : Fin T.αL.length ↦ T.αL.getD j 0)
    (fun j : Fin T.αL.length ↦ ι (T.αL.getD j 0)) (fun _ ↦ rfl) Y0 Y0' (fun _ _ ↦ rfl) hσ
    (fun (j : Fin T.αL.length) (k : Fin S0.F.natDegree) ↦ M * (T.ΓL.getD j []).getD k 0)
    (M * T.cdeg)).mpr htestC
  exact (S0.principal_iff_test_unram hB0 (fun j : Fin T.αL.length ↦ T.αL.getD j 0)
    (fun (j : Fin T.αL.length) (k : Fin S0.F.natDegree) ↦ (T.yL.getD j []).getD k 0) Y0 hY0c hsp
    hyinj (fun (j : Fin T.αL.length) (k : Fin S0.F.natDegree) ↦ M * (T.ΓL.getD j []).getD k 0)
    (M * T.cdeg)).mpr htestF

end NTM

end Curves
