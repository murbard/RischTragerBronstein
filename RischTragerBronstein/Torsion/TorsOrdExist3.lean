import RischTragerBronstein.Torsion.TorsOrdExist2
import RischTragerBronstein.Torsion.RamNonTors

/-!
# Torsion data from principal divisors (3): the principality test fails

**`not_princTest_PcE`**: if no multiple of the `j₀`-residue divisor is torsion (no `w ≠ 0` satisfies
`TorsOrdStd`), the principality test for `Mt (Γ − cΓ ∞ₓ)` (`Γ` the divisor of the place certificate
`PcE`, expansions along the actual roots) fails for every `Mt > 0`: a passing test gives `γ` with
`div γ ≥ Mt (Γ − cΓ ∞ₓ)` (`principal_iff_test`), hence equality (`divGE_exact`), hence a torsion
witness (`torsOrdStd_of_exact`).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Fail

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

lemma lmap_algebraMap_self (z : LaurentSeries C) : lmap (algebraMap C C) z = z := by
  ext k; simp [lmap]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F))

/-- A `ℚ`-linear functional extending `coord j₀` along `ψ`. -/
lemma exists_Λ : ∃ Λ : C →ₗ[ℚ] ℚ, ∀ r : F, Λ (ψ r) = coord j₀ r := by
  set ιF : F →ₗ[ℚ] C := ψ.toRatAlgHom.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ιF
    (LinearMap.ker_eq_bot.mpr ψ.injective)
  refine ⟨(coord j₀).comp g, fun r ↦ ?_⟩
  have : g (ιF r) = r := by rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
  rw [LinearMap.comp_apply]
  exact congrArg (coord j₀) this

/-- **The principality test fails for the multiples of a non-torsion residue divisor.** -/
theorem not_princTest_PcE (hnd : (P.pts.map Prod.fst).Nodup)
    (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0) (T : GlobalCert F) (hT : T.globalCheck = true)
    (hTF : T.Fc = P.Fc)
    (hNT : ∀ m, 0 < m → ∀ Λ : C →ₗ[ℚ] ℚ, (∀ r : F, Λ (ψ r) = coord j₀ r) →
      ∀ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 → ¬ S.TorsOrdStd (K := C) P ψ m w Λ)
    (Mt : ℕ) (hMt : 0 < Mt) :
    ¬ princTest (fun i : Fin S.F.natDegree ↦ T.I.δL.getD i 0) (Mt * ∑ j, S.eLj P hSF hV hζ j₀ j)
      (fun q : Fin P.pts.length × Fin S.F.natDegree ↦ (S.Φj P hSF hV q.1).N)
      (fun q ↦ ψ (P.pts[q.1]).1)
      (fun q i ↦ basisSer (fun i : Fin S.F.natDegree ↦ (toB (T.I.Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly T.I.Dc).map ψ) (S.Φj P hSF hV q.1).N (ψ (P.pts[q.1]).1)
          (ofPowerSeries ℤ C ((S.Φj P hSF hV q.1).y q.2)) i)
      (fun q ↦ Mt * ((S.Φj P hSF hV q.1).sIdx (S.ζj_spec P hSF hV hζ q.1)
        ((S.Φj P hSF hV q.1).rep (S.ζj_spec P hSF hV hζ q.1) q.2) *
          S.Γj P hSF hV hζ j₀ q.1 ((S.Φj P hSF hV q.1).rep (S.ζj_spec P hSF hV hζ q.1) q.2))) := by
  classical
  intro htest
  have hTf := globalCheck_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  have hSF' : S.F = (toB T.Fc).map (mapRingHom ψ) := by rw [hSF, hTF]
  have hnS : S.F.natDegree = T.n := by rw [hSF', hmon.natDegree_map, hdeg]
  have hBS : S.IsIntBasis C (fun j ↦ (toB (T.I.Bc.getD j [])).map (mapRingHom ψ))
      ((toPoly T.I.Dc).map ψ) (fun j ↦ T.I.δL.getD j 0) :=
    ibCheckR_spec (K := C) S T.Fc ψ hSF' T.n T.k hnS.symm T.I T.G hTf.ib (dvd_of_eq hTf.G_eq.symm)
  set m := P.pts.length
  set α : Fin m → C := fun j ↦ ψ (P.pts[j]).1
  have hα : Function.Injective α := by
    intro j j' h
    have h1 : (P.pts.map Prod.fst)[j.1]'(by rw [List.length_map]; exact j.2) =
        (P.pts.map Prod.fst)[j'.1]'(by rw [List.length_map]; exact j'.2) := by
      simpa using ψ.injective h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
  set N : Fin m → ℕ := fun j ↦ (S.Φj P hSF hV j).N
  have hN : ∀ j, 0 < N j := fun j ↦ (S.Φj P hSF hV j).hN
  set rC : Fin m → Fin S.F.natDegree → LaurentSeries C :=
    fun j k ↦ ofPowerSeries ℤ C ((S.Φj P hSF hV j).y k)
  have hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (α j)) = ∏ k, (X - Polynomial.C (rC j k)) :=
    fun j ↦ (congrArg (fun G : C[X][X] ↦ G.map (branchSub (K := C) (N j) (α j))) hSF).trans
      (S.Φj P hSF hV j).split
  have hrinj : ∀ j, Function.Injective fun k ↦ lmap (algebraMap C C) (rC j k) := fun j k k' h ↦ by
    simp only [lmap_algebraMap_self, rC] at h
    exact (S.Φj P hSF hV j).inj (HahnSeries.ofPowerSeries_injective h)
  set ΓC : Fin m → Fin S.F.natDegree → ℕ := fun j k ↦
    Mt * ((S.Φj P hSF hV j).sIdx (S.ζj_spec P hSF hV hζ j)
      ((S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) k) *
        S.Γj P hSF hV hζ j₀ j ((S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) k))
  set ΓK : Fin m → LaurentSeries C → ℕ := fun j ↦
    Function.extend (fun k ↦ lmap (algebraMap C C) (rC j k)) (ΓC j) 0
  have hΓK : ∀ j k, ΓK j (lmap (algebraMap C C) (rC j k)) = ΓC j k := fun j k ↦
    (hrinj j).extend_apply _ _ k
  set cΓ := ∑ j, S.eLj P hSF hV hζ j₀ j
  obtain ⟨γ, hγ0, hγ⟩ := (S.principal_iff_test hBS α N hN rC hsC ΓC ΓK hΓK (Mt * cΓ)).mpr htest
  have hn := S.natDegree_F_eq P ψ hSF hV
  -- the local sums of the multiplicities
  set dΓ : Fin m → ℕ := fun j ↦ Mt * (S.lpj P hSF hV hζ j (S.Γj P hSF hV hζ j₀ j)).Γ.sum
  have hdΓ : ∀ j, ((List.ofFn fun k ↦ lmap (algebraMap C C) (rC j k)).map (ΓK j)).sum = N j * dΓ j := by
    intro j
    rw [List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, hΓK]
    have hOK := (S.Φj P hSF hV j).locPlaces_OK (S.ζj_spec P hSF hV hζ j) (S.Φj_a P hSF hV j) (txj P j)
      (Function.invFun ψ) (ζj P hζ j) (S.Γj P hSF hV hζ j₀ j) ψ.injective rfl (S.hpre_j P hSF hV hζ j)
    have hds := hOK.dsum
    rw [← Fin.sum_univ_eq_sum_range] at hds
    simp only [ΓC, dΓ, ← Finset.mul_sum]
    rw [show N j * (Mt * _) = Mt * (N j * (S.lpj P hSF hV hζ j (S.Γj P hSF hV hζ j₀ j)).Γ.sum) by ring]
    congr 1
    refine Eq.trans ?_ hds
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hlt := (S.Φj P hSF hV j).idxOf_lt (S.ζj_spec P hSF hV hζ j) k
    rw [SplitFibre.lp_s _ _ _ _ _ _ _ k k.2, SplitFibre.lp_idx _ _ _ _ _ _ _ k k.2]
    simp only [Fin.eta]
    rw [SplitFibre.lp_Γ _ _ _ _ _ _ _ _ hlt, (S.Φj P hSF hV j).getElem_idxOf]
  have hsumΓ : ∑ j, dΓ j = Mt * cΓ * S.F.natDegree := by
    have h := S.sum_Γj P hSF hV hζ j₀ hnd hinf0
    simp only [dΓ, ← Finset.mul_sum]
    rw [hn, mul_assoc]
    congr 1
    exact_mod_cast h
  have hlf := fun j ↦ S.split_lmap (K := C) (N j) (α j) (rC j) (hsC j)
  obtain ⟨hex1, hex2, hex3⟩ := S.divGE_exact S.hasBranches S.hasBranchesInf α hα N hN _ hlf ΓK
    (Mt * cΓ) dΓ hdΓ hsumΓ γ hγ0 hγ
  obtain ⟨Λ, hΛ⟩ := exists_Λ (C := C) (ψ := ψ) j₀
  have hT := S.torsOrdStd_of_exact P hSF hV hζ j₀ hnd hinf0 Λ hΛ Mt γ hγ0 (fun j k ↦ by
      have hr : lmap (algebraMap C C) (rC j k) ∈ List.ofFn fun k ↦ lmap (algebraMap C C) (rC j k) :=
        List.mem_ofFn.mpr ⟨k, rfl⟩
      have e := hex1 j _ hr
      rw [hΓK] at e
      have e' : ((Mt : ℤ) * ((S.Φj P hSF hV j).sIdx (S.ζj_spec P hSF hV hζ j)
          ((S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) k) *
            S.Γj P hSF hV hζ j₀ j ((S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) k) : ℕ)) =
          ((ΓC j k : ℕ) : ℤ) := by simp only [ΓC]; push_cast; ring
      rw [e', e]
      exact (congrArg HahnSeries.order (congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries C ↦ φ γ)
        (S.embG_congr' rfl _ _ (lmap_algebraMap_self _) _ _))).symm)
    (fun b hb N' hN' l hl r hr ↦ hex2 b (by simpa [α] using hb) N' hN'.ne' l hl r hr)
    (fun N' hN' l hl r hr ↦ (hex3 N' hN'.ne' l hl r hr).symm)
  exact hNT _ (Nat.mul_pos hMt (S.sden_pos P hSF hV hζ j₀)) Λ hΛ _
    (mul_ne_zero hγ0 (S.Uq_ne_zero P hSF hV hζ j₀ Mt)) hT

end CurveData

end Fail

end Curves
