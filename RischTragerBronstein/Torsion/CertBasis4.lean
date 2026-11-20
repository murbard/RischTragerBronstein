import RischTragerBronstein.Torsion.CertBasis3
import RischTragerBronstein.Torsion.CertBasisDet

/-!
# Certified integral bases (any characteristic)

`isIntBasis_of_cert`: branch certificates and basis checks at the listed special points, a
multiple `G` of `disc · D · ∏ⱼ B_{j,j}` whose roots are covered by these points, and the basis check
above infinity give `IsIntBasis` over every algebraically closed field receiving the coefficients.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors CPoly Sup

section Cert

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)

/-- **Certified integral bases.** -/
theorem isIntBasis_of_cert (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree)
    (Bc : List (BPoly F)) (Dc : CPoly F) (δ : List ℕ) (hD : toPoly Dc ≠ 0)
    (htri : ∀ j : Fin S.F.natDegree, (toB (Bc.getD j [])).natDegree ≤ j)
    (hlead : ∀ j : Fin S.F.natDegree, (toB (Bc.getD j [])).coeff j ≠ 0)
    (pts : List (F × BranchCert F × List (List F)))
    (hpts : ∀ p ∈ pts, certCheck Fc S.F.natDegree p.1 p.2.1 = true ∧
      basisCheckAt S.F.natDegree Bc Dc p.1 p.2.1 p.2.2 = true)
    (G : CPoly F) (hG : resultant (toB Fc) (derivative (toB Fc)) S.F.natDegree
      (S.F.natDegree - 1) * toPoly Dc * ∏ j : Fin S.F.natDegree, (toB (Bc.getD j [])).coeff j ∣ toPoly G)
    (hcov : coverCheck G (pts.map Prod.fst) = true)
    (infc : BranchCert F) (Linf : List (List F))
    (hinfc : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 infc = true)
    (hinfb : basisCheckInf S.F.natDegree k Bc Dc δ infc Linf = true) :
    S.IsIntBasis K (fun j ↦ (toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)
      (fun j ↦ δ.getD j 0) := by
  classical
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  obtain ⟨hinf, hindInf⟩ := S.basisCheckInf_spec (K := K) Fc ψ₀ hSF hmon hdeg k hok hmon' hn' Bc Dc
    δ infc hinfc Linf hinfb
  set Sp : Finset K := (pts.map fun p ↦ algebraMap C K (ψ₀ p.1)).toFinset with hSp
  have hmemSp : ∀ a ∈ Sp, ∃ p ∈ pts, a = algebraMap C K (ψ₀ p.1) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact ⟨p, hp, rfl⟩
  have hψe : (mapRingHom (algebraMap C K)).comp (mapRingHom ψ₀) = mapRingHom ψ :=
    by rw [hψ, Polynomial.mapRingHom_comp]
  refine S.isIntBasis_of_special ((Polynomial.map_ne_zero_iff ψ₀.injective).mpr hD)
    (fun j ↦ natDegree_map_le.trans (htri j))
    (fun j ↦ by
      rw [coeff_map]
      exact (map_ne_zero_iff _ (Polynomial.map_injective _ ψ₀.injective)).mpr (hlead j))
    Sp (fun a ha ↦ ?_) (fun j a ha ↦ ?_) (fun a ha ↦ ?_) hinf hindInf
  · -- away from the special points
    set φ : F[X] →+* K := (evalRingHom a).comp (mapRingHom ψ) with hφ
    have hφa : ∀ P : F[X], ((P.map ψ₀).map (algebraMap C K)).eval a = φ P := fun P ↦ by
      rw [Polynomial.map_map]; rfl
    have hG0 : φ (toPoly G) ≠ 0 := by
      intro h0
      apply ha
      obtain ⟨a', ha', rfl⟩ := coverCheck_spec G _ hcov ψ a h0
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha'
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
    obtain ⟨Rq, hRq⟩ := hG
    rw [hRq, map_mul, map_mul, map_mul, map_prod] at hG0
    replace hG0 := left_ne_zero_of_mul hG0
    obtain ⟨⟨h1, h2⟩, h3⟩ := And.intro (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hG0).1)
      (mul_ne_zero_iff.mp hG0).2
    have hfib : (S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a) = (toB Fc).map φ := by
      rw [hSF, Polynomial.map_map, Polynomial.map_map, RingHom.comp_assoc, hψe]
    refine ⟨?_, by rw [hφa]; exact h2, fun j ↦ ?_⟩
    · rw [hfib, Polynomial.derivative_map, resultant_map_map]; exact h1
    · rw [coeff_map, coe_mapRingHom, hφa]; exact (Finset.prod_ne_zero_iff.mp h3) j (Finset.mem_univ _)
  · obtain ⟨p, hp, rfl⟩ := hmemSp a ha
    exact ((S.basisCheckAt_spec (K := K) Fc ψ₀ hSF hmon hdeg Bc Dc hD p.1 p.2.1 (hpts p hp).1 p.2.2
      (hpts p hp).2).1 j)
  · obtain ⟨p, hp, rfl⟩ := hmemSp a ha
    exact (S.basisCheckAt_spec (K := K) Fc ψ₀ hSF hmon hdeg Bc Dc hD p.1 p.2.1 (hpts p hp).1 p.2.2
      (hpts p hp).2).2

theorem isIntBasis_of_cert_det (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree)
    (Bc : List (BPoly F)) (Dc : CPoly F) (δ : List ℕ) (hD : toPoly Dc ≠ 0)
    (hdegB : ∀ j : Fin S.F.natDegree, (toB (Bc.getD j [])).natDegree < S.F.natDegree)
    (hdetB : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (toB (Bc.getD j [])).coeff i).det ≠ 0)
    (pts : List (F × BranchCert F × List (List F)))
    (hpts : ∀ p ∈ pts, certCheck Fc S.F.natDegree p.1 p.2.1 = true ∧
      basisCheckAt S.F.natDegree Bc Dc p.1 p.2.1 p.2.2 = true)
    (G : CPoly F) (hG : resultant (toB Fc) (derivative (toB Fc)) S.F.natDegree
      (S.F.natDegree - 1) * toPoly Dc *
        (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (toB (Bc.getD j [])).coeff i).det ∣ toPoly G)
    (hcov : coverCheck G (pts.map Prod.fst) = true)
    (infc : BranchCert F) (Linf : List (List F))
    (hinfc : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 infc = true)
    (hinfb : basisCheckInfS S.F.natDegree k Bc Dc δ infc Linf = true) :
    S.IsIntBasis K (fun j ↦ (toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)
      (fun j ↦ δ.getD j 0) := by
  classical
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  obtain ⟨hinf, hindInf⟩ := S.basisCheckInfS_spec (K := K) Fc ψ₀ hSF hmon hdeg k hok hmon' hn' Bc Dc
    δ infc hinfc Linf hinfb
  set Sp : Finset K := (pts.map fun p ↦ algebraMap C K (ψ₀ p.1)).toFinset with hSp
  have hmemSp : ∀ a ∈ Sp, ∃ p ∈ pts, a = algebraMap C K (ψ₀ p.1) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact ⟨p, hp, rfl⟩
  have hψe : (mapRingHom (algebraMap C K)).comp (mapRingHom ψ₀) = mapRingHom ψ :=
    by rw [hψ, Polynomial.mapRingHom_comp]
  have hdetmap : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ ((toB (Bc.getD j [])).map
      (mapRingHom ψ₀)).coeff i).det =
      (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (toB (Bc.getD j [])).coeff i).det.map ψ₀ := by
    rw [show ∀ P : F[X], P.map ψ₀ = mapRingHom ψ₀ P from fun _ ↦ rfl, RingHom.map_det]
    congr 1
    ext i j
    simp [coeff_map]
  refine S.isIntBasis_of_special_det ((Polynomial.map_ne_zero_iff ψ₀.injective).mpr hD)
    (fun j ↦ lt_of_le_of_lt natDegree_map_le (hdegB j))
    (by rw [hdetmap]; exact (Polynomial.map_ne_zero_iff ψ₀.injective).mpr hdetB)
    Sp (fun a ha ↦ ?_) (fun j a ha ↦ ?_) (fun a ha ↦ ?_) hinf hindInf
  · -- away from the special points
    set φ : F[X] →+* K := (evalRingHom a).comp (mapRingHom ψ) with hφ
    have hφa : ∀ P : F[X], ((P.map ψ₀).map (algebraMap C K)).eval a = φ P := fun P ↦ by
      rw [Polynomial.map_map]; rfl
    have hG0 : φ (toPoly G) ≠ 0 := by
      intro h0
      apply ha
      obtain ⟨a', ha', rfl⟩ := coverCheck_spec G _ hcov ψ a h0
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha'
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
    obtain ⟨Rq, hRq⟩ := hG
    rw [hRq, map_mul, map_mul, map_mul] at hG0
    replace hG0 := left_ne_zero_of_mul hG0
    obtain ⟨⟨h1, h2⟩, h3⟩ := And.intro (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hG0).1)
      (mul_ne_zero_iff.mp hG0).2
    have hfib : (S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a) = (toB Fc).map φ := by
      rw [hSF, Polynomial.map_map, Polynomial.map_map, RingHom.comp_assoc, hψe]
    refine ⟨?_, by rw [hφa]; exact h2, ?_⟩
    · rw [hfib, Polynomial.derivative_map, resultant_map_map]; exact h1
    · rw [hdetmap, hφa]; exact h3
  · obtain ⟨p, hp, rfl⟩ := hmemSp a ha
    exact ((S.basisCheckAt_spec (K := K) Fc ψ₀ hSF hmon hdeg Bc Dc hD p.1 p.2.1 (hpts p hp).1 p.2.2
      (hpts p hp).2).1 j)
  · obtain ⟨p, hp, rfl⟩ := hmemSp a ha
    exact (S.basisCheckAt_spec (K := K) Fc ψ₀ hSF hmon hdeg Bc Dc hD p.1 p.2.1 (hpts p hp).1 p.2.2
      (hpts p hp).2).2

end CurveData

end Cert

end Curves
