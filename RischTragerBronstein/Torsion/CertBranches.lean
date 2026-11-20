import RischTragerBronstein.Torsion.CertBasis4

/-!
# Complete branch systems from certificates (any characteristic)

`hasBranches_of_cert`: certified branches at the listed points, which cover the roots of a
multiple of the discriminant `Res_Y(F, F_Y)`, give a complete branch system above every finite
point (Hensel at the unramified fibres). `hasBranchesInf_of_cert`: a certified system above
infinity. No Newton–Puiseux is needed, so this also applies in characteristic `p`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors CPoly Sup

section Cert

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)

lemma certCheck_N_pos {Fc : BPoly F} {n : ℕ} {a : F} {c : BranchCert F}
    (h : certCheck Fc n a c = true) : 0 < c.N := by
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- **Finite branch systems from certificates.** -/
theorem hasBranches_of_cert (Fc : BPoly F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB Fc).map (mapRingHom ψ₀)) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (pts : List (F × BranchCert F))
    (hpts : ∀ p ∈ pts, certCheck Fc S.F.natDegree p.1 p.2 = true) (G : CPoly F)
    (hG : resultant (toB Fc) (derivative (toB Fc)) S.F.natDegree (S.F.natDegree - 1) ∣ toPoly G)
    (hcov : coverCheck G (pts.map Prod.fst) = true) : S.HasBranches K := by
  classical
  intro a
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  have hψe : (mapRingHom (algebraMap C K)).comp (mapRingHom ψ₀) = mapRingHom ψ := by
    rw [hψ, Polynomial.mapRingHom_comp]
  set φ : F[X] →+* K := (evalRingHom a).comp (mapRingHom ψ) with hφ
  have hfib : (S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a) = (toB Fc).map φ := by
    rw [hSF, Polynomial.map_map, Polynomial.map_map, RingHom.comp_assoc, hψe]
  by_cases hres : φ (resultant (toB Fc) (derivative (toB Fc)) S.F.natDegree (S.F.natDegree - 1)) = 0
  · -- a special point: use its certificate
    obtain ⟨R, hR⟩ := hG
    have h0 : ((toPoly G).map ψ).eval a = 0 := by
      change φ (toPoly G) = 0
      rw [hR, map_mul, hres, zero_mul]
    obtain ⟨a', ha', rfl⟩ := coverCheck_spec G _ hcov ψ a h0
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨y, -, -, hsplit⟩ := certCheck_spec (K := K) Fc S.F.natDegree hmon hdeg p.1 p.2
      (hpts p hp) ψ₀
    refine ⟨p.2.N, (certCheck_N_pos (hpts p hp)).ne', List.ofFn y, by simp, ?_⟩
    rw [List.map_ofFn, List.prod_ofFn]
    exact (congrArg (fun P ↦ P.map (branchSub p.2.N (ψ p.1))) hSF).trans hsplit
  · -- an unramified fibre: Hensel
    set Fa := (S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a) with hFa
    have hFam : Fa.Monic := (S.monic.map _).map _
    have hFan : Fa.natDegree = S.F.natDegree := by
      rw [hFa, (S.monic.map _).natDegree_map, S.monic.natDegree_map]
    have hres' : resultant Fa (derivative Fa) S.F.natDegree (S.F.natDegree - 1) ≠ 0 := by
      rw [hfib, Polynomial.derivative_map, resultant_map_map]; exact hres
    obtain ⟨b, hbinj, hb⟩ := fibre_distinct_roots Fa hFam hFan S.natDegree_F_ne_zero hres'
    obtain ⟨Y, -, hs⟩ := split_unramified S.F S.monic a b hbinj (fun k ↦ (hb k).1)
      (fun k ↦ by
        rw [fibreAt, ← Polynomial.derivative_map, ← Polynomial.derivative_map]
        exact (hb k).2)
    refine ⟨1, one_ne_zero, List.ofFn Y, by simp, ?_⟩
    rw [List.map_ofFn, List.prod_ofFn]
    exact hs

/-- **The branch system above infinity from a certificate.** -/
theorem hasBranchesInf_of_cert (Fc : BPoly F) (ψ₀ : F →+* C)
    (hSF : S.F = (toB Fc).map (mapRingHom ψ₀)) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree) (c : BranchCert F)
    (h : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 c = true) :
    S.HasBranchesInf K := by
  obtain ⟨w, -, hs⟩ := certInf_spec (K := K) Fc S.F.natDegree hmon hdeg k hok hmon' hn' c h ψ₀
  refine ⟨c.N, (certCheck_N_pos h).ne', List.ofFn fun j ↦ single (-((k * c.N : ℕ) : ℤ)) (1 : K) *
    HahnSeries.ofPowerSeries ℤ K (w j), by simp, ?_⟩
  rw [List.map_ofFn, List.prod_ofFn]
  exact (congrArg (fun P : C[X][X] ↦ P.map (infSub (C := C) (K := K) c.N)) hSF).trans hs

end CurveData

end Cert

end Curves
