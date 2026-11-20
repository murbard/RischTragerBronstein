import RischTragerBronstein.Torsion.GoodPrimeStep

/-!
# Non-torsion from certificates

`not_torsion_of_cert`: a curve over a computable field `K` of characteristic `0` with the global
certificate, two good primes `p ≠ q` (with certified reductions and prime certificates) and a
failed principality test for `(m_p m_q) Γ` over `K`: no multiple `M Γ − M c ∞ₓ` (`M > 0`) is the
divisor of a function (`DivGEU`). Everything is checked by `globalCheck`, `primeCheck` and
`nonPrincCheck`.
-/

open Polynomial IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section NT

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

set_option maxHeartbeats 4000000 in
/-- **Non-torsion from certificates.** -/
theorem not_torsion_of_cert {L Kb : Type*} [Field L] [Algebra K L] [Field Kb] [Algebra K Kb]
    [IsAlgClosed Kb] (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : T.globalCheck = true) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p K) (φp : K →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true)
    (Rq : RedFns q K) (φq : K →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Pb : ℕ) (Lm : List (List K))
    (htest : nonPrincCheck T.n ((Pp.mp * Pq.mp) * T.cdeg) Pb T.I.δL T.I.Bc T.I.Dc T.αL T.cΓ
      (T.ΓL.map (·.map ((Pp.mp * Pq.mp) * ·))) Lm = true) :
    ∀ M : ℕ, 0 < M → ¬ ∃ γ : K⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGEU (K := Kb) (fun j : Fin T.αL.length ↦ T.αL.getD j 0)
        (fun j (k : Fin S.F.natDegree) ↦ (T.yL.getD j []).getD k 0)
        (fun j k ↦ M * (T.ΓL.getD j []).getD k 0) (M * T.cdeg) γ := by
  classical
  have hTf := globalCheck_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  have hnS : S.F.natDegree = T.n := by rw [hSF, hdeg]
  haveI : CharZero Kb := charZero_of_injective_algebraMap (algebraMap K Kb).injective
  -- the integral basis over `K`
  have hBS : S.IsIntBasis Kb (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
      (fun j ↦ T.I.δL.getD j 0) := by
    have := ibCheckR_spec (K := Kb) S T.Fc (RingHom.id K)
      (by rw [hSF, Polynomial.mapRingHom_id, Polynomial.map_id]) T.n T.k hnS.symm T.I T.G hTf.ib
      (dvd_of_eq hTf.G_eq.symm)
    simpa only [Polynomial.mapRingHom_id, Polynomial.map_id] using this
  -- the branches at the points of `Γ`
  obtain ⟨hyl, hαnd, hptK⟩ := ptCheck_spec (RingHom.id K) (n := S.F.natDegree) hmon
    (by rw [hdeg, hnS]) (by rw [hnS]; exact hTf.pt)
  have hY0 : ∀ j : Fin T.αL.length, ∃ Y : Fin S.F.natDegree → PowerSeries K,
      (∀ k, PowerSeries.constantCoeff (Y k) = (T.yL.getD j []).getD k 0) ∧
      S.F.map (branchSub (C := K) (K := K) 1 (T.αL.getD j 0)) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ K (Y k))) ∧
      ∀ k : Fin S.F.natDegree, (PowerSeries.X : PowerSeries K) ^ (T.cΓ.getD j (dcert K)).prec ∣
        Y k - thetaT (RingHom.id K) (toPoly ((T.cΓ.getD j (dcert K)).ys.getD k [])) := by
    intro j
    obtain ⟨Y, hYc, hYs, hYt, -⟩ := (hptK j j.2).2
    refine ⟨Y, hYc, ?_, hYt⟩
    rw [Polynomial.mapRingHom_id, Polynomial.map_id, RingHom.id_apply] at hYs
    exact (congrArg (fun Q : K[X][X] ↦ Q.map (branchSub (C := K) (K := K) 1 (T.αL.getD j 0)))
      hSF).trans hYs
  choose Y0 hY0c hsp hY0t using hY0
  have hylen : ∀ j : Fin T.αL.length, (T.yL.getD j []).length = S.F.natDegree :=
    fun j ↦ (hptK j j.2).1.1
  have hyinj : ∀ j : Fin T.αL.length, Function.Injective fun k : Fin S.F.natDegree ↦
      (T.yL.getD j []).getD k 0 := fun j k k' h ↦ by
    by_contra hne
    exact nodup_getD_ne (hptK j j.2).1.2 (by rw [hylen]; exact k.2) (by rw [hylen]; exact k'.2)
      (Fin.val_ne_of_ne hne) 0 h
  have hαinj : Function.Injective fun j : Fin T.αL.length ↦ T.αL.getD j 0 := fun j j' h ↦ by
    by_contra hne
    exact nodup_getD_ne hαnd j.2 j'.2 (Fin.val_ne_of_ne hne) 0 h
  -- the sum of `Γ`
  have hsumΓ : ∑ j : Fin T.αL.length, ∑ k : Fin S.F.natDegree, (T.ΓL.getD j []).getD k 0 =
      T.cdeg * S.F.natDegree := by
    have e : ∀ j : ℕ, ∑ k : Fin S.F.natDegree, (T.ΓL.getD j []).getD k 0 =
        ∑ k ∈ Finset.range T.n, (T.ΓL.getD j []).getD k 0 := fun j ↦ by
      rw [Fin.sum_univ_eq_sum_range (fun k ↦ (T.ΓL.getD j []).getD k 0), hnS]
    simp only [e]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ∑ k ∈ Finset.range T.n, (T.ΓL.getD j []).getD k 0),
      hTf.sum, hnS]
  -- the failed test
  have hb : ∀ (j : Fin T.αL.length) (k : Fin S.F.natDegree),
      ((T.ΓL.map (·.map ((Pp.mp * Pq.mp) * ·))).getD j []).getD k 0 =
        (Pp.mp * Pq.mp) * (T.ΓL.getD j []).getD k 0 := fun j k ↦ by
    rw [getD_map_lt _ _ _ (by rw [hTf.Γl]; exact j.2) []]
    by_cases hk : (k : ℕ) < (T.ΓL.getD j []).length
    · rw [getD_map_lt _ _ _ hk 0]
    · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        List.getD_eq_default _ _ (by omega), mul_zero]
  have hnp := not_princTest_of_cert (RingHom.id K) S.F.natDegree ((Pp.mp * Pq.mp) * T.cdeg)
    T.I.δL T.I.Bc T.I.Dc T.αL T.cΓ (T.ΓL.map (·.map ((Pp.mp * Pq.mp) * ·))) Y0 Pb Lm
    (by rw [hnS]; exact htest) hY0t
  simp only [Polynomial.mapRingHom_id, Polynomial.map_id, RingHom.id_apply, hb] at hnp
  exact S.not_torsion_unram S.hasBranches S.hasBranchesInf hBS
    (fun j : Fin T.αL.length ↦ T.αL.getD j 0) hαinj
    (fun (j : Fin T.αL.length) (k : Fin S.F.natDegree) ↦ (T.yL.getD j []).getD k 0) Y0 hY0c hsp
    hyinj (fun (j : Fin T.αL.length) (k : Fin S.F.natDegree) ↦ (T.ΓL.getD j []).getD k 0) T.cdeg
    hsumΓ p q (Fact.out) (Fact.out) hpq
    Pp.mp Pq.mp (primeCheck_spec Rp hPp).mp (primeCheck_spec Rq hPq).mp
    (hstep_of_prime Rp φp hRp S T hSF hTf Pp (primeCheck_spec Rp hPp))
    (hstep_of_prime Rq φq hRq S T hSF hTf Pq (primeCheck_spec Rq hPq)) hnp

end NT

end Curves
