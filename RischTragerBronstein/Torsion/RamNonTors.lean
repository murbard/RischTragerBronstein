import RischTragerBronstein.Torsion.RamGood
import RischTragerBronstein.Torsion.NullTest
import RischTragerBronstein.Torsion.PairMult

/-!
# Non-torsion of divisors at places from certificates

`not_torsion_places_of_cert`: a curve over a computable field `K` (characteristic `0`) with the
global certificate, a place certificate, two good primes `p ≠ q` (with prime certificates for the
curve and for the places) and a failed principality test for `(m_p m_q) Γ` over `K`: no multiple
`M Γ − M c ∞ₓ` (`M > 0`) passes the principality test.

`not_torsion_places_map`: the same over any field `C ⊇ K`, as the non-existence of a function with
`div γ ≥ M Γ − M c ∞ₓ` (`DivGE`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section NTP

variable {F : Type*} [Field F] [DecidableEq F]

theorem not_princTest_of_certN' {K : Type*} [Field K] (ψ : F →+* K) (n M P : ℕ) (δL : List ℕ)
    (Bc : List (BPoly F)) (Dc : CPoly F) (αL : List F) (cL : List (BranchCert F))
    (bL : List (List ℕ)) (Lm : List (List F))
    (hchk : nonPrincCheckN n M P δL Bc Dc αL cL bL Lm = true) {m : ℕ} (hm : αL.length = m)
    (Y : Fin m → Fin n → PowerSeries K)
    (hY : ∀ (j : Fin m) (k : Fin n), (PowerSeries.X : PowerSeries K) ^ (cL.getD j ⟨1, [], 0⟩).prec ∣
      Y j k - thetaT ψ (toPoly (((cL.getD j ⟨1, [], 0⟩).ys).getD k []))) :
    ¬ princTest (fun i : Fin n ↦ δL.getD i 0) M (fun q : Fin m × Fin n ↦ (cL.getD q.1 ⟨1, [], 0⟩).N)
      (fun q ↦ ψ (αL.getD q.1 0))
      (fun q i ↦ basisSer (fun i : Fin n ↦ (toB (Bc.getD i [])).map (mapRingHom ψ))
        ((toPoly Dc).map ψ) (cL.getD q.1 ⟨1, [], 0⟩).N (ψ (αL.getD q.1 0))
          (HahnSeries.ofPowerSeries ℤ K (Y q.1 q.2)) i)
      (fun q ↦ (bL.getD q.1 []).getD q.2 0) := by
  subst hm
  exact not_princTest_of_certN ψ n M δL Bc Dc αL cL bL Y P Lm hchk hY

end NTP

section NT

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

lemma PlaceCert.fN_pos {Pc : PlaceCert K} {Fc : BPoly K} {n : ℕ} (hPc : Pc.Facts Fc n) (hn : 0 < n)
    (j : ℕ) (hj : j < Pc.fib.length) : 0 < Pc.fN j := by
  obtain ⟨hπ, -, hs, hN, -⟩ := (hPc.rt j hj).2 0 hn
  rw [hN]; exact Nat.mul_pos hs (hPc.pl _ hπ).2.1

lemma PlaceCert.fα_inj {Pc : PlaceCert K} {Fc : BPoly K} {n : ℕ} (hPc : Pc.Facts Fc n) :
    Function.Injective fun j : Fin Pc.fib.length ↦ Pc.fα j := fun j j' h ↦ by
  by_contra hne
  have := nodup_getD_ne hPc.nd (by simp only [PlaceCert.αs, List.length_map]; exact j.2)
    (by simp only [PlaceCert.αs, List.length_map]; exact j'.2) (Fin.val_ne_of_ne hne) 0
  rw [Pc.αs_getD j j.2, Pc.αs_getD j' j'.2] at this
  exact this h

set_option maxHeartbeats 8000000 in
/-- **Non-torsion at places from certificates.** -/
theorem not_torsion_places_of_cert {L Kb : Type*} [Field L] [Algebra K L] [Field Kb]
    [Algebra K Kb] [IsAlgClosed Kb] (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : T.globalCheckR = true) (Pc : PlaceCert K) (hPc : Pc.check T.Fc T.n = true)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p K) (φp : K →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true) (Qp : PlaceCert.PrimeData p)
    (hQp : Pc.primeCheck Rp T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true)
    (Rq : RedFns q K) (φq : K →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Qq : PlaceCert.PrimeData q)
    (hQq : Pc.primeCheck Rq T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pq.xs Qq = true)
    (Pb : ℕ) (Lm : List (List K))
    (htest : nonPrincOK T.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true) :
    ∀ M : ℕ, 0 < M → ¬ princTest (fun i : Fin S.F.natDegree ↦ T.I.δL.getD i 0) (M * Pc.cΓ)
        (fun q : Fin Pc.fib.length × Fin S.F.natDegree ↦ Pc.fN q.1) (fun q ↦ Pc.fα q.1)
        (fun q i ↦ basisSer (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc) (Pc.fN q.1)
          (Pc.fα q.1) (rCK T.Fc Pc q.1 q.2) i)
        (fun q ↦ M * (Pc.rs q.1 q.2 * Pc.Γp.getD (Pc.rπ q.1 q.2) 0)) := by
  classical
  have hTf := globalCheckR_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  have hnS : S.F.natDegree = T.n := by rw [hSF, hdeg]
  haveI : CharZero Kb := charZero_of_injective_algebraMap (algebraMap K Kb).injective
  have hPc' : Pc.Facts T.Fc S.F.natDegree := by rw [hnS]; exact Pc.check_spec hPc
  have hBS : S.IsIntBasis Kb (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
      (fun j ↦ T.I.δL.getD j 0) := by
    have := ibCheckR_spec (K := Kb) S T.Fc (RingHom.id K)
      (by rw [hSF, Polynomial.mapRingHom_id, Polynomial.map_id]) T.n T.k hnS.symm T.I T.G hTf.ib
      (dvd_of_eq hTf.G_eq.symm)
    simpa only [Polynomial.mapRingHom_id, Polynomial.map_id] using this
  set m := Pc.fib.length with hm
  have hsplit := fun j : Fin m ↦ split_K S T.Fc hSF hmon Pc hPc' j j.2
  -- the failed test
  have hfc : ∀ j : Fin m, (Pc.fcerts S.F.natDegree).getD j ⟨1, [], 0⟩ =
      ⟨Pc.fN j, (List.range S.F.natDegree).map (Pc.apx j), Pc.tp.getD j 0⟩ :=
    fun j ↦ Pc.fcerts_getD _ _ j.2
  have hQp' := PlaceCert.primeCheck_spec Rp hQp
  have hQq' := PlaceCert.primeCheck_spec Rq hQq
  -- the multiplier of the failed test
  obtain ⟨mt, hmt, htestM⟩ : ∃ mt : ℕ, (∀ v w : ℕ, Nat.gcd (Qp.mp * p ^ v) (Qq.mp * q ^ w) ∣ mt) ∧
      nonPrincOK T.n (mt * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs (Pc.fcerts T.n) (Pc.bL T.n mt)
        Lm = true := by
    rcases htest with h | h
    · exact ⟨_, CurveData.gcd_dvd_mul_primes Fact.out Fact.out hpq _ _, h⟩
    · exact ⟨_, dvd_pairMult Fact.out Fact.out hpq hQp'.mp hQq'.mp, h⟩
  have htest' := htestM
  rw [← hnS] at htest'
  have hnp := not_princTest_of_nonPrincOK (RingHom.id K) S.F.natDegree (mt * Pc.cΓ) Pb
    T.I.δL T.I.Bc T.I.Dc Pc.αs (Pc.fcerts _) (Pc.bL _ mt) Lm htest' (m := m)
    (by simp [PlaceCert.αs, hm])
    (fun j k ↦ conjPS (Pc.rζ j k) (Pc.rs j k) (repK T.Fc Pc (Pc.rπ j k))) (fun j k ↦ by
      rw [hfc]
      show (PowerSeries.X : PowerSeries K) ^ Pc.tp.getD j 0 ∣ _ - thetaT (RingHom.id K)
        (toPoly (((List.range S.F.natDegree).map (Pc.apx j)).getD k []))
      have e2 : ((List.range S.F.natDegree).map (Pc.apx j)).getD k [] = Pc.apx j k := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
      rw [e2]
      obtain ⟨hπ, -, hs, -, -, htp⟩ := (hPc'.rt j j.2).2 k k.2
      exact conj_approx (RingHom.id K) (Pc.rζ j k) hs _ _
        (repK_spec T.Fc Pc _ (hPc'.pl _ hπ).2.2).2 htp)
  have htestC : ¬ princTest (fun i : Fin S.F.natDegree ↦ T.I.δL.getD i 0)
      (mt * Pc.cΓ) (fun q : Fin m × Fin S.F.natDegree ↦ Pc.fN q.1)
      (fun q ↦ Pc.fα q.1)
      (fun q i ↦ basisSer (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc) (Pc.fN q.1)
        (Pc.fα q.1) (rCK T.Fc Pc q.1 q.2) i)
      (fun q ↦ mt * (Pc.rs q.1 q.2 * Pc.Γp.getD (Pc.rπ q.1 q.2) 0)) := fun h ↦
    hnp (princTest_congr (fun i ↦ rfl) (fun q ↦ by rw [hfc])
      (fun q ↦ by rw [Pc.αs_getD _ q.1.2]; rfl)
      (fun q i ↦ by
        simp only [hfc, Polynomial.mapRingHom_id, Polynomial.map_id, RingHom.id_apply,
          Pc.αs_getD _ q.1.2]
        rfl)
      (fun q ↦ by rw [Pc.bL_getD _ _ _ _ q.1.2 q.2.2]) h)
  have hdΓ : ∀ j : Fin m, ∑ k : Fin S.F.natDegree, Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 =
      Pc.fN j * Pc.dΓ.getD j 0 := fun j ↦ by
    rw [← (hPc'.dΓ j j.2).1]
    exact Fin.sum_univ_eq_sum_range (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) _
  have hsumΓ : ∑ j : Fin m, Pc.dΓ.getD j 0 = Pc.cΓ * S.F.natDegree := by
    rw [← hPc'.sum]
    exact Fin.sum_univ_eq_sum_range (fun j ↦ Pc.dΓ.getD j 0) _
  exact S.not_torsion_places_mt (K := Kb) S.hasBranches S.hasBranchesInf hBS
    (fun j : Fin m ↦ Pc.fα j) (PlaceCert.fα_inj hPc') (fun j ↦ Pc.fN j)
    (fun j ↦ PlaceCert.fN_pos hPc' (by rw [hnS]; exact hn0) j j.2)
    (fun j k ↦ rCK T.Fc Pc j k) (fun j ↦ (hsplit j).1)
    (fun j ↦ (lmap_injective _).comp (hsplit j).2)
    (fun j k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) Pc.cΓ (fun j ↦ Pc.dΓ.getD j 0) hdΓ hsumΓ
    p q (Fact.out) (Fact.out) hpq Qp.mp Qq.mp hQp'.mp hQq'.mp
    (hstep_places_of_prime (Kb := Kb) Rp φp hRp S T hSF hTf Pp (primeCheck_spec Rp hPp) Pc hPc' Qp hQp)
    (hstep_places_of_prime (Kb := Kb) Rq φq hRq S T hSF hTf Pq (primeCheck_spec Rq hPq) Pc hPc' Qq hQq)
    mt hmt htestC

end NT

section NTM

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- The certified roots above `α_j` over `C ⊇ F`. -/
noncomputable def rCC {C : Type*} [Field C] (ι : F →+* C) (Fc : BPoly F) (Pc : PlaceCert F)
    (j k : ℕ) : LaurentSeries C :=
  lmap ι (rCK Fc Pc j k)

/-- **The splitting of the fibres over `C ⊇ F`.** -/
theorem split_places_map {C L : Type*} [Field C] [Field L] [Algebra C L] (S : CurveData C L)
    (ι : F →+* C) (Fc : BPoly F) (hmon : (toB Fc).Monic) (hSF : S.F = (toB Fc).map (mapRingHom ι))
    (Pc : PlaceCert F) (hPc : Pc.Facts Fc (toB Fc).natDegree) (j : ℕ) (hj : j < Pc.fib.length) :
    S.F.map (branchSub (C := C) (K := C) (Pc.fN j) (ι (Pc.fα j))) =
        ∏ k : Fin S.F.natDegree, (X - Polynomial.C (rCC ι Fc Pc j k)) ∧
      Function.Injective fun k : Fin S.F.natDegree ↦ rCC ι Fc Pc j k := by
  classical
  have hnS : S.F.natDegree = (toB Fc).natDegree := by rw [hSF, hmon.natDegree_map]
  obtain ⟨-, hrt⟩ := hPc.rt j hj
  have hinj0 : Function.Injective fun k : Fin (toB Fc).natDegree ↦ rCK Fc Pc j k :=
    conj_inj (RingHom.id F) (tp := Pc.tp.getD j 0)
      (fun k : Fin (toB Fc).natDegree ↦ conjPS (Pc.rζ j k) (Pc.rs j k) (repK Fc Pc (Pc.rπ j k)))
      (fun k ↦ Pc.apx j k) (fun k ↦ by
        obtain ⟨hπ, -, hs, -, -, htp⟩ := hrt k k.2
        obtain ⟨-, hd⟩ := repK_spec Fc Pc (Pc.rπ j k) (hPc.pl _ hπ).2.2
        exact conj_approx (RingHom.id F) (Pc.rζ j k) hs _ _ hd htp)
      (fun k l hkl ↦ PlaceCert.sepCheckP_spec Pc hPc.sep j hj k l k.2 l.2 (Fin.val_ne_of_ne hkl))
  have hsp : (toB Fc).map (branchSub (C := F) (K := F) (Pc.fN j) (Pc.fα j)) =
      ∏ k : Fin (toB Fc).natDegree, (X - Polynomial.C (rCK Fc Pc j k)) := by
    refine split_of_roots _ hmon rfl _ _ _ (fun k ↦ ?_) hinj0
    obtain ⟨hπ, hpj, hs, hN, hζ, -⟩ := hrt k k.2
    have hN0 : 0 < Pc.fN j := by rw [hN]; exact Nat.mul_pos hs (hPc.pl _ hπ).2.1
    obtain ⟨hr, -⟩ := repK_spec Fc Pc (Pc.rπ j k) (hPc.pl _ hπ).2.2
    rw [hpj] at hr
    exact conj_root _ _ _ _ hs hN _ (ne_zero_of_pow_eq_one hN0 hζ) hζ _ _ hr
  have hinj : Function.Injective fun k : Fin S.F.natDegree ↦ rCC ι Fc Pc j k := by
    intro k l hkl
    have h1 : rCK Fc Pc j k = rCK Fc Pc j l := lmap_injective ι hkl
    have := hinj0 (a₁ := Fin.cast hnS k) (a₂ := Fin.cast hnS l) h1
    exact Fin.ext (by simpa using congrArg Fin.val this)
  refine ⟨?_, hinj⟩
  have h1 := split_map ι (toB Fc) _ _ _ hsp
  rw [← prod_cast hnS (fun k ↦ X - Polynomial.C (lmap ι (rCK Fc Pc j k)))] at h1
  exact (congrArg (fun Q : C[X][X] ↦ Q.map (branchSub (C := C) (K := C) (Pc.fN j) (ι (Pc.fα j))))
    hSF).trans h1

set_option maxHeartbeats 8000000 in
/-- **Non-torsion at places over any extension.** -/
theorem not_torsion_places_map {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb]
    [Algebra C Kb] [IsAlgClosed Kb] (S : CurveData C L) (ι : F →+* C) (T : GlobalCert F)
    (hSF : S.F = (toB T.Fc).map (mapRingHom ι)) (hT : T.globalCheckR = true)
    (Pc : PlaceCert F) (hPc : Pc.check T.Fc T.n = true)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true) (Qp : PlaceCert.PrimeData p)
    (hQp : Pc.primeCheck Rp T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Qq : PlaceCert.PrimeData q)
    (hQq : Pc.primeCheck Rq T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pq.xs Qq = true)
    (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincOK T.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true)
    (M : ℕ) (hM : 0 < M) (hN : ∀ j : Fin Pc.fib.length, 0 < Pc.fN j)
    (hlf : ∀ j : Fin Pc.fib.length, S.F.map (branchSub (Pc.fN j) (algebraMap C Kb (ι (Pc.fα j)))) =
      ((List.ofFn fun k : Fin S.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ι T.Fc Pc j k)).map
        fun r ↦ X - Polynomial.C r).prod) :
    ¬ ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧ S.DivGE (fun j : Fin Pc.fib.length ↦ ι (Pc.fα j))
      (fun j ↦ Pc.fN j) hN
      (fun j ↦ List.ofFn fun k : Fin S.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ι T.Fc Pc j k))
      hlf (fun j r ↦ M * Function.extend
        (fun k : Fin S.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ι T.Fc Pc j k))
        (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) 0 r) (M * Pc.cΓ) γ := by
  classical
  have hTf := globalCheckR_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  -- the curve over `F`
  have hirr : Irreducible ((toB T.Fc).map (algebraMap F[X] (RatFunc F))) :=
    (irr_all Rp φp hRp T hTf Pp (primeCheck_spec Rp hPp)).2.2
  set S0 := stdCurve (toB T.Fc) hmon (by rw [hdeg]; exact hn0) hirr with hS0
  have hS0n : S0.F.natDegree = T.n := by show (toB T.Fc).natDegree = T.n; exact hdeg
  have hnS : S.F.natDegree = S0.F.natDegree := by
    rw [hS0n, hSF, hmon.natDegree_map, hdeg]
  have hNT := not_torsion_places_of_cert (Kb := AlgebraicClosure F) S0 T rfl hT Pc hPc hpq
    Rp φp hRp Pp hPp Qp hQp Rq φq hRq Pq hPq Qq hQq Pb Lm htest M hM
  rintro ⟨γ, hγ0, hγ⟩
  apply hNT
  have hPc0 : Pc.Facts T.Fc S0.F.natDegree := by rw [hS0n]; exact Pc.check_spec hPc
  have hPcd : Pc.Facts T.Fc (toB T.Fc).natDegree := by rw [hdeg]; exact Pc.check_spec hPc
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
  set m := Pc.fib.length with hm
  have hspC := fun j : Fin m ↦ split_places_map S ι T.Fc hmon hSF Pc hPcd j j.2
  have hsp0 := fun j : Fin m ↦ split_K S0 T.Fc rfl hmon Pc hPc0 j j.2
  -- the test over `C`
  have hinjK : ∀ j : Fin m, Function.Injective fun k : Fin S.F.natDegree ↦
      lmap (algebraMap C Kb) (rCC ι T.Fc Pc j k) := fun j ↦ (lmap_injective _).comp (hspC j).2
  have htestC := (S.principal_iff_test hBS (fun j : Fin m ↦ ι (Pc.fα j)) (fun j ↦ Pc.fN j) hN
    (fun j k ↦ rCC ι T.Fc Pc j k) (fun j ↦ (hspC j).1)
    (fun j k ↦ M * (Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0))
    (fun j r ↦ M * Function.extend
      (fun k : Fin S.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ι T.Fc Pc j k))
      (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) 0 r)
    (fun j k ↦ by rw [(hinjK j).extend_apply]) (M * Pc.cΓ)).mp ⟨γ, hγ0, hγ⟩
  have hσ : ∀ (q : Fin m × Fin S0.F.natDegree) i,
      LowerBd (basisSer (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc) (Pc.fN q.1) (Pc.fα q.1)
        (rCK T.Fc Pc q.1 q.2) i) 0 :=
    fun q i ↦ S0.basisSer_lowerBd_N hB0 _ (hN q.1) _ _ (hsp0 q.1).1 q.2 i
  exact (princTest_transport_N S0 S ι hnS (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
    (fun j ↦ T.I.δL.getD j 0) (fun j ↦ (toB (T.I.Bc.getD j [])).map (mapRingHom ι))
    ((toPoly T.I.Dc).map ι) (fun _ ↦ rfl) rfl (fun j : Fin m ↦ Pc.fN j)
    (fun j : Fin m ↦ Pc.fα j) (fun j : Fin m ↦ ι (Pc.fα j)) (fun _ ↦ rfl)
    (fun j k ↦ rCK T.Fc Pc j k) (fun j k ↦ rCC ι T.Fc Pc j k) (fun _ _ ↦ rfl) hσ
    (fun j k ↦ M * (Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0)) (M * Pc.cΓ)).mpr htestC

end NTM

end Curves
