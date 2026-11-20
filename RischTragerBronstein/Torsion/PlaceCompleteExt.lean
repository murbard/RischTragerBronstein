import RischTragerBronstein.Torsion.PlaceComplete
import RischTragerBronstein.Torsion.PrimeEv2

/-!
# The multiplier `m_p` does not depend on the precision of the place certificate

`exists_placeWit_ext`: the multiplier `m_p` of `exists_placeWit` is obtained from the exact
branches modulo `p`, which are the same for every *refinement* `Pc'` of the place certificate `Pc`
(same fibres, places, roots and multiplicities; longer approximations extending those of `Pc`).
So a single `m_p` works for all refinements: at every refinement with enough precision for `m_p`
(`testSideN`), the kernel search `placeWit` at `m_p` succeeds. The integral roots of a
refinement are those of `Pc` (`zp_root_eq`, uniqueness of Hensel roots).

This breaks the circularity between the precision of the place certificate and `m_p`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section Step

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

local notation "𝕜" => IsLocalRing.ResidueField ℤ_[p]
local notation "ρ" => IsLocalRing.residue ℤ_[p]
local notation "ι" => algebraMap ℤ_[p] ℚ_[p]

/-- **Integral roots are determined by approximations.** -/
lemma zp_root_eq (Fc : BPoly K) (hokF : ∀ P ∈ Fc, ∀ c ∈ P, R.ok c = true) (a : K)
    (hoka : R.ok a = true) {e prec prec' : ℕ} {y y' : CPoly K} (hoky : ∀ c ∈ y, R.ok c = true)
    (h : rootCheck Fc a e prec y = true) (ρ1 ρ2 : PowerSeries ℤ_[p])
    (h1 : ((toB (liftBL R φ hR Fc)).map (psSubR e (zL R φ hR a))).eval ρ1 = 0)
    (h2 : ((toB (liftBL R φ hR Fc)).map (psSubR e (zL R φ hR a))).eval ρ2 = 0)
    (hd1 : (PowerSeries.X : PowerSeries ℤ_[p]) ^ prec ∣
        ρ1 - ((toPoly (liftL R φ hR y) : ℤ_[p][X]) : PowerSeries ℤ_[p]))
    (hpp : prec ≤ prec') (hoky' : ∀ c ∈ y', R.ok c = true)
    (hag : ∀ i < prec, y'.getD i 0 = y.getD i 0)
    (hd2 : (PowerSeries.X : PowerSeries ℤ_[p]) ^ prec' ∣
        ρ2 - ((toPoly (liftL R φ hR y') : ℤ_[p][X]) : PowerSeries ℤ_[p])) : ρ1 = ρ2 := by
  have hιi : Function.Injective ι := IsFractionRing.injective ℤ_[p] ℚ_[p]
  have hFι : (toB (liftBL R φ hR Fc)).map (mapRingHom ι) = (toB Fc).map (mapRingHom φ) :=
    toB_liftBL_map R φ hR _ hokF
  have hαι : ι (zL R φ hR a) = φ a := zL_map R φ hR hoka
  have heq : PowerSeries.map ι ρ1 = PowerSeries.map ι ρ2 := by
    refine rep_unique φ h _ _ ?_ ?_ ?_ ?_
    · have := congrArg (PowerSeries.map ι) h1
      rw [map_eval_psSubR, hFι, hαι, map_zero] at this
      exact this
    · have := congrArg (PowerSeries.map ι) h2
      rw [map_eval_psSubR, hFι, hαι, map_zero] at this
      exact this
    · have := map_dvd (PowerSeries.map ι) hd1
      rwa [map_pow, PowerSeries.map_X, map_sub, map_coe_poly, toPoly_liftL_map R φ hR _ hoky,
        ← thetaT_apply] at this
    · have h3 := map_dvd (PowerSeries.map ι) hd2
      rw [map_pow, PowerSeries.map_X, map_sub, map_coe_poly, toPoly_liftL_map R φ hR _ hoky',
        ← thetaT_apply] at h3
      have h4 := X_pow_dvd_thetaT_sub φ y' y prec fun j hj ↦ by
        rw [coeff_toPoly, coeff_toPoly, hag j hj]
      have := dvd_add ((pow_dvd_pow _ hpp).trans h3) h4
      rwa [sub_add_sub_cancel] at this
  ext n
  apply hιi
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map, heq]

set_option maxHeartbeats 16000000 in
include φ hR in
/-- **One multiplier `m_p` for all refinements of the place certificate.** -/
theorem exists_placeWit_ext {L : Type*} [Field L] [Algebra K L]
    (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P)
    (Pc : PlaceCert K) (hPc : Pc.Facts T.Fc S.F.natDegree)
    (hpre : Pc.primePre R T.Fc T.n T.I.Dc P.xs = true) :
    ∃ mm : ℕ, 0 < mm ∧ ∀ Pc' : PlaceCert K, Pc'.fib = Pc.fib → Pc'.rt = Pc.rt →
      Pc'.Γp = Pc.Γp → Pc'.cΓ = Pc.cΓ → Pc'.pl.length = Pc.pl.length →
      (∀ π < Pc.pl.length, Pc'.pj π = Pc.pj π ∧ Pc'.pe π = Pc.pe π ∧ Pc.pp π ≤ Pc'.pp π ∧
        ∀ i < Pc.pp π, (Pc'.py π).getD i 0 = (Pc.py π).getD i 0) →
      Pc'.Facts T.Fc S.F.natDegree → Pc'.primePre R T.Fc T.n T.I.Dc P.xs = true →
      testSideN T.n (T.I.Dc.map R.red) (Pc'.map R.red).αs ((Pc'.map R.red).fcerts T.n)
        ((Pc'.map R.red).bL T.n mm) = true →
      (placeWit T.n T.I.δL (T.I.Bc.map (redBL R)) (T.I.Dc.map R.red) (Pc'.map R.red) mm).isSome := by
  classical
  obtain ⟨hn0, hmon, hdeg, hok, hmon', hn'⟩ := hT.shape
  have hnS : S.F.natDegree = T.n := by rw [hSF, hdeg]
  have hokF := okB_spec R hP.okF
  have hιi : Function.Injective ι := IsFractionRing.injective ℤ_[p] ℚ_[p]
  -- the checks modulo `p`
  have hibp := hP.ib
  simp only [ibCheck, Bool.and_eq_true] at hibp
  obtain ⟨⟨⟨⟨⟨⟨hshp, -⟩, -⟩, hptsp⟩, hcovp⟩, hcinfp⟩, -⟩ := hibp
  obtain ⟨-, hmonp, hdegp, hokp, hmon'p, hn'p⟩ := shapeCheck_spec hshp
  set Fp := redBL R T.Fc with hFp
  -- the integral model
  set FO : ℤ_[p][X][X] := toB (liftBL R φ hR T.Fc) with hFO
  have hFι : FO.map (mapRingHom ι) = (toB T.Fc).map (mapRingHom φ) := toB_liftBL_map R φ hR _ hokF
  have hFz : FO.map (mapRingHom PadicInt.toZMod) = toB Fp := toB_liftBL_red R φ hR _ hokF
  have hFm : FO.Monic := Polynomial.monic_of_injective (Polynomial.map_injective _ hιi)
    (by rw [hFι]; exact hmon.map _)
  have hFdeg : FO.natDegree = T.n := by
    rw [← natDegree_map_eq_of_injective (f := mapRingHom ι) (Polynomial.map_injective _ hιi), hFι,
      hmon.natDegree_map, hdeg]
  have hFk : FO.map (mapRingHom ρ) = (toB Fp).map (mapRingHom psiP) := by
    rw [mapRingHom_residue, ← Polynomial.map_map, hFz]
  obtain ⟨-, hSki, -⟩ := irr_all R φ hR T hT P hP
  -- the curve over `𝕜`
  have hSkm : (FO.map (mapRingHom ρ)).Monic := hFm.map _
  have hSkd : 0 < (FO.map (mapRingHom ρ)).natDegree := by rw [hFm.natDegree_map, hFdeg]; exact hn0
  set Sk := stdCurve (FO.map (mapRingHom ρ)) hSkm hSkd hSki with hSk
  have hSkn : Sk.F.natDegree = T.n := by
    show (FO.map (mapRingHom ρ)).natDegree = T.n
    rw [hFm.natDegree_map, hFdeg]
  have hSkF : Sk.F = (toB Fp).map (mapRingHom psiP) := hFk
  have hGp : toPoly (T.G.map R.red) = resultant (toB Fp) (derivative (toB Fp)) T.n (T.n - 1) *
      toPoly (T.I.Dc.map R.red) *
      (Matrix.of fun (i j : Fin T.n) ↦ (toB ((T.I.Bc.map (redBL R)).getD j [])).coeff i).det :=
    cover_red R φ hR T.Fc T.n T.I.Dc T.I.Bc T.G hT.G_eq hokF hP.okD
      (fun W hW ↦ okB_spec R (hP.okBc W hW)) hP.okG
  -- branch systems modulo `p`
  have hBrk : Sk.HasBranches (AlgebraicClosure 𝕜) := by
    refine Sk.hasBranches_of_cert Fp psiP hSkF hmonp (by rw [hdegp, hSkn])
      (P.pts.map fun q ↦ (q.1, q.2.1)) (fun q hq ↦ ?_) (T.G.map R.red) ?_ ?_
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      rw [hSkn]
      exact (Bool.and_eq_true _ _ ▸ (List.all_eq_true.mp hptsp q' hq')).1
    · rw [hSkn, hGp, mul_assoc]; exact dvd_mul_right _ _
    · rw [List.map_map]; exact hcovp
  have hBIk : Sk.HasBranchesInf (AlgebraicClosure 𝕜) := by
    refine Sk.hasBranchesInf_of_cert Fp psiP hSkF hmonp (by rw [hdegp, hSkn]) T.k
      (by rw [hSkn]; exact hokp) (by rw [hSkn]; exact hmon'p) (by rw [hSkn]; exact hn'p) P.infc
      (by rw [hSkn]; exact hcinfp)
  -- the integral basis modulo `p`
  have hokB : ∀ j, ∀ P' ∈ T.I.Bc.getD j [], ∀ c ∈ P', R.ok c = true := fun j P' hP' c hc ↦ by
    by_cases hj : j < T.I.Bc.length
    · rw [List.getD_eq_getElem _ _ hj] at hP'
      exact okB_spec R (hP.okBc _ (List.getElem_mem hj)) P' hP' c hc
    · rw [List.getD_eq_default _ _ (by omega)] at hP'; simp at hP'
  have hredB : ∀ j, (T.I.Bc.map (redBL R)).getD j [] = redBL R (T.I.Bc.getD j []) := fun j ↦ by
    cases h : T.I.Bc[j]? <;> simp [List.getD_eq_getElem?_getD, h, redBL]
  set B : ℕ → ℤ_[p][X][X] := fun j ↦ toB (liftBL R φ hR (T.I.Bc.getD j [])) with hB
  set D : ℤ_[p][X] := toPoly (liftL R φ hR T.I.Dc) with hD
  have hBρ : ∀ j, (B j).map (mapRingHom ρ) =
      (toB ((T.I.Bc.map (redBL R)).getD j [])).map (mapRingHom psiP) := fun j ↦ by
    rw [mapRingHom_residue, ← Polynomial.map_map, toB_liftBL_red R φ hR _ (hokB j), hredB]
    rfl
  have hDρ : D.map ρ = (toPoly (T.I.Dc.map R.red)).map psiP := by
    rw [← coe_mapRingHom, mapRingHom_residue, RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom,
      toPoly_liftL_red R φ hR _ hP.okD]
  have hBk : Sk.IsIntBasis (AlgebraicClosure 𝕜)
      (fun j ↦ (toB ((T.I.Bc.map (redBL R)).getD j [])).map (mapRingHom psiP))
      ((toPoly (T.I.Dc.map R.red)).map psiP) (fun j ↦ T.I.δL.getD j 0) :=
    ibCheck_spec Sk Fp psiP hSkF T.n T.k hSkn.symm (P.Ip R T) (T.G.map R.red) hP.ib (dvd_of_eq hGp.symm)
  have hBk' : Sk.IsIntBasis (AlgebraicClosure 𝕜) (fun j ↦ (B j).map (mapRingHom ρ)) (D.map ρ)
      (fun j ↦ T.I.δL.getD j 0) := by
    simp only [hBρ, hDρ]; exact hBk
  -- the places
  have hpre' := hpre
  simp only [PlaceCert.primePre, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hpre'
  obtain ⟨⟨⟨⟨⟨⟨okα, oky⟩, okζ⟩, hαnd'⟩, hαp⟩, hunit⟩, sepp⟩ := hpre'
  set m := Pc.fib.length with hm
  set np := Pc.pl.length with hnp
  have hn0S : 0 < S.F.natDegree := by rw [hnS]; exact hn0
  have hfαok : ∀ j < m, R.ok (Pc.fα j) = true := fun j hj ↦ okα _ (by
    rw [← Pc.αs_getD j hj, List.getD_eq_getElem _ _ (by simpa [PlaceCert.αs] using hj)]
    exact List.getElem_mem _)
  set pjF : Fin np → Fin m := fun π ↦ ⟨Pc.pj π, (hPc.pl π π.2).1⟩ with hpjF
  set αO : Fin m → ℤ_[p] := fun j ↦ zL R φ hR (Pc.fα j) with hαO
  have hρ : ∀ π : Fin np, ∃ ρO : PowerSeries ℤ_[p],
      (FO.map (psSubR (Pc.pe π) (αO (pjF π)))).eval ρO = 0 ∧
      (PowerSeries.X : PowerSeries ℤ_[p]) ^ Pc.pp π ∣
        ρO - ((toPoly (liftL R φ hR (Pc.py π)) : ℤ_[p][X]) : PowerSeries ℤ_[p]) := fun π ↦
    rep_root_Zp R φ hR T.Fc hokF _ (hfαok _ (hPc.pl π π.2).1) (oky π π.2)
      (hPc.pl π π.2).2.2 (by simpa using hunit π π.2)
  choose ρO hρO hdO using hρ
  have hrt := hPc.rt
  have hkn : ∀ k : Fin Sk.F.natDegree, (k : ℕ) < S.F.natDegree := fun k ↦ by
    rw [hnS, ← hSkn]; exact k.2
  have hkT : ∀ k : Fin Sk.F.natDegree, (k : ℕ) < T.n := fun k ↦ by rw [← hSkn]; exact k.2
  set πr : Fin m → Fin Sk.F.natDegree → Fin np := fun j k ↦
    ⟨Pc.rπ j k, ((hrt j j.2).2 k (hkn k)).1⟩ with hπrdef
  have hπr : ∀ j k, pjF (πr j k) = j := fun j k ↦ Fin.ext ((hrt j j.2).2 k (hkn k)).2.1
  have hsr : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), 0 < Pc.rs j k := fun j k ↦
    ((hrt j j.2).2 k (hkn k)).2.2.1
  have hNr : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), Pc.fN j = Pc.rs j k * Pc.pe (πr j k) :=
    fun j k ↦ ((hrt j j.2).2 k (hkn k)).2.2.2.1
  have hNpos : ∀ j : Fin m, 0 < Pc.fN j := fun j ↦ by
    obtain ⟨hπ, -, hs, hN, -⟩ := (hrt j j.2).2 0 hn0S
    rw [hN]; exact Nat.mul_pos hs (hPc.pl _ hπ).2.1
  set ζO : Fin m → Fin Sk.F.natDegree → ℤ_[p] := fun j k ↦ zL R φ hR (Pc.rζ j k) with hζOdef
  have hζok : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), R.ok (Pc.rζ j k) = true := fun j k ↦
    okζ j j.2 k (hkT k)
  have hζι : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), ι (ζO j k) = φ (Pc.rζ j k) := fun j k ↦
    zL_map R φ hR (hζok j k)
  have hζρ : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), ρ (ζO j k) = psiP (R.red (Pc.rζ j k)) :=
    fun j k ↦ by rw [residue_eq_psiP, zL_red R φ hR (hζok j k)]
  have hζO : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), ζO j k ^ Pc.fN j = 1 := fun j k ↦ hιi (by
    rw [map_pow, map_one, hζι, ← map_pow, ((hrt j j.2).2 k (hkn k)).2.2.2.2.1, map_one])
  have hζk : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), ρ (ζO j k) ≠ 0 := fun j k ↦
    ne_zero_of_pow_eq_one (hNpos j) (by rw [← map_pow, hζO, map_one])
  have hrootO : ∀ (j : Fin m) (k : Fin Sk.F.natDegree),
      (FO.map (psSubR (Pc.pe (πr j k)) (αO j))).eval (ρO (πr j k)) = 0 := fun j k ↦ by
    have := hρO (πr j k)
    rwa [hπr] at this
  have htp : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), Pc.tp.getD j 0 ≤ Pc.rs j k * Pc.pp (πr j k) :=
    fun j k ↦ ((hrt j j.2).2 k (hkn k)).2.2.2.2.2
  have hrtl : ∀ j : Fin m, j < Pc.rt.length := fun j ↦ by rw [hPc.rtl]; exact j.2
  have hrtk : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), (k : ℕ) < (Pc.rt.getD j []).length :=
    fun j k ↦ by rw [(hrt j j.2).1]; exact hkn k
  have hsepk : ∀ (j : Fin m) (k l : Fin Sk.F.natDegree), k ≠ l → ∃ i < Pc.tp.getD j 0,
      ((Pc.map R.red).apx j k).getD i 0 ≠ ((Pc.map R.red).apx j l).getD i 0 := fun j k l hkl ↦ by
    have := PlaceCert.sepCheckP_spec (Pc.map R.red) sepp j (by rw [PlaceCert.map_fib_length]; exact j.2)
      k l (hkT k) (hkT l) (Fin.val_ne_of_ne hkl)
    simpa using this
  have hapxk : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), (Pc.map R.red).apx j k =
      conjC (R.red (Pc.rζ j k)) (Pc.rs j k) ((Pc.py (πr j k)).map R.red) := fun j k ↦
    Pc.map_apx R.red j k (hrtl j) (hrtk j k) (πr j k).2
  -- the roots over `𝕜`
  set rC : Fin m → Fin Sk.F.natDegree → LaurentSeries 𝕜 := fun j k ↦
    rot (ρ (ζO j k)) (hζk j k) (lsub (Pc.rs j k) (hsr j k)
      (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πr j k))))) with hrC
  have hsplitk : ∀ j : Fin m,
      Sk.F.map (branchSub (C := 𝕜) (K := 𝕜) (Pc.fN j) (ρ (αO j))) =
        ∏ k, (X - Polynomial.C (rC j k)) ∧ Function.Injective fun k ↦ rC j k := by
    intro j
    have hinj : Function.Injective fun k ↦ ofPowerSeries ℤ 𝕜
        (conjPS (ρ (ζO j k)) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j k)))) := by
      refine conj_inj psiP (tp := Pc.tp.getD j 0) _ (fun k ↦ (Pc.map R.red).apx j k)
        (fun k ↦ ?_) (hsepk j)
      rw [hζρ, hapxk]
      exact conj_approx psiP _ (hsr j k) _ _
        (approx_map_ρ R φ hR _ (oky _ (πr j k).2) _ (hdO (πr j k))) (htp j k)
    have e : ∀ k, rC j k = ofPowerSeries ℤ 𝕜
        (conjPS (ρ (ζO j k)) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j k)))) := fun k ↦
      (ofPS_conjPS _ (hζk j k) _ (hsr j k) _).symm
    simp only [e]
    refine ⟨split_of_roots Sk.F Sk.monic rfl _ _ _ (fun k ↦ ?_) hinj, hinj⟩
    refine conj_root Sk.F _ _ _ (hsr j k) (hNr j k) _ (hζk j k)
      (by rw [← map_pow, hζO, map_one]) _ _ ?_
    have := congrArg (PowerSeries.map ρ) (hrootO j k)
    rw [map_eval_psSubR, map_zero] at this
    exact this
  -- multiplicities
  set ΓP : Fin np → ℕ := fun π ↦ Pc.Γp.getD π 0 with hΓP
  have hdK : ∀ j : Fin m, ∑ k : Fin Sk.F.natDegree, Pc.rs j k * ΓP (πr j k) =
      Pc.fN j * Pc.dΓ.getD j 0 := fun j ↦ by
    rw [← (hPc.dΓ j j.2).1, hnS, ← hSkn]
    exact Fin.sum_univ_eq_sum_range (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) _
  have hsumΓ : ∑ j : Fin m, Pc.dΓ.getD j 0 = Pc.cΓ * Sk.F.natDegree := by
    rw [hSkn, ← hnS, ← hPc.sum]
    exact Fin.sum_univ_eq_sum_range (fun j ↦ Pc.dΓ.getD j 0) _
  have hplacesF : ∑ π : Fin np, ΓP π = Pc.cΓ * Sk.F.natDegree := by
    rw [hSkn, ← hnS, ← hPc.places]
    exact Fin.sum_univ_eq_sum_range (fun π ↦ Pc.Γp.getD π 0) _
  have hsurjF : ∀ π : Fin np, ∃ j k, πr j k = π := fun π ↦ by
    obtain ⟨j, hj, k, hk, h⟩ := hPc.surj π π.2
    exact ⟨⟨j, hj⟩, ⟨k, by rw [hSkn, ← hnS]; exact hk⟩, Fin.ext h⟩
  -- the fibres are distinct modulo `p`
  have hρα : ∀ j : Fin m, ρ (αO j) = psiP ((Pc.map R.red).αs.getD j 0) := fun j ↦ by
    rw [PlaceCert.αs_getD _ _ (by rw [PlaceCert.map_fib_length]; exact j.2),
      PlaceCert.map_fα _ _ _ j.2, residue_eq_psiP, zL_red R φ hR (hfαok _ j.2)]
  have hαinj : Function.Injective fun j : Fin m ↦ ρ (αO j) := fun j j' h ↦ by
    by_contra hne
    simp only [hρα] at h
    exact nodup_getD_ne hαnd'
      (by simp only [PlaceCert.αs, List.length_map, PlaceCert.map_fib_length]; exact j.2)
      (by simp only [PlaceCert.αs, List.length_map, PlaceCert.map_fib_length]; exact j'.2)
      (Fin.val_ne_of_ne hne) 0 (psiP.injective h)
  -- **finiteness of `Pic⁰` modulo `p`**
  haveI : Finite 𝕜 := Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  haveI : Fintype 𝕜 := Fintype.ofFinite 𝕜
  obtain ⟨mm, hmm, htestk⟩ := Sk.exists_principal_test_places (K := AlgebraicClosure 𝕜) hBrk hBIk
    hBk' (fun j ↦ ρ (αO j)) hαinj (fun j ↦ Pc.fN j) hNpos pjF (fun π ↦ Pc.pe π)
    (fun π ↦ ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO π))) πr hπr hsurjF (fun j k ↦ Pc.rs j k) hsr
    hNr (fun j k ↦ ρ (ζO j k)) hζk (fun j k ↦ by rw [← map_pow, hζO, map_one]) rC (fun j k ↦ rfl)
    (fun j ↦ (hsplitk j).1) (fun j ↦ (lmap_injective _).comp (hsplitk j).2) ΓP Pc.cΓ hplacesF
    (fun j ↦ Pc.dΓ.getD j 0) hdK hsumΓ
  refine ⟨mm, hmm, fun Pc' hfib hrt' hΓp hcΓ hpll hpl' hPc' hpre2 hside ↦ ?_⟩
  -- the refinement has the same fibres, roots and multiplicities
  have hfα' : ∀ j, Pc'.fα j = Pc.fα j := fun j ↦ by simp only [PlaceCert.fα, hfib]
  have hfN' : ∀ j, Pc'.fN j = Pc.fN j := fun j ↦ by simp only [PlaceCert.fN, hfib]
  have hrs' : ∀ j k, Pc'.rs j k = Pc.rs j k := fun j k ↦ by simp only [PlaceCert.rs, hrt']
  have hrπ' : ∀ j k, Pc'.rπ j k = Pc.rπ j k := fun j k ↦ by simp only [PlaceCert.rπ, hrt']
  have hrζ' : ∀ j k, Pc'.rζ j k = Pc.rζ j k := fun j k ↦ by simp only [PlaceCert.rζ, hrt']
  have hαs : (Pc'.map R.red).αs = (Pc.map R.red).αs := by
    simp only [PlaceCert.αs, PlaceCert.map, hfib]
  have hbL : (Pc'.map R.red).bL Sk.F.natDegree mm = (Pc.map R.red).bL Sk.F.natDegree mm := by
    simp only [PlaceCert.bL, PlaceCert.rs, PlaceCert.rπ, PlaceCert.map, hfib, hrt', hΓp]
  have hpre2' := hpre2
  simp only [PlaceCert.primePre, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hpre2'
  obtain ⟨⟨⟨⟨⟨⟨-, oky2⟩, -⟩, -⟩, -⟩, hunit2⟩, -⟩ := hpre2'
  -- the integral roots of the refinement are those of `Pc`
  have hdO' : ∀ π : Fin np, (PowerSeries.X : PowerSeries ℤ_[p]) ^ Pc'.pp π ∣
      ρO π - ((toPoly (liftL R φ hR (Pc'.py π)) : ℤ_[p][X]) : PowerSeries ℤ_[p]) := by
    intro π
    obtain ⟨hpj, hpe, hpp, hpy⟩ := hpl' π π.2
    have hπ' : (π : ℕ) < Pc'.pl.length := by rw [hpll]; exact π.2
    have hok' : R.ok (Pc'.fα (Pc'.pj π)) = true := by
      rw [hpj, hfα']; exact hfαok _ (hPc.pl π π.2).1
    obtain ⟨ρ2, hρ2, hd2⟩ := rep_root_Zp R φ hR T.Fc hokF _ hok' (oky2 π hπ') (hPc'.pl π hπ').2.2
      (by simpa using hunit2 π hπ')
    rw [hpj, hpe, hfα'] at hρ2
    rw [zp_root_eq R φ hR T.Fc hokF _ (hfαok _ (hPc.pl π π.2).1) (oky π π.2) (hPc.pl π π.2).2.2
      (ρO π) ρ2 (hρO π) hρ2 (hdO π) hpp (oky2 π hπ') hpy hd2]
    exact hd2
  have hrtl2 : ∀ j : Fin m, j < Pc'.rt.length := fun j ↦ by rw [hrt']; exact hrtl j
  have hrtk2 : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), (k : ℕ) < (Pc'.rt.getD j []).length :=
    fun j k ↦ by rw [hrt']; exact hrtk j k
  have hapxk' : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), (Pc'.map R.red).apx j k =
      conjC (R.red (Pc.rζ j k)) (Pc.rs j k) ((Pc'.py (πr j k)).map R.red) := fun j k ↦ by
    rw [PlaceCert.map_apx Pc' R.red j k (hrtl2 j) (hrtk2 j k) (by rw [hrπ', hpll]; exact (πr j k).2),
      hrζ', hrs', hrπ']
  have htp' : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), Pc'.tp.getD j 0 ≤ Pc.rs j k * Pc'.pp (πr j k) :=
    fun j k ↦ by
      have := ((hPc'.rt j (by rw [hfib]; exact j.2)).2 k (hkn k)).2.2.2.2.2
      rwa [hrs', hrπ'] at this
  -- the test in the form of the kernel search
  have hfc : ∀ j : Fin m, ((Pc'.map R.red).fcerts Sk.F.natDegree).getD j ⟨1, [], 0⟩ =
      ⟨Pc.fN j, (List.range Sk.F.natDegree).map ((Pc'.map R.red).apx j), Pc'.tp.getD j 0⟩ := by
    intro j
    rw [PlaceCert.fcerts_getD _ _ _ (by rw [PlaceCert.map_fib_length, hfib]; exact j.2),
      PlaceCert.map_fN _ _ _ (by rw [hfib]; exact j.2), hfN']
    rfl
  set Y' : Fin m → Fin Sk.F.natDegree → PowerSeries 𝕜 := fun j k ↦
    conjPS (ρ (ζO j k)) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j k))) with hY'
  have hY : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), (PowerSeries.X : PowerSeries 𝕜) ^
      (((Pc'.map R.red).fcerts Sk.F.natDegree).getD j ⟨1, [], 0⟩).prec ∣
        Y' j k - thetaT psiP (toPoly (((((Pc'.map R.red).fcerts Sk.F.natDegree).getD j
          ⟨1, [], 0⟩).ys).getD k [])) := fun j k ↦ by
    rw [hfc]
    show (PowerSeries.X : PowerSeries 𝕜) ^ Pc'.tp.getD j 0 ∣ Y' j k - thetaT psiP
      (toPoly (((List.range Sk.F.natDegree).map ((Pc'.map R.red).apx j)).getD k []))
    have e2 : ((List.range Sk.F.natDegree).map ((Pc'.map R.red).apx j)).getD k [] =
        (Pc'.map R.red).apx j k := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    rw [e2, hapxk' j k, hY']
    beta_reduce
    rw [hζρ]
    exact conj_approx psiP _ (hsr j _) _ _
      (approx_map_ρ R φ hR _ (oky2 _ (by rw [hpll]; exact (πr j k).2)) _ (hdO' (πr j k))) (htp' j _)
  have htest0 := princTest_congr
    (δ' := fun i : Fin Sk.F.natDegree ↦ T.I.δL.getD i 0)
    (e' := fun q : Fin m × Fin Sk.F.natDegree ↦
      (((Pc'.map R.red).fcerts Sk.F.natDegree).getD q.1 ⟨1, [], 0⟩).N)
    (a' := fun q ↦ psiP ((Pc'.map R.red).αs.getD q.1 0))
    (σ' := fun q i ↦ basisSer (fun i : Fin Sk.F.natDegree ↦
        (toB ((T.I.Bc.map (redBL R)).getD i [])).map (mapRingHom psiP))
      ((toPoly (T.I.Dc.map R.red)).map psiP)
      (((Pc'.map R.red).fcerts Sk.F.natDegree).getD q.1 ⟨1, [], 0⟩).N
      (psiP ((Pc'.map R.red).αs.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ 𝕜 (Y' q.1 q.2)) i)
    (b' := fun q ↦ (((Pc'.map R.red).bL Sk.F.natDegree mm).getD q.1 []).getD q.2 0)
    (fun i ↦ rfl) (fun q ↦ by simp only [hfc]) (fun q ↦ by rw [hαs]; exact hρα q.1)
    (fun q i ↦ ?_) (fun q ↦ ?_) htestk
  rotate_left
  · have hB' : (fun j : Fin Sk.F.natDegree ↦ (B j).map (mapRingHom ρ)) =
        fun i : Fin Sk.F.natDegree ↦ (toB ((T.I.Bc.map (redBL R)).getD i [])).map (mapRingHom psiP) := funext fun j ↦ hBρ j
    simp only [hfc]
    rw [hαs, ← hρα, hB', hDρ, hY']
    beta_reduce
    rw [ofPS_conjPS (ρ (ζO q.1 q.2)) (hζk q.1 _) (Pc.rs q.1 q.2) (hsr q.1 q.2)]
  · show _ = (((Pc'.map R.red).bL Sk.F.natDegree mm).getD q.1 []).getD q.2 0
    rw [hbL, PlaceCert.bL_getD _ _ _ _ _ (by rw [PlaceCert.map_fib_length]; exact q.1.2) q.2.2,
      PlaceCert.map_rs _ _ _ _ (hrtl q.1) (hrtk q.1 q.2),
      PlaceCert.map_rπ _ _ _ _ (hrtl q.1) (hrtk q.1 q.2)]
    rfl
  rw [← hSkn] at hside ⊢
  exact placeWit_isSome psiP hside (by rw [PlaceCert.map_fib_length, hfib]) Y' hY
    (by rw [PlaceCert.map_cΓ, hcΓ]; exact htest0)

end Step

end Curves
