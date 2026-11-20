import RischTragerBronstein.Torsion.RamDOrder

/-!
# The prime step for divisors at places, from certificates

`hstep_places_of_prime`: a curve over `K` with `globalCheck`, a prime `p` with `primeCheck`, and a
place certificate with its checks satisfy the conclusion of `prime_step_places` (over `O = ℤ_p`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section Aux

lemma princTest_congr {C : Type*} [Field C] {n : ℕ} {δ δ' : Fin n → ℕ} {M : ℕ} {Q : Type*}
    {e e' : Q → ℕ} {a a' : Q → C} {σ σ' : Q → Fin n → LaurentSeries C} {b b' : Q → ℕ}
    (hδ : ∀ i, δ i = δ' i) (he : ∀ q, e q = e' q) (ha : ∀ q, a q = a' q)
    (hσ : ∀ q i, σ q i = σ' q i) (hb : ∀ q, b q = b' q) :
    princTest δ M e a σ b → princTest δ' M e' a' σ' b' := by
  obtain rfl : δ = δ' := funext hδ
  obtain rfl : e = e' := funext he
  obtain rfl : a = a' := funext ha
  obtain rfl : σ = σ' := funext fun q ↦ funext (hσ q)
  obtain rfl : b = b' := funext hb
  exact id

namespace PlaceCert

variable {F : Type*} [Field F] [DecidableEq F] (D : PlaceCert F)

lemma map_apx {F' : Type*} [Field F'] [DecidableEq F'] (f : F → F') (j k : ℕ) (hj : j < D.rt.length)
    (hk : k < (D.rt.getD j []).length) (hπ : D.rπ j k < D.pl.length) :
    (D.map f).apx j k = conjC (f (D.rζ j k)) (D.rs j k) ((D.py (D.rπ j k)).map f) := by
  rw [apx, map_rζ D f j k hj hk, map_rs D f j k hj hk, map_rπ D f j k hj hk, map_py D f _ hπ]

end PlaceCert

end Aux

section PFacts

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- The content of `PlaceCert.primeCheck`. -/
structure PlaceCert.PFacts (Fc : BPoly K) (n : ℕ) (δL : List ℕ) (Bc : List (BPoly K)) (Dc : CPoly K)
    (xs : List (ZMod p)) (D : PlaceCert K) (Q : PlaceCert.PrimeData p) : Prop where
  okα : ∀ c ∈ D.αs, R.ok c = true
  oky : ∀ π < D.pl.length, ∀ c ∈ D.py π, R.ok c = true
  okζ : ∀ j < D.fib.length, ∀ k < n, R.ok (D.rζ j k) = true
  nd : (D.map R.red).αs.Nodup
  pt : ∀ j < D.fib.length,
    (compC (Dc.map R.red) (shiftC (R.red (D.fα j)) 1)).getD (muD Dc (D.fα j) 1) 0 ≠ 0 ∧
    ∀ i < xs.length, R.red (D.fα j) ≠ xs.getD i 0
  unit : ∀ π < D.pl.length,
    (bivEval (derivYB (redBL R Fc)) (shiftC (R.red (D.fα (D.pj π))) (D.pe π))
      ((D.py π).map R.red)).getD
        (ordC (bivEval (derivYB Fc) (shiftC (D.fα (D.pj π)) (D.pe π)) (D.py π))) 0 ≠ 0
  sep : (D.map R.red).sepCheckP n = true
  mp : 1 ≤ Q.mp
  wit : princWitCheckN n (Q.mp * D.cΓ) δL (Bc.map (redBL R)) (Dc.map R.red) (D.map R.red).αs
    ((D.map R.red).fcerts n) ((D.map R.red).bL n Q.mp) Q.Gw = true

lemma PlaceCert.primeCheck_spec {Fc : BPoly K} {n : ℕ} {δL : List ℕ} {Bc : List (BPoly K)}
    {Dc : CPoly K} {xs : List (ZMod p)} {D : PlaceCert K} {Q : PlaceCert.PrimeData p}
    (h : D.primeCheck R Fc n δL Bc Dc xs Q = true) : D.PFacts R Fc n δL Bc Dc xs Q := by
  simp only [PlaceCert.primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end PFacts

section Step

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

local notation "𝕜" => IsLocalRing.ResidueField ℤ_[p]
local notation "ρ" => IsLocalRing.residue ℤ_[p]
local notation "ι" => algebraMap ℤ_[p] ℚ_[p]

include hR in
lemma approx_map_ι (y : CPoly K) (hoky : ∀ c ∈ y, R.ok c = true) (ρO : PowerSeries ℤ_[p]) {P : ℕ}
    (h : (PowerSeries.X : PowerSeries ℤ_[p]) ^ P ∣
      ρO - ((toPoly (liftL R φ hR y) : ℤ_[p][X]) : PowerSeries ℤ_[p])) :
    (PowerSeries.X : PowerSeries ℚ_[p]) ^ P ∣ PowerSeries.map ι ρO - thetaT φ (toPoly y) := by
  have := map_dvd (PowerSeries.map ι) h
  rwa [map_pow, PowerSeries.map_X, map_sub, map_coe_poly, toPoly_liftL_map R φ hR _ hoky,
    ← thetaT_apply] at this

lemma map_residue_PS (z : PowerSeries ℤ_[p]) :
    PowerSeries.map ρ z = PowerSeries.map psiP (PowerSeries.map PadicInt.toZMod z) := by
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, residue_eq_psiP]

include hR in
lemma approx_map_ρ (y : CPoly K) (hoky : ∀ c ∈ y, R.ok c = true) (ρO : PowerSeries ℤ_[p]) {P : ℕ}
    (h : (PowerSeries.X : PowerSeries ℤ_[p]) ^ P ∣
      ρO - ((toPoly (liftL R φ hR y) : ℤ_[p][X]) : PowerSeries ℤ_[p])) :
    (PowerSeries.X : PowerSeries 𝕜) ^ P ∣
      PowerSeries.map ρ ρO - thetaT psiP (toPoly (y.map R.red)) := by
  have e : thetaT psiP (toPoly (y.map R.red)) =
      PowerSeries.map ρ ((toPoly (liftL R φ hR y) : ℤ_[p][X]) : PowerSeries ℤ_[p]) := by
    rw [thetaT_apply, ← toPoly_liftL_red R φ hR _ hoky, Polynomial.map_map, map_coe_poly]
    congr 2
    exact RingHom.ext fun z ↦ (residue_eq_psiP z).symm
  have := map_dvd (PowerSeries.map ρ) h
  rw [map_pow, PowerSeries.map_X, map_sub] at this
  rw [e]; exact this

set_option maxHeartbeats 16000000 in
include φ hR in
/-- **The prime step for divisors at places, from certificates.** -/
theorem hstep_places_of_prime {L Kb : Type*} [Field L] [Algebra K L] [Field Kb] [Algebra K Kb]
    [IsAlgClosed Kb] (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P)
    (Pc : PlaceCert K) (hPc : Pc.Facts T.Fc S.F.natDegree) (Q : PlaceCert.PrimeData p)
    (hQ : Pc.primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc P.xs Q = true) :
    ∀ M : ℕ, 0 < M →
      princTest (fun i : Fin S.F.natDegree ↦ T.I.δL.getD i 0) (M * Pc.cΓ)
        (fun q : Fin Pc.fib.length × Fin S.F.natDegree ↦ Pc.fN q.1) (fun q ↦ Pc.fα q.1)
        (fun q i ↦ basisSer (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc) (Pc.fN q.1)
          (Pc.fα q.1) (rCK T.Fc Pc q.1 q.2) i)
        (fun q ↦ M * (Pc.rs q.1 q.2 * Pc.Γp.getD (Pc.rπ q.1 q.2) 0)) →
      ∃ v : ℕ, princTest (fun i : Fin S.F.natDegree ↦ T.I.δL.getD i 0) ((Q.mp * p ^ v) * Pc.cΓ)
        (fun q : Fin Pc.fib.length × Fin S.F.natDegree ↦ Pc.fN q.1) (fun q ↦ Pc.fα q.1)
        (fun q i ↦ basisSer (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc) (Pc.fN q.1)
          (Pc.fα q.1) (rCK T.Fc Pc q.1 q.2) i)
        (fun q ↦ (Q.mp * p ^ v) * (Pc.rs q.1 q.2 * Pc.Γp.getD (Pc.rπ q.1 q.2) 0)) := by
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
    rw [← natDegree_map_eq_of_injective (f := mapRingHom ι) (Polynomial.map_injective _ hιi), hFι, hmon.natDegree_map,
      hdeg]
  have hFk : FO.map (mapRingHom ρ) = (toB Fp).map (mapRingHom psiP) := by
    rw [mapRingHom_residue, ← Polynomial.map_map, hFz]
  -- the curve over `ℚ_p`
  have hSKm : (FO.map (mapRingHom ι)).Monic := hFm.map _
  have hSKd : 0 < (FO.map (mapRingHom ι)).natDegree := by rw [hFm.natDegree_map, hFdeg]; exact hn0
  obtain ⟨hSKi, hSki, -⟩ := irr_all R φ hR T hT P hP
  set SK := stdCurve (FO.map (mapRingHom ι)) hSKm hSKd hSKi with hSK
  have hSKn : SK.F.natDegree = T.n := by
    show (FO.map (mapRingHom ι)).natDegree = T.n
    rw [hFm.natDegree_map, hFdeg]
  -- the curve over `𝕜`
  have hSkm : (FO.map (mapRingHom ρ)).Monic := hFm.map _
  have hSkd : 0 < (FO.map (mapRingHom ρ)).natDegree := by rw [hFm.natDegree_map, hFdeg]; exact hn0
  set Sk := stdCurve (FO.map (mapRingHom ρ)) hSkm hSkd hSki with hSk
  have hSkn : Sk.F.natDegree = T.n := by
    show (FO.map (mapRingHom ρ)).natDegree = T.n
    rw [hFm.natDegree_map, hFdeg]
  have hSkF : Sk.F = (toB Fp).map (mapRingHom psiP) := hFk
  -- the cover polynomial modulo `p`
  have hGp : toPoly (T.G.map R.red) = resultant (toB Fp) (derivative (toB Fp)) T.n (T.n - 1) *
      toPoly (T.I.Dc.map R.red) *
      (Matrix.of fun (i j : Fin T.n) ↦ (toB ((T.I.Bc.map (redBL R)).getD j [])).coeff i).det :=
    cover_red R φ hR T.Fc T.n T.I.Dc T.I.Bc T.G hT.G_eq hokF hP.okD
      (fun W hW ↦ okB_spec R (hP.okBc W hW)) hP.okG
  -- branch systems
  have hBrK : SK.HasBranches (AlgebraicClosure ℚ_[p]) := SK.hasBranches
  have hBIK : SK.HasBranchesInf (AlgebraicClosure ℚ_[p]) := SK.hasBranchesInf
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
  -- the integral basis over `ℤ_p`
  have hokB : ∀ j, ∀ P' ∈ T.I.Bc.getD j [], ∀ c ∈ P', R.ok c = true := fun j P' hP' c hc ↦ by
    by_cases hj : j < T.I.Bc.length
    · rw [List.getD_eq_getElem _ _ hj] at hP'
      exact okB_spec R (hP.okBc _ (List.getElem_mem hj)) P' hP' c hc
    · rw [List.getD_eq_default _ _ (by omega)] at hP'; simp at hP'
  have hredB : ∀ j, (T.I.Bc.map (redBL R)).getD j [] = redBL R (T.I.Bc.getD j []) := fun j ↦ by
    cases h : T.I.Bc[j]? <;> simp [List.getD_eq_getElem?_getD, h, redBL]
  set B : ℕ → ℤ_[p][X][X] := fun j ↦ toB (liftBL R φ hR (T.I.Bc.getD j [])) with hB
  set D : ℤ_[p][X] := toPoly (liftL R φ hR T.I.Dc) with hD
  have hBι : ∀ j, (B j).map (mapRingHom ι) = (toB (T.I.Bc.getD j [])).map (mapRingHom φ) :=
    fun j ↦ toB_liftBL_map R φ hR _ (hokB j)
  have hBρ : ∀ j, (B j).map (mapRingHom ρ) =
      (toB ((T.I.Bc.map (redBL R)).getD j [])).map (mapRingHom psiP) := fun j ↦ by
    rw [mapRingHom_residue, ← Polynomial.map_map, toB_liftBL_red R φ hR _ (hokB j), hredB]
    rfl
  have hDι : D.map ι = (toPoly T.I.Dc).map φ := toPoly_liftL_map R φ hR _ hP.okD
  have hDρ : D.map ρ = (toPoly (T.I.Dc.map R.red)).map psiP := by
    rw [← coe_mapRingHom, mapRingHom_residue, RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom,
      toPoly_liftL_red R φ hR _ hP.okD]
  have hDm : D.Monic := Polynomial.monic_of_injective hιi
    (by rw [hDι]; exact (toPoly_monic_of_getLast T.I.Dc hT.Dlast).map φ)
  have hnorm := hT.norm
  simp only [normCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hnorm
  obtain ⟨⟨hB0c, hδ0c⟩, hδc⟩ := hnorm
  -- the integral bases over `ℚ_p` and `𝕜`
  have hBK : SK.IsIntBasis (AlgebraicClosure ℚ_[p]) (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι)
      (fun j ↦ T.I.δL.getD j 0) := by
    simp only [hBι, hDι]
    exact ibCheckR_spec SK T.Fc φ hFι T.n T.k hSKn.symm T.I T.G hT.ib (dvd_of_eq hT.G_eq.symm)
  have hBk : Sk.IsIntBasis (AlgebraicClosure 𝕜)
      (fun j ↦ (toB ((T.I.Bc.map (redBL R)).getD j [])).map (mapRingHom psiP))
      ((toPoly (T.I.Dc.map R.red)).map psiP) (fun j ↦ T.I.δL.getD j 0) :=
    ibCheck_spec Sk Fp psiP hSkF T.n T.k hSkn.symm (P.Ip R T) (T.G.map R.red) hP.ib (dvd_of_eq hGp.symm)
  have hBk' : Sk.IsIntBasis (AlgebraicClosure 𝕜) (fun j ↦ (B j).map (mapRingHom ρ)) (D.map ρ)
      (fun j ↦ T.I.δL.getD j 0) := by
    simp only [hBρ, hDρ]; exact hBk
  -- the base points
  set g := P.xs.length with hg_def
  set x : Fin g → ℤ_[p] := fun i ↦ liftZ (P.xs.getD i 0) with hx_def
  have hxz : ∀ i, PadicInt.toZMod (x i) = P.xs.getD i 0 := fun i ↦ toZMod_liftZ _
  have hx : ∀ i j, i ≠ j → IsUnit (x i - x j) := fun i j hij ↦ Jac.isUnit_of_toZMod (by
    rw [map_sub, hxz, hxz]
    exact sub_ne_zero.mpr (nodup_getD_ne hP.xnd i.2 j.2 (Fin.val_ne_of_ne hij) 0))
  have hbase := hP.base
  have hy : ∀ i : Fin g, ∃ y : Fin SK.F.natDegree → ℤ_[p],
      (∀ k, PadicInt.toZMod (y k) = (P.ys.getD i []).getD k 0) ∧
        FO.map (evalRingHom (x i)) = ∏ k, (X - Polynomial.C (y k)) := by
    intro i
    obtain ⟨hlen, hnd, -, hroots⟩ := hbase i i.2
    refine split_Zp _ (hFm.map _) (by rw [hFm.natDegree_map, hFdeg, hSKn])
      (fun k ↦ (P.ys.getD i []).getD k 0) (fun k k' h ↦ ?_) (fun k ↦ ?_) (fun k ↦ ?_)
    · by_contra hne
      exact nodup_getD_ne hnd (by rw [hlen, ← hSKn]; exact k.2) (by rw [hlen, ← hSKn]; exact k'.2)
        (Fin.val_ne_of_ne hne) 0 h
    · rw [fibre_toZMod, hFz, hxz]
      show evalW (toB Fp) _ _ = 0
      rw [← evalB_eq]
      exact (hroots k (by rw [← hSKn]; exact k.2)).1
    · rw [Polynomial.derivative_map, fibre_toZMod, ← Polynomial.derivative_map, hFz, hxz]
      show evalW (derivative (toB Fp)) _ _ ≠ 0
      rw [← toB_derivYB, ← evalB_eq]
      exact (hroots k (by rw [← hSKn]; exact k.2)).2
  choose y hyz hys using hy
  have hFu : ∀ i k, IsUnit (evalW (derivative FO) (x i) (y i k)) := fun i k ↦
    Jac.isUnit_of_toZMod (by
      rw [hFO, toZMod_evalW_deriv_lift R φ hR _ hokF, hxz, hyz]
      exact ((hbase i i.2).2.2.2 k (by rw [← hSKn]; exact k.2)).2)
  have hdet : ∀ i, IsUnit (Matrix.det (Matrix.of fun kk (j : Fin SK.F.natDegree) ↦
      evalW (B j) (x i) (y i kk))) := fun i ↦ Jac.isUnit_of_toZMod (by
    rw [RingHom.map_det]
    have e : (PadicInt.toZMod).mapMatrix (Matrix.of fun kk (j : Fin SK.F.natDegree) ↦
        evalW (B j) (x i) (y i kk)) = Matrix.of fun kk j : Fin SK.F.natDegree ↦
          detMat (T.I.Bc.map (redBL R)) P.xs P.ys i kk j := by
      ext kk j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, hB]
      dsimp only
      rw [toZMod_evalW_lift R φ hR _ (hokB j), hxz, hyz, detMat, hredB]
    rw [e]
    exact detCheck_spec (n := SK.F.natDegree) (by rw [hSKn]; exact hP.det) i i.2)
  have hDx : ∀ i, IsUnit (D.eval (x i)) := fun i ↦ Jac.isUnit_of_toZMod (by
    rw [hD, toZMod_eval_liftL R φ hR _ hP.okD, hxz]; exact (hbase i i.2).2.2.1)
  have hNS : ∀ q : Fin SK.F.natDegree → 𝕜[X], (∀ j, q j ≠ 0 → (q j).natDegree + T.I.δL.getD j 0 ≤ g) →
      (∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 →
        evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i k)) = 0) →
      ∀ i, evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i))
        (ρ (y i ⟨0, by rw [hSKn]; exact hn0⟩)) = 0 := by
    intro q hq hv i
    have e1 : ∀ i : Fin g, ρ (x i) = psiP (P.xs.getD i 0) := fun i ↦ by rw [residue_eq_psiP, hxz]
    have e2 : ∀ i k, ρ (y i k) = psiP ((P.ys.getD i []).getD k 0) := fun i k ↦ by
      rw [residue_eq_psiP, hyz]
    have e3 : (fun j : Fin SK.F.natDegree ↦ (B j).map (mapRingHom ρ)) =
        fun j : Fin SK.F.natDegree ↦ (toB ((T.I.Bc.map (redBL R)).getD j [])).map (mapRingHom psiP) :=
      funext fun j ↦ hBρ j
    rw [e3] at hv ⊢
    simp only [e1, e2] at hv ⊢
    exact nsCheck_spec psiP (n := SK.F.natDegree) (by rw [hSKn]; exact hP.ns) q hq
      (fun i k hk ↦ hv i k hk) i
  -- the base field
  have hSKφ : SK.F = S.F.map (mapRingHom φ) := by rw [hSF]; exact hFι
  have hnK : SK.F.natDegree = S.F.natDegree := by rw [hSKn, hnS]
  have hBS : S.IsIntBasis Kb (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
      (fun j ↦ T.I.δL.getD j 0) := by
    have := ibCheckR_spec (K := Kb) S T.Fc (RingHom.id K)
      (by rw [hSF, Polynomial.mapRingHom_id, Polynomial.map_id]) T.n T.k hnS.symm T.I T.G hT.ib
      (dvd_of_eq hT.G_eq.symm)
    simpa only [Polynomial.mapRingHom_id, Polynomial.map_id] using this

  -- the places
  obtain ⟨okα, oky, okζ, hαnd', hαp, hunit, sepp, hmp, hwit⟩ := PlaceCert.primeCheck_spec R hQ
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
    rep_root_Zp R φ hR T.Fc hokF _ (hfαok _ (hPc.pl π π.2).1) (oky π π.2) (hPc.pl π π.2).2.2
      (hunit π π.2)
  choose ρO hρO hdO using hρ
  have hrt := hPc.rt
  have hkn : ∀ k : Fin SK.F.natDegree, (k : ℕ) < S.F.natDegree := fun k ↦ by rw [← hnK]; exact k.2
  have hkT : ∀ k : Fin SK.F.natDegree, (k : ℕ) < T.n := fun k ↦ by rw [← hnS]; exact hkn k
  set πr : Fin m → Fin SK.F.natDegree → Fin np := fun j k ↦
    ⟨Pc.rπ j k, ((hrt j j.2).2 k (hkn k)).1⟩ with hπrdef
  have hπr : ∀ j k, pjF (πr j k) = j := fun j k ↦ Fin.ext ((hrt j j.2).2 k (hkn k)).2.1
  have hsr : ∀ (j : Fin m) (k : Fin SK.F.natDegree), 0 < Pc.rs j k := fun j k ↦
    ((hrt j j.2).2 k (hkn k)).2.2.1
  have hNr : ∀ (j : Fin m) (k : Fin SK.F.natDegree), Pc.fN j = Pc.rs j k * Pc.pe (πr j k) := fun j k ↦
    ((hrt j j.2).2 k (hkn k)).2.2.2.1
  have hNpos : ∀ j : Fin m, 0 < Pc.fN j := fun j ↦ by
    obtain ⟨hπ, -, hs, hN, -⟩ := (hrt j j.2).2 0 hn0S
    rw [hN]; exact Nat.mul_pos hs (hPc.pl _ hπ).2.1
  set ζO : Fin m → Fin SK.F.natDegree → ℤ_[p] := fun j k ↦ zL R φ hR (Pc.rζ j k) with hζOdef
  have hζok : ∀ (j : Fin m) (k : Fin SK.F.natDegree), R.ok (Pc.rζ j k) = true := fun j k ↦
    okζ j j.2 k (hkT k)
  have hζι : ∀ (j : Fin m) (k : Fin SK.F.natDegree), ι (ζO j k) = φ (Pc.rζ j k) := fun j k ↦ zL_map R φ hR (hζok j k)
  have hζρ : ∀ (j : Fin m) (k : Fin SK.F.natDegree), ρ (ζO j k) = psiP (R.red (Pc.rζ j k)) := fun j k ↦ by
    rw [residue_eq_psiP, zL_red R φ hR (hζok j k)]
  have hζO : ∀ (j : Fin m) (k : Fin SK.F.natDegree), ζO j k ^ Pc.fN j = 1 := fun j k ↦ hιi (by
    rw [map_pow, map_one, hζι, ← map_pow, ((hrt j j.2).2 k (hkn k)).2.2.2.2.1, map_one])
  have hζK : ∀ (j : Fin m) (k : Fin SK.F.natDegree), ι (ζO j k) ≠ 0 := fun j k ↦
    ne_zero_of_pow_eq_one (hNpos j) (by rw [← map_pow, hζO, map_one])
  have hζk : ∀ (j : Fin m) (k : Fin SK.F.natDegree), ρ (ζO j k) ≠ 0 := fun j k ↦
    ne_zero_of_pow_eq_one (hNpos j) (by rw [← map_pow, hζO, map_one])
  have hrootO : ∀ (j : Fin m) (k : Fin SK.F.natDegree),
      (FO.map (psSubR (Pc.pe (πr j k)) (αO j))).eval (ρO (πr j k)) = 0 := fun j k ↦ by
    have := hρO (πr j k)
    rwa [hπr] at this
  have htp : ∀ (j : Fin m) (k : Fin SK.F.natDegree), Pc.tp.getD j 0 ≤ Pc.rs j k * Pc.pp (πr j k) :=
    fun j k ↦ ((hrt j j.2).2 k (hkn k)).2.2.2.2.2
  have hsepK : ∀ (j : Fin m) (k l : Fin SK.F.natDegree), k ≠ l →
      ∃ i < Pc.tp.getD j 0, (Pc.apx j k).getD i 0 ≠ (Pc.apx j l).getD i 0 := fun j k l hkl ↦
    PlaceCert.sepCheckP_spec Pc hPc.sep j j.2 k l (hkn k) (hkn l) (Fin.val_ne_of_ne hkl)
  have hrtl : ∀ j : Fin m, j < Pc.rt.length := fun j ↦ by rw [hPc.rtl]; exact j.2
  have hrtk : ∀ (j : Fin m) (k : Fin SK.F.natDegree), (k : ℕ) < (Pc.rt.getD j []).length := fun j k ↦ by
    rw [(hrt j j.2).1]; exact hkn k
  have hsepk : ∀ (j : Fin m) (k l : Fin SK.F.natDegree), k ≠ l → ∃ i < Pc.tp.getD j 0,
      ((Pc.map R.red).apx j k).getD i 0 ≠ ((Pc.map R.red).apx j l).getD i 0 := fun j k l hkl ↦ by
    have := PlaceCert.sepCheckP_spec (Pc.map R.red) sepp j (by rw [PlaceCert.map_fib_length]; exact j.2) k l (hkT k) (hkT l)
      (Fin.val_ne_of_ne hkl)
    simpa using this
  have hapxk : ∀ (j : Fin m) (k : Fin SK.F.natDegree), (Pc.map R.red).apx j k =
      conjC (R.red (Pc.rζ j k)) (Pc.rs j k) ((Pc.py (πr j k)).map R.red) := fun j k ↦
    Pc.map_apx R.red j k (hrtl j) (hrtk j k) (πr j k).2
  -- the splittings over `ℚ_p` and `𝕜`
  have hsplitK : ∀ j : Fin m,
      SK.F.map (branchSub (C := ℚ_[p]) (K := ℚ_[p]) (Pc.fN j) (ι (αO j))) =
        ∏ k, (X - Polynomial.C (ofPowerSeries ℤ ℚ_[p]
          (conjPS (ι (ζO j k)) (Pc.rs j k) (PowerSeries.map ι (ρO (πr j k)))))) ∧
      Function.Injective fun k ↦ ofPowerSeries ℤ ℚ_[p]
          (conjPS (ι (ζO j k)) (Pc.rs j k) (PowerSeries.map ι (ρO (πr j k)))) := by
    intro j
    have hinj : Function.Injective fun k ↦ ofPowerSeries ℤ ℚ_[p]
        (conjPS (ι (ζO j k)) (Pc.rs j k) (PowerSeries.map ι (ρO (πr j k)))) := by
      refine conj_inj φ (tp := Pc.tp.getD j 0) _ (fun k ↦ Pc.apx j k) (fun k ↦ ?_) (hsepK j)
      rw [hζι]
      exact conj_approx φ _ (hsr j k) _ _
        (approx_map_ι R φ hR _ (oky _ (πr j k).2) _ (hdO (πr j k))) (htp j k)
    refine ⟨split_of_roots SK.F SK.monic rfl _ _ _ (fun k ↦ ?_) hinj, hinj⟩
    refine conj_root SK.F _ _ _ (hsr j k) (hNr j k) _ (hζK j k)
      (by rw [← map_pow, hζO, map_one]) _ _ ?_
    have := congrArg (PowerSeries.map ι) (hrootO j k)
    rw [map_eval_psSubR, map_zero] at this
    exact this
  have hsplitk : ∀ j : Fin m,
      Sk.F.map (branchSub (C := 𝕜) (K := 𝕜) (Pc.fN j) (ρ (αO j))) =
        ∏ k, (X - Polynomial.C (ofPowerSeries ℤ 𝕜
          (conjPS (ρ (ζO j k)) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j k)))))) ∧
      Function.Injective fun k ↦ ofPowerSeries ℤ 𝕜
          (conjPS (ρ (ζO j k)) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j k)))) := by
    intro j
    have hinj : Function.Injective fun k ↦ ofPowerSeries ℤ 𝕜
        (conjPS (ρ (ζO j k)) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j k)))) := by
      refine conj_inj psiP (tp := Pc.tp.getD j 0) _ (fun k ↦ (Pc.map R.red).apx j k)
        (fun k ↦ ?_) (hsepk j)
      rw [hζρ, hapxk]
      exact conj_approx psiP _ (hsr j k) _ _
        (approx_map_ρ R φ hR _ (oky _ (πr j k).2) _ (hdO (πr j k))) (htp j k)
    refine ⟨split_of_roots Sk.F Sk.monic (by rw [hSkn, ← hSKn]) _ _ _ (fun k ↦ ?_) hinj, hinj⟩
    refine conj_root Sk.F _ _ _ (hsr j k) (hNr j k) _ (hζk j k)
      (by rw [← map_pow, hζO, map_one]) _ _ ?_
    have := congrArg (PowerSeries.map ρ) (hrootO j k)
    rw [map_eval_psSubR, map_zero] at this
    exact this
  -- the base-field roots
  have hrC : ∀ (j : Fin m) (k : Fin SK.F.natDegree), lmap φ (rCK T.Fc Pc j (Fin.cast hnK k)) =
      rot (ι (ζO j k)) (hζK j k) (lsub (Pc.rs j k) (hsr j k)
        (ofPowerSeries ℤ ℚ_[p] (PowerSeries.map ι (ρO (πr j k))))) := by
    intro j k
    have hπ := (πr j k).2
    obtain ⟨hK1, hK2⟩ := repK_spec T.Fc Pc (πr j k) (hPc.pl _ hπ).2.2
    have hid : repEq (RingHom.id K) T.Fc (Pc.fα (Pc.pj (πr j k))) (Pc.pe (πr j k)) =
        (toB T.Fc).map (psSubR (Pc.pe (πr j k)) (Pc.fα (Pc.pj (πr j k)))) := by
      simp [repEq]
    have hmatch := rep_match R φ hR T.Fc hokF _ (hfαok _ (hPc.pl _ hπ).1) (oky _ hπ)
      (hPc.pl _ hπ).2.2 (ρO (πr j k)) (hρO (πr j k)) (hdO (πr j k)) _ (by rw [hid]; exact hK1) hK2
    rw [← ofPS_conjPS, rCK, Fin.val_cast, lmap_ofPS, map_conjPS, hζι, hmatch]
  -- multiplicities
  set ΓP : Fin np → ℕ := fun π ↦ Pc.Γp.getD π 0 with hΓP
  have hdK : ∀ j : Fin m, ∑ k : Fin SK.F.natDegree, Pc.rs j k * ΓP (πr j k) =
      Pc.fN j * Pc.dΓ.getD j 0 := fun j ↦ by
    rw [← (hPc.dΓ j j.2).1, ← hnK]
    exact Fin.sum_univ_eq_sum_range (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) _
  have hsumΓ : ∑ j : Fin m, Pc.dΓ.getD j 0 = Pc.cΓ * SK.F.natDegree := by
    rw [hnK, ← hPc.sum]
    exact Fin.sum_univ_eq_sum_range (fun j ↦ Pc.dΓ.getD j 0) _
  have hmP : ∑ π : Fin np, (Pc.cf.getD (pjF π) 0 * Pc.pe π - ΓP π) =
      ∑ j : Fin m, (SK.F.natDegree * Pc.cf.getD j 0 - Pc.dΓ.getD j 0) := by
    rw [hnK]
    rw [Fin.sum_univ_eq_sum_range (fun π ↦ Pc.cf.getD (Pc.pj π) 0 * Pc.pe π - Pc.Γp.getD π 0),
      Fin.sum_univ_eq_sum_range (fun j ↦ S.F.natDegree * Pc.cf.getD j 0 - Pc.dΓ.getD j 0)]
    exact hPc.mP
  -- the principal witness modulo `p`
  have hwit' := hwit
  rw [← hSkn] at hwit'
  have hnk : Sk.F.natDegree = SK.F.natDegree := by rw [hSkn, hSKn]
  set Y' : Fin m → Fin Sk.F.natDegree → PowerSeries 𝕜 := fun j k ↦
    conjPS (ρ (ζO j (Fin.cast hnk k))) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j (Fin.cast hnk k))))
    with hY'
  have hfc : ∀ j : Fin m, ((Pc.map R.red).fcerts Sk.F.natDegree).getD j ⟨1, [], 0⟩ =
      ⟨Pc.fN j, (List.range Sk.F.natDegree).map ((Pc.map R.red).apx j), Pc.tp.getD j 0⟩ := by
    intro j
    rw [PlaceCert.fcerts_getD _ _ _ (by rw [PlaceCert.map_fib_length]; exact j.2),
      PlaceCert.map_fN _ _ _ j.2]
    rfl
  have htest0 := princTest_of_certN psiP Sk.F.natDegree (Q.mp * Pc.cΓ) T.I.δL
    (T.I.Bc.map (redBL R)) (T.I.Dc.map R.red) (Pc.map R.red).αs ((Pc.map R.red).fcerts _)
    ((Pc.map R.red).bL _ Q.mp) Q.Gw hwit' (m := m) (by simp [PlaceCert.αs, hm]) Y' (fun j k ↦ by
      rw [hfc]
      show (PowerSeries.X : PowerSeries 𝕜) ^ Pc.tp.getD j 0 ∣ Y' j k - thetaT psiP
        (toPoly (((List.range Sk.F.natDegree).map ((Pc.map R.red).apx j)).getD k []))
      have e2 : ((List.range Sk.F.natDegree).map ((Pc.map R.red).apx j)).getD k [] =
          (Pc.map R.red).apx j k := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
      rw [e2]
      have := hapxk j (Fin.cast hnk k)
      simp only [Fin.val_cast] at this
      rw [this, hY']
      beta_reduce
      rw [hζρ]
      exact conj_approx psiP _ (hsr j _) _ _
        (approx_map_ρ R φ hR _ (oky _ (πr j _).2) _ (hdO (πr j (Fin.cast hnk k)))) (htp j _))
  have htestk := princTest_congr (δ' := fun i : Fin Sk.F.natDegree ↦
      T.I.δL.getD (Fin.cast hnk i) 0) (e' := fun q : Fin m × Fin Sk.F.natDegree ↦ Pc.fN q.1)
    (a' := fun q ↦ ρ (αO q.1))
    (σ' := fun q i ↦ basisSer (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
      (Pc.fN q.1) (ρ (αO q.1)) (rot (ρ (ζO q.1 (Fin.cast hnk q.2))) (hζk q.1 _)
        (lsub (Pc.rs q.1 (Fin.cast hnk q.2)) (hsr q.1 _) (ofPowerSeries ℤ 𝕜
          (PowerSeries.map ρ (ρO (πr q.1 (Fin.cast hnk q.2))))))) i)
    (b' := fun q ↦ Q.mp * (Pc.rs q.1 (Fin.cast hnk q.2) * ΓP (πr q.1 (Fin.cast hnk q.2))))
    (fun i ↦ rfl) (fun q ↦ by simp only [hfc]) (fun q ↦ ?_) (fun q i ↦ ?_) (fun q ↦ ?_) htest0
  rotate_left
  · show psiP ((Pc.map R.red).αs.getD q.1 0) = ρ (αO q.1)
    rw [PlaceCert.αs_getD _ _ (by rw [PlaceCert.map_fib_length]; exact q.1.2), PlaceCert.map_fα _ _ _ q.1.2,
      residue_eq_psiP, zL_red R φ hR (hfαok _ q.1.2)]
  · have ha : psiP ((Pc.map R.red).αs.getD q.1 0) = ρ (αO q.1) := by
      rw [PlaceCert.αs_getD _ _ (by rw [PlaceCert.map_fib_length]; exact q.1.2), PlaceCert.map_fα _ _ _ q.1.2,
        residue_eq_psiP, zL_red R φ hR (hfαok _ q.1.2)]
    have hB' : (fun i : Fin Sk.F.natDegree ↦
        (toB ((T.I.Bc.map (redBL R)).getD i [])).map (mapRingHom psiP)) =
        fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ) := funext fun j ↦ (hBρ j).symm
    simp only [hfc]
    rw [ha, hB', ← hDρ, hY']
    beta_reduce
    rw [ofPS_conjPS (ρ (ζO q.1 (Fin.cast hnk q.2))) (hζk q.1 _) (Pc.rs q.1 q.2)
      (hsr q.1 (Fin.cast hnk q.2))]
    rfl
  · show (((Pc.map R.red).bL Sk.F.natDegree Q.mp).getD q.1 []).getD q.2 0 = _
    rw [PlaceCert.bL_getD _ _ _ _ _ (by rw [PlaceCert.map_fib_length]; exact q.1.2) q.2.2,
      PlaceCert.map_rs _ _ _ _ (hrtl q.1) (by rw [(hrt q.1 q.1.2).1, hnS, ← hSkn]; exact q.2.2),
      PlaceCert.map_rπ _ _ _ _ (hrtl q.1) (by rw [(hrt q.1 q.1.2).1, hnS, ← hSkn]; exact q.2.2)]
    rfl
  -- the step
  exact prime_step_places (O := ℤ_[p]) (K₀ := ℚ_[p]) (KK := AlgebraicClosure ℚ_[p])
    (kk := AlgebraicClosure 𝕜) PadicInt.irreducible_p FO hFm SK rfl hBrK hBIK Sk rfl hBrk hBIk
    hnk (by rw [hSKn]; exact hn0) (fun j ↦ B j) D hDm
    (fun j ↦ T.I.δL.getD j 0)
    (by show toB (liftBL R φ hR (T.I.Bc.getD 0 [])) = Polynomial.C D; rw [hB0c]; simp [liftBL, hD])
    hδ0c
    (fun j hj ↦ (hδc j (by rw [← hSKn]; exact j.2)).resolve_left hj) hBK hBk'
    (by rw [Fin.sum_univ_eq_sum_range (fun j ↦ T.I.δL.getD j 0), hSKn]; exact hP.gen)
    x hx y hys hFu hdet hDx hNS αO
    (fun j j' hjj ↦ Jac.isUnit_of_toZMod (by
      rw [map_sub, zL_red R φ hR (hfαok _ j.2), zL_red R φ hR (hfαok _ j'.2)]
      intro h0
      rw [sub_eq_zero, ← PlaceCert.map_fα Pc R.red j j.2, ← PlaceCert.map_fα Pc R.red j' j'.2,
        ← PlaceCert.αs_getD (Pc.map R.red) j (by rw [PlaceCert.map_fib_length]; exact j.2),
        ← PlaceCert.αs_getD (Pc.map R.red) j' (by rw [PlaceCert.map_fib_length]; exact j'.2)] at h0
      exact nodup_getD_ne hαnd'
        (by simp only [PlaceCert.αs, List.length_map, PlaceCert.map_fib_length]; exact j.2)
        (by simp only [PlaceCert.αs, List.length_map, PlaceCert.map_fib_length]; exact j'.2)
        (Fin.val_ne_of_ne hjj) 0 h0))
    (fun j i ↦ Jac.isUnit_of_toZMod (by
      rw [map_sub, zL_red R φ hR (hfαok _ j.2), hxz]
      exact sub_ne_zero.mpr ((hαp j j.2).2 i i.2)))
    (fun j ↦ lift_D_order R φ hR T.I.Dc hP.okD _ (hfαok _ j.2) (hαp j j.2).1)
    (fun j ↦ Pc.fN j) hNpos pjF (fun π ↦ Pc.pe π) (fun π ↦ (hPc.pl π π.2).2.1) ρO hρO πr hπr
    (fun π ↦ by
      obtain ⟨j, hj, k, hk, h⟩ := hPc.surj π π.2
      exact ⟨⟨j, hj⟩, ⟨k, by rw [hnK]; exact hk⟩, Fin.ext h⟩)
    (fun j k ↦ Pc.rs j k) hsr hNr ζO hζO hζK hζk
    (fun j ↦ by simp only [← ofPS_conjPS]; exact (hsplitK j).1)
    (fun j ↦ by simp only [← ofPS_conjPS]; exact (hsplitk j).1)
    (fun j ↦ by simp only [← ofPS_conjPS]; exact (hsplitK j).2)
    (fun j ↦ by simp only [← ofPS_conjPS]; exact (hsplitk j).2)
    ΓP Pc.cΓ (fun j ↦ Pc.cf.getD j 0) (fun j ↦ Pc.dΓ.getD j 0) (fun π ↦ hPc.Γle π π.2) hdK hsumΓ
    (fun j ↦ by rw [hnK]; exact (hPc.dΓ j j.2).2) hmP
    S φ hSKφ hnK (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
    (fun j ↦ T.I.δL.getD j 0) hBS (fun j ↦ hBι j) hDι (fun _ ↦ rfl)
    (fun j ↦ Pc.fα j) (fun j ↦ zL_map R φ hR (hfαok _ j.2))
    (fun j k ↦ rCK T.Fc Pc j k) (fun j ↦ (split_K S T.Fc hSF hmon Pc hPc j j.2).1) hrC
    (fun j k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) (fun _ _ ↦ rfl) p hp.out
    (fun ℓ hℓ ↦ isUnit_natCast_Zp ℓ hℓ) Q.mp hmp htestk

end Step

end Curves
