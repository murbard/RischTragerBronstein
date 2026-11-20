import RischTragerBronstein.Torsion.GoodPrime

/-!
# The prime step from certificates

`hstep_of_prime`: a curve over `K` with `globalCheck` and a prime `p` with a certified reduction
and `primeCheck` satisfy the conclusion of `prime_step_unram` (over `O = ℤ_p`): every principal
multiple `M Γ` gives `(m_p p^v) Γ` principal.
-/

open Polynomial IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section Step

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

local notation "𝕜" => IsLocalRing.ResidueField ℤ_[p]
local notation "ρ" => IsLocalRing.residue ℤ_[p]
local notation "ι" => algebraMap ℤ_[p] ℚ_[p]

lemma GlobalFacts.shape {T : GlobalCert K} (hT : GlobalFacts T) :
    0 < T.n ∧ (toB T.Fc).Monic ∧ (toB T.Fc).natDegree = T.n ∧ InvOK T.k (T.k * T.n) 0 T.Fc ∧
      (toB (invB T.Fc T.k (T.k * T.n))).Monic ∧
      (toB (invB T.Fc T.k (T.k * T.n))).natDegree = T.n := by
  have h := hT.ib
  simp only [ibCheckR, Bool.and_eq_true] at h
  exact shapeCheck_spec h.1.1.1.1.1.1

lemma GlobalFacts.G_eq {T : GlobalCert K} (hT : GlobalFacts T) :
    toPoly T.G = resultant (toB T.Fc) (derivative (toB T.Fc)) T.n (T.n - 1) * toPoly T.I.Dc *
      (Matrix.of fun (i j : Fin T.n) ↦ (toB (T.I.Bc.getD j [])).coeff i).det := by
  obtain ⟨-, hmon, hdeg, -⟩ := hT.shape
  rw [GlobalCert.G, toPoly_mul, toPoly_mul, toPoly_detC,
    toPoly_discRC T.Fc T.n T.kD hmon hdeg fun i ↦ ?_]
  rw [coeff_toB]
  refine (natDegree_toPoly_le_length _).trans ?_
  by_cases hj : i < T.Fc.length
  · have := hT.kF i hj; omega
  · rw [List.getD_eq_default _ _ (by omega)]; simp

lemma nodup_getD_ne {F : Type*} {l : List F} (h : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (hij : i ≠ j) (d : F) : l.getD i d ≠ l.getD j d := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact fun he ↦ hij ((List.Nodup.getElem_inj_iff h).mp he)

lemma getD_map_lt {F G : Type*} (f : F → G) (l : List F) (i : ℕ) (hi : i < l.length) (d : F)
    (d' : G) : (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

lemma fibre_toZMod (W : ℤ_[p][X][X]) (a : ℤ_[p]) :
    (W.map (evalRingHom a)).map PadicInt.toZMod =
      (W.map (mapRingHom PadicInt.toZMod)).map (evalRingHom (PadicInt.toZMod a)) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun q ↦ by
    simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom]
    exact Sup.toZMod_eval q a

lemma isUnit_natCast_Zp (ℓ : ℕ) (hℓ : Nat.Coprime ℓ p) : IsUnit (ℓ : ℤ_[p]) := by
  refine Jac.isUnit_of_toZMod ?_
  rw [map_natCast]
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hℓ.symm h0)

set_option maxHeartbeats 2000000 in
include φ hR in
/-- **Irreducibility** of the curve over `ℚ_p(x)`, over `𝕜(x)` and over `K(x)`, from Eisenstein or
from an irreducible specialization modulo `p`. -/
theorem irr_all (T : GlobalCert K) (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P) :
    Irreducible (((toB (liftBL R φ hR T.Fc)).map (mapRingHom ι)).map
      (algebraMap ℚ_[p][X] (RatFunc ℚ_[p]))) ∧
    Irreducible (((toB (liftBL R φ hR T.Fc)).map (mapRingHom ρ)).map
      (algebraMap 𝕜[X] (RatFunc 𝕜))) ∧
    Irreducible ((toB T.Fc).map (algebraMap K[X] (RatFunc K))) := by
  classical
  obtain ⟨hn0, hmon, hdeg, -⟩ := hT.shape
  have hokF := okB_spec R hP.okF
  have hιi : Function.Injective ι := IsFractionRing.injective ℤ_[p] ℚ_[p]
  set Fp := redBL R T.Fc with hFp
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
  have hSKm : (FO.map (mapRingHom ι)).Monic := hFm.map _
  have hSKd : 0 < (FO.map (mapRingHom ι)).natDegree := by rw [hFm.natDegree_map, hFdeg]; exact hn0
  have hSkm : (FO.map (mapRingHom ρ)).Monic := hFm.map _
  have hSkd : 0 < (FO.map (mapRingHom ρ)).natDegree := by rw [hFm.natDegree_map, hFdeg]; exact hn0
  rcases hP.irr with ⟨hE, hE'⟩ | ⟨a, -, hsmall⟩ | hsub
  · -- Eisenstein
    obtain ⟨heis, heis'⟩ := eisCheck_spec hE
    refine ⟨?_, ?_, irreducible_eisenstein_at (toB T.Fc) hmon (by rw [hdeg]; exact hn0) T.aE
      (fun i hi ↦ by rw [coeff_toB, ← Kron.evalC_eq]; exact heis i (by rwa [hdeg] at hi))
      (by rw [coeff_toB, ← toPoly_deriv, ← Kron.evalC_eq]; exact heis')⟩
    · refine irreducible_eisenstein_at _ hSKm hSKd (φ T.aE) (fun i hi ↦ ?_) ?_
      · rw [hFm.natDegree_map, hFdeg] at hi
        rw [hFι, coeff_map, coe_mapRingHom, eval_map, eval₂_at_apply, coeff_toB, ← Kron.evalC_eq,
          heis i hi, map_zero]
      · rw [hFι, coeff_map, coe_mapRingHom, Polynomial.derivative_map, eval_map, eval₂_at_apply,
          coeff_toB, ← toPoly_deriv, ← Kron.evalC_eq]
        exact (map_ne_zero_iff φ φ.injective).mpr heis'
    · refine irreducible_eisenstein_at _ hSkm hSkd (psiP (R.red T.aE)) (fun i hi ↦ ?_) ?_
      · rw [hFm.natDegree_map, hFdeg] at hi
        have h0 : (FO.coeff i).eval (zL R φ hR T.aE) = 0 := by
          apply hιi
          rw [map_zero, ← eval₂_at_apply, ← eval_map, zL_map R φ hR hP.okE, ← coe_mapRingHom,
            ← coeff_map, hFι, coeff_map, coe_mapRingHom, eval_map, eval₂_at_apply, coeff_toB,
            ← Kron.evalC_eq, heis i hi, map_zero]
        have h1 := congrArg PadicInt.toZMod h0
        rw [Sup.toZMod_eval, zL_red R φ hR hP.okE, map_zero, ← coe_mapRingHom, ← coeff_map,
          hFz] at h1
        rw [hFk, coeff_map, coe_mapRingHom, eval_map, eval₂_at_apply, h1, map_zero]
      · rw [hFk, coeff_map, coe_mapRingHom, Polynomial.derivative_map, eval_map, eval₂_at_apply,
          coeff_toB, ← toPoly_deriv, ← Kron.evalC_eq]
        exact (map_ne_zero_iff _ (psiP (p := p)).injective).mpr hE'
  · -- an irreducible specialization modulo `p`
    set aO : ℤ_[p] := liftZ a with haO
    have haz : PadicInt.toZMod aO = a := toZMod_liftZ a
    set fO : ℤ_[p][X] := FO.map (evalRingHom aO) with hfO
    have hfOm : fO.Monic := hFm.map _
    have hfOn : fO.natDegree = T.n := by rw [hfO, hFm.natDegree_map, hFdeg]
    have hfz : fO.map PadicInt.toZMod = (toB Fp).map (evalRingHom a) := by
      rw [hfO, fibre_toZMod, hFz, haz]
    have hirrz : Irreducible ((toB Fp).map (evalRingHom a)) := by
      have hmp : ((toB Fp).map (evalRingHom a)).natDegree = T.n := by
        rw [← hfz, hfOm.natDegree_map, hfOn]
      have he : toPoly ((redBL R T.Fc).map fun c ↦ Kron.evalC c a) = (toB Fp).map (evalRingHom a) :=
        toPoly_evalFibre Fp a
      rw [← he] at hmp ⊢
      refine irreducible_of_noSmallFactor _ (fun y ↦ List.mem_map.mpr ⟨y.val, List.mem_range.mpr
        (ZMod.val_lt y), ZMod.natCast_zmod_val y⟩) _ T.n (by rw [he, ← hfz]; exact hfOm.map _) hmp hn0
        hsmall
    have hirrO : Irreducible fO :=
      Polynomial.Monic.irreducible_of_irreducible_map PadicInt.toZMod fO hfOm (by rw [hfz]; exact hirrz)
    have hirrQ : Irreducible (fO.map ι) :=
      (hfOm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirrO
    have hcomm : ∀ G : ℤ_[p][X][X], (G.map (mapRingHom ι)).map (evalRingHom (ι aO)) =
        (G.map (evalRingHom aO)).map ι := fun G ↦ by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      exact RingHom.ext fun q ↦ by
        simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom, eval_map, eval₂_at_apply]
    refine ⟨irreducible_ratFunc_of_map _ hSKm (evalRingHom (ι aO)) (by rw [hcomm]; exact hirrQ),
      irreducible_ratFunc_of_map _ hSkm (evalRingHom (psiP a)) ?_,
      irreducible_ratFunc_of_map _ hmon ((evalRingHom (ι aO)).comp (mapRingHom φ)) ?_⟩
    · have e : ((FO.map (mapRingHom ρ)).map (evalRingHom (psiP a))) =
          ((toB Fp).map (evalRingHom a)).map psiP := by
        rw [hFk, Polynomial.map_map, Polynomial.map_map]
        congr 1
        exact RingHom.ext fun q ↦ by
          simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom, eval_map, eval₂_at_apply]
      rw [e]
      exact (MulEquiv.irreducible_iff
        (Polynomial.mapEquiv (PadicInt.residueField (p := p)).symm).toMulEquiv).mpr hirrz
    · have e : (toB T.Fc).map ((evalRingHom (ι aO)).comp (mapRingHom φ)) = fO.map ι := by
        rw [← Polynomial.map_map, ← hFι, hcomm]
      rw [e]; exact hirrQ
  · -- the subset certificate at the first base point
    have hFpm : (toB Fp).Monic := by rw [← hFz]; exact hFm.map _
    have hFpn : (toB Fp).natDegree = T.n := by rw [← hFz, hFm.natDegree_map, hFdeg]
    have hirrZ : Irreducible (toB Fp) := by
      have := irrSubsetCheck_spec _ _ _ _ _ hsub hFpm hFpn hn0 (RingHom.id (ZMod p))
      rwa [Polynomial.mapRingHom_id, Polynomial.map_id] at this
    have hirrO : Irreducible FO :=
      hFm.irreducible_of_irreducible_map (mapRingHom PadicInt.toZMod) FO (by rw [hFz]; exact hirrZ)
    have h1 := irreducible_ratFunc_of_irreducible (Q := ℚ_[p]) FO hFm hirrO
    refine ⟨h1, ?_, ?_⟩
    · rw [hFk]
      exact (hFpm.map _).irreducible_iff_irreducible_map_fraction_map.mp
        (irrSubsetCheck_spec _ _ _ _ _ hsub hFpm hFpn hn0 psiP)
    · rw [hFι] at h1
      have h3 := ((hmon.map (mapRingHom φ)).irreducible_iff_irreducible_map_fraction_map
        (K := RatFunc ℚ_[p])).mpr h1
      exact hmon.irreducible_iff_irreducible_map_fraction_map.mp
        (hmon.irreducible_of_irreducible_map (mapRingHom φ) _ h3)

set_option maxHeartbeats 8000000 in
include φ hR in
/-- **The prime step from certificates.** -/
theorem hstep_of_prime {L Kb : Type*} [Field L] [Algebra K L] [Field Kb] [Algebra K Kb]
    [IsAlgClosed Kb] (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P) :
    ∀ M : ℕ, 0 < M → (∃ γ : K⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := Kb) (fun j : Fin T.αL.length ↦ T.αL.getD j 0)
          (fun j (k : Fin S.F.natDegree) ↦ (T.yL.getD j []).getD k 0)
          (fun j k ↦ M * (T.ΓL.getD j []).getD k 0) (M * T.cdeg) γ) →
      ∃ v : ℕ, ∃ γ : K⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := Kb) (fun j : Fin T.αL.length ↦ T.αL.getD j 0)
          (fun j (k : Fin S.F.natDegree) ↦ (T.yL.getD j []).getD k 0)
          (fun j k ↦ (P.mp * p ^ v) * (T.ΓL.getD j []).getD k 0) ((P.mp * p ^ v) * T.cdeg) γ := by
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
  -- the points of `Γ`
  set m := T.αL.length with hm
  obtain ⟨hyl, -, hptK⟩ := ptCheck_spec (RingHom.id K) (n := S.F.natDegree) hmon
    (by rw [hdeg, hnS]) (by rw [hnS]; exact hT.pt)
  have hαmem : ∀ j : Fin m, T.αL.getD j 0 ∈ T.αL := fun j ↦ by
    rw [List.getD_eq_getElem _ _ j.2]; exact List.getElem_mem _
  have hymem : ∀ j : Fin m, T.yL.getD j [] ∈ T.yL := fun j ↦ by
    rw [List.getD_eq_getElem _ _ (by rw [hyl]; exact j.2)]; exact List.getElem_mem _
  have hylen : ∀ j : Fin m, (T.yL.getD j []).length = S.F.natDegree := fun j ↦ (hptK j j.2).1.1
  have hyok : ∀ (j : Fin m) (k : ℕ), k < S.F.natDegree → R.ok ((T.yL.getD j []).getD k 0) = true :=
    fun j k hk ↦ hP.oky _ (hymem j) _ (by
      rw [List.getD_eq_getElem (T.yL.getD j []) 0 (by rw [hylen]; exact hk)]
      exact List.getElem_mem _)
  set α' : Fin m → ℤ_[p] := fun j ↦ zL R φ hR (T.αL.getD j 0) with hα'
  have hα'z : ∀ j : Fin m, PadicInt.toZMod (α' j) = (T.αL.map R.red).getD j 0 := fun j ↦ by
    rw [hα', zL_red R φ hR (hP.okα _ (hαmem j)), getD_map_lt _ _ _ j.2 0]
  have hα : ∀ j j', j ≠ j' → IsUnit (α' j - α' j') := fun j j' hjj ↦ Jac.isUnit_of_toZMod (by
    rw [map_sub, hα'z, hα'z]
    exact sub_ne_zero.mpr (nodup_getD_ne hP.αnd (by rw [List.length_map]; exact j.2)
      (by rw [List.length_map]; exact j'.2)
      (Fin.val_ne_of_ne hjj) 0))
  have hαx : ∀ j i, IsUnit (α' j - x i) := fun j i ↦ Jac.isUnit_of_toZMod (by
    rw [map_sub, hα'z, hxz]
    exact sub_ne_zero.mpr ((hP.Γpt j j.2).2.2.1 i i.2))
  have hDα : ∀ j, IsUnit (D.eval (α' j)) := fun j ↦ Jac.isUnit_of_toZMod (by
    rw [hD, toZMod_eval_liftL R φ hR _ hP.okD, hα'z]; exact (hP.Γpt j j.2).2.1)
  set yΓ : Fin m → Fin SK.F.natDegree → ℤ_[p] := fun j k ↦
    zL R φ hR ((T.yL.getD j []).getD k 0) with hyΓ
  have hkS : ∀ k : Fin SK.F.natDegree, (k : ℕ) < S.F.natDegree := fun k ↦ by
    rw [hnS, ← hSKn]; exact k.2
  have hyΓz : ∀ j k, PadicInt.toZMod (yΓ j k) = ((T.yL.map (·.map R.red)).getD j []).getD k 0 :=
    fun j k ↦ by
      rw [hyΓ, zL_red R φ hR (hyok j k (hkS k)), getD_map_lt _ _ _ (by rw [hyl]; exact j.2) [],
        getD_map_lt _ _ _ (by rw [hylen]; exact hkS k) 0]
  have hyΓι : ∀ j k, ι (yΓ j k) = φ ((T.yL.getD j []).getD k 0) := fun j k ↦
    zL_map R φ hR (hyok j k (hkS k))
  have hsplitΓ : ∀ j, FO.map (evalRingHom (α' j)) = ∏ k, (X - Polynomial.C (yΓ j k)) := by
    intro j
    refine prod_eq_of_roots _ (hFm.map _) (by rw [hFm.natDegree_map, hFdeg, hSKn]) (yΓ j)
      (fun k k' h ↦ ?_) (fun k ↦ ?_)
    · have h1 := congrArg ι h
      rw [hyΓι, hyΓι] at h1
      by_contra hne
      exact nodup_getD_ne (hptK j j.2).1.2 (by rw [hylen]; exact hkS k)
        (by rw [hylen]; exact hkS k') (Fin.val_ne_of_ne hne) 0 (φ.injective h1)
    · apply hιi
      show ι (evalW FO (α' j) (yΓ j k)) = ι 0
      rw [map_zero, hFO, map_evalW_lift R φ hR _ hokF _ _ _ _ (zL_map R φ hR (hP.okα _ (hαmem j)))
        (hyΓι j k), (hptK j j.2).2.choose_spec.2.2.2 k (hkS k), map_zero]
  have hFuΓ : ∀ j k, IsUnit (evalW (derivative FO) (α' j) (yΓ j k)) := fun j k ↦
    Jac.isUnit_of_toZMod (by
      rw [hFO, toZMod_evalW_deriv_lift R φ hR _ hokF, hα'z, hyΓz]
      exact (hP.Γpt j j.2).2.2.2 k (by rw [← hSKn]; exact k.2))
  set ΓC : Fin m → Fin SK.F.natDegree → ℕ := fun j k ↦ (T.ΓL.getD j []).getD k 0 with hΓC
  have hsumΓ : ∑ j, ∑ k, ΓC j k = T.cdeg * SK.F.natDegree := by
    have e : ∀ j : ℕ, ∑ k : Fin SK.F.natDegree, (T.ΓL.getD j []).getD k 0 =
        ∑ k ∈ Finset.range T.n, (T.ΓL.getD j []).getD k 0 := fun j ↦ by
      rw [Fin.sum_univ_eq_sum_range (fun k ↦ (T.ΓL.getD j []).getD k 0), hSKn]
    rw [hΓC]
    simp only [e]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ∑ k ∈ Finset.range T.n, (T.ΓL.getD j []).getD k 0) m,
      hT.sum, hSKn]
  -- the base field
  have hSKφ : SK.F = S.F.map (mapRingHom φ) := by rw [hSF]; exact hFι
  have hnK : SK.F.natDegree = S.F.natDegree := by rw [hSKn, hnS]
  have hBS : S.IsIntBasis Kb (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
      (fun j ↦ T.I.δL.getD j 0) := by
    have := ibCheckR_spec (K := Kb) S T.Fc (RingHom.id K)
      (by rw [hSF, Polynomial.mapRingHom_id, Polynomial.map_id]) T.n T.k hnS.symm T.I T.G hT.ib
      (dvd_of_eq hT.G_eq.symm)
    simpa only [Polynomial.mapRingHom_id, Polynomial.map_id] using this
  have hY0 : ∀ j : Fin m, ∃ Y : Fin S.F.natDegree → PowerSeries K,
      (∀ k, PowerSeries.constantCoeff (Y k) = (T.yL.getD j []).getD k 0) ∧
      S.F.map (branchSub (C := K) (K := K) 1 (T.αL.getD j 0)) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ K (Y k))) := by
    intro j
    obtain ⟨Y, hYc, hYs, -⟩ := (hptK j j.2).2
    refine ⟨Y, hYc, ?_⟩
    rw [Polynomial.mapRingHom_id, Polynomial.map_id, RingHom.id_apply] at hYs
    exact (congrArg (fun Q : K[X][X] ↦ Q.map (branchSub (C := K) (K := K) 1 (T.αL.getD j 0)))
      hSF).trans hYs
  choose Y0 hY0c hsp using hY0
  have hyinj : ∀ j : Fin m, Function.Injective fun k : Fin S.F.natDegree ↦
      (T.yL.getD j []).getD k 0 := fun j k k' h ↦ by
    by_contra hne
    exact nodup_getD_ne (hptK j j.2).1.2 (by rw [hylen]; exact k.2) (by rw [hylen]; exact k'.2)
      (Fin.val_ne_of_ne hne) 0 h
  -- the principal witness modulo `p`
  obtain ⟨-, -, hptp⟩ := ptCheck_spec psiP (n := Sk.F.natDegree) hmonp (by rw [hdegp, hSkn])
    (by rw [hSkn]; exact hP.pt)
  have hYp : ∀ j : Fin m, ∃ Y : Fin Sk.F.natDegree → PowerSeries 𝕜,
      (∀ k, PowerSeries.constantCoeff (Y k) =
        psiP (((T.yL.map (·.map R.red)).getD j []).getD k 0)) ∧
      ((toB Fp).map (mapRingHom psiP)).map (branchSub (C := 𝕜) (K := 𝕜) 1
        (psiP ((T.αL.map R.red).getD j 0))) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ 𝕜 (Y k))) ∧
      ∀ k : Fin Sk.F.natDegree, (PowerSeries.X : PowerSeries 𝕜) ^ (P.cΓ.getD j (dcert _)).prec ∣
        Y k - thetaT psiP (toPoly ((P.cΓ.getD j (dcert _)).ys.getD k [])) := by
    intro j
    obtain ⟨Y, hYc, hYs, hYt, -⟩ := (hptp j (by rw [List.length_map]; exact j.2)).2
    exact ⟨Y, hYc, hYs, hYt⟩
  choose Yp hYpc hYps hYpt using hYp
  have htest := princTest_of_cert psiP Sk.F.natDegree (P.mp * T.cdeg) T.I.δL
    (T.I.Bc.map (redBL R)) (T.I.Dc.map R.red) (T.αL.map R.red) P.cΓ
    (T.ΓL.map (·.map (P.mp * ·))) P.Gw (by rw [hSkn]; exact hP.wit) (List.length_map _) Yp hYpt
  have hyinjp : ∀ j : Fin m, Function.Injective fun k : Fin Sk.F.natDegree ↦
      psiP (((T.yL.map (·.map R.red)).getD j []).getD k 0) := fun j k k' h ↦ by
    have hl : ((T.yL.map (·.map R.red)).getD j []).length = Sk.F.natDegree := by
      rw [getD_map_lt _ _ _ (by rw [hyl]; exact j.2) [], List.length_map, hylen, hnS, hSkn]
    by_contra hne
    exact nodup_getD_ne (hP.Γpt j j.2).1 (by rw [hl]; exact k.2) (by rw [hl]; exact k'.2)
      (Fin.val_ne_of_ne hne) 0 (psiP.injective h)
  obtain ⟨γk, hγk0, hγk⟩ := (Sk.principal_iff_test_unram (K := AlgebraicClosure 𝕜) hBk
    (fun j : Fin m ↦ psiP ((T.αL.map R.red).getD j 0))
    (fun j k ↦ psiP (((T.yL.map (·.map R.red)).getD j []).getD k 0)) Yp hYpc
    (fun j ↦ (congrArg (fun Q : 𝕜[X][X] ↦ Q.map (branchSub (C := 𝕜) (K := 𝕜) 1
      (psiP ((T.αL.map R.red).getD j 0)))) hSkF).trans (hYps j)) hyinjp
    (fun j k ↦ ((T.ΓL.map (·.map (P.mp * ·))).getD j []).getD k 0) (P.mp * T.cdeg)).mpr htest
  have eα : (fun j ↦ ρ (α' j)) = fun j : Fin m ↦ psiP ((T.αL.map R.red).getD j 0) :=
    funext fun j ↦ by rw [residue_eq_psiP, hα'z]
  have eY : (fun (j : Fin m) (k : Fin Sk.F.natDegree) ↦ ρ (yΓ j (Fin.cast (by rw [hSkn, hSKn]) k))) =
      fun (j : Fin m) (k : Fin Sk.F.natDegree) ↦
        psiP (((T.yL.map (·.map R.red)).getD j []).getD k 0) :=
    _root_.funext fun j ↦ _root_.funext fun k ↦ by rw [residue_eq_psiP, hyΓz]; rfl
  have eΓ : (fun (j : Fin m) (k : Fin Sk.F.natDegree) ↦
      P.mp * ΓC j (Fin.cast (by rw [hSkn, hSKn]) k)) =
      fun (j : Fin m) (k : Fin Sk.F.natDegree) ↦
        ((T.ΓL.map (·.map (P.mp * ·))).getD j []).getD k 0 := by
    refine _root_.funext fun j ↦ _root_.funext fun k ↦ ?_
    rw [getD_map_lt _ _ _ (by rw [hT.Γl]; exact j.2) []]
    simp only [hΓC, Fin.val_cast]
    by_cases hk : (k : ℕ) < (T.ΓL.getD j []).length
    · rw [getD_map_lt _ _ _ hk 0]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        mul_zero]
  have hγk' : Sk.DivGEU (K := AlgebraicClosure 𝕜) (fun j ↦ ρ (α' j))
      (fun j k ↦ ρ (yΓ j (Fin.cast (by rw [hSkn, hSKn]) k)))
      (fun j k ↦ P.mp * ΓC j (Fin.cast (by rw [hSkn, hSKn]) k)) (P.mp * T.cdeg) γk := by
    rw [eα, eY, eΓ]; exact hγk
  exact prime_step_unram (O := ℤ_[p]) (K₀ := ℚ_[p]) (KK := AlgebraicClosure ℚ_[p])
    (kk := AlgebraicClosure 𝕜) PadicInt.irreducible_p FO hFm SK rfl hBrK hBIK Sk rfl hBrk hBIk
    (by rw [hSkn, hSKn]) (by rw [hSKn]; exact hn0) (fun j ↦ B j) D hDm
    (fun j ↦ T.I.δL.getD j 0)
    (by show toB (liftBL R φ hR (T.I.Bc.getD 0 [])) = Polynomial.C D; rw [hB0c]; simp [liftBL, hD])
    hδ0c
    (fun j hj ↦ (hδc j (by rw [← hSKn]; exact j.2)).resolve_left hj) hBK hBk'
    (by rw [Fin.sum_univ_eq_sum_range (fun j ↦ T.I.δL.getD j 0), hSKn]; exact hP.gen)
    x hx y hys hFu hdet hDx hNS α' hα hαx hDα yΓ hsplitΓ hFuΓ ΓC T.cdeg
    (fun j ↦ ∑ k, ΓC j k) (fun j k ↦ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ k)) hsumΓ S φ hSKφ hnK (fun j ↦ toB (T.I.Bc.getD j [])) (toPoly T.I.Dc)
    (fun j ↦ T.I.δL.getD j 0) hBS (fun j ↦ hBι j) hDι (fun _ ↦ rfl)
    (fun j ↦ T.αL.getD j 0) (fun j ↦ zL_map R φ hR (hP.okα _ (hαmem j)))
    (fun j k ↦ (T.yL.getD j []).getD k 0) hyΓι Y0 hY0c hsp hyinj
    (fun j k ↦ (T.ΓL.getD j []).getD k 0) (fun _ _ ↦ rfl) p hp.out
    (fun ℓ hℓ ↦ isUnit_natCast_Zp ℓ hℓ) P.mp hP.mp γk hγk0 hγk'

end Step

end Curves
