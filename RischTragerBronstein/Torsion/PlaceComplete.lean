import RischTragerBronstein.Torsion.RamGood
import RischTragerBronstein.Torsion.PicTorsion3
import RischTragerBronstein.Torsion.PlaceWitSpec

/-!
# The multiplier `m_p` is found by the search

At a prime `p` passing the global checks (`PrimeFacts`) and the checks of a place certificate that
do not involve the multiplier (`primePre`), the reduced divisor `Γ − c ∞ₓ` over the finite field
`𝕜 = 𝔽_p` has finite order (`exists_principal_test_places`, Riemann's inequality + Frobenius +
pigeonhole). **`exists_placeWit`**: there is `m ≥ 1` such that, whenever the fibre precisions
are large enough for `m` (`testSideN`, a decidable condition on the place data), the kernel search
`placeWit` at `m` succeeds, and the resulting `PrimeData` passes `primeCheck`
(**`autoPlaceData_isSome`**, **`autoPlaceData_spec`**).

The place data must be complete: every place carries a root and the multiplicities `Γ_π` add up
to `c n` (`Facts.surj`, `Facts.places`, checked by `PlaceCert.check`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section Pre

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- The checks of `primeCheck` that do not involve the multiplier `m_p`. -/
def PlaceCert.primePre (Fc : BPoly K) (n : ℕ) (Dc : CPoly K) (xs : List (ZMod p))
    (D : PlaceCert K) : Bool :=
  D.αs.all R.ok && (List.range D.pl.length).all (fun π ↦ (D.py π).all R.ok) &&
  (List.range D.fib.length).all (fun j ↦ (List.range n).all fun k ↦ R.ok (D.rζ j k)) &&
  decide (D.map R.red).αs.Nodup &&
  (List.range D.fib.length).all (fun j ↦
    decide ((compC (Dc.map R.red) (shiftC (R.red (D.fα j)) 1)).getD (muD Dc (D.fα j) 1) 0 ≠ 0) &&
    (List.range xs.length).all fun i ↦ decide (R.red (D.fα j) ≠ xs.getD i 0)) &&
  (List.range D.pl.length).all (fun π ↦
    decide ((bivEval (derivYB (redBL R Fc)) (shiftC (R.red (D.fα (D.pj π))) (D.pe π))
      ((D.py π).map R.red)).getD
        (ordC (bivEval (derivYB Fc) (shiftC (D.fα (D.pj π)) (D.pe π)) (D.py π))) 0 ≠ 0)) &&
  (D.map R.red).sepCheckP n

lemma PlaceCert.primeCheck_eq (Fc : BPoly K) (n : ℕ) (δL : List ℕ) (Bc : List (BPoly K))
    (Dc : CPoly K) (xs : List (ZMod p)) (D : PlaceCert K) (Q : PlaceCert.PrimeData p) :
    D.primeCheck R Fc n δL Bc Dc xs Q = (D.primePre R Fc n Dc xs && decide (1 ≤ Q.mp) &&
      princWitCheckN n (Q.mp * D.cΓ) δL (Bc.map (redBL R)) (Dc.map R.red) (D.map R.red).αs
        ((D.map R.red).fcerts n) ((D.map R.red).bL n Q.mp) Q.Gw) := rfl

end Pre

section Side

variable {F : Type*} [Field F] [DecidableEq F]

lemma compC_shift_getD_zero' (Dc : CPoly F) (a : F) (N : ℕ) (hN : 0 < N) :
    (compC Dc (shiftC a N)).getD 0 0 = Kron.evalC Dc a := by
  rw [← coeff_toPoly, toPoly_compC, toPoly_shiftC, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, Kron.evalC_eq]
  simp [zero_pow hN.ne']

/-- **Enough precision** (with poles of the basis at the fibres): the side conditions of the test
at `m Γ` hold as soon as `m s Γ_π + μ_j` is below the fibre precision (`μ_j` the order of `D` at
the fibre `j`). -/
lemma testSideN_of_tpM (n m : ℕ) (Dc : CPoly F) (Pc : PlaceCert F)
    (hμ : ∀ j < Pc.fib.length,
      muD Dc (Pc.fα j) (Pc.fN j) < (compC Dc (shiftC (Pc.fα j) (Pc.fN j))).length)
    (htp : ∀ j < Pc.fib.length, ∀ k < n,
      m * (Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) + muD Dc (Pc.fα j) (Pc.fN j) ≤ Pc.tp.getD j 0) :
    testSideN n Dc Pc.αs (Pc.fcerts n) (Pc.bL n m) = true := by
  have hl : Pc.αs.length = Pc.fib.length := by simp [PlaceCert.αs]
  simp only [testSideN, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro j hj
  rw [hl] at hj
  rw [Pc.αs_getD j hj, Pc.fcerts_getD n j hj]
  refine ⟨hμ j hj, fun k hk ↦ ?_⟩
  simp only [rowsN, muAtN, Pc.αs_getD j hj, Pc.fcerts_getD n j hj, Pc.bL_getD n m j k hj hk]
  exact htp j hj k hk

/-- **Enough precision**: if `D` does not vanish at the fibres, the side conditions of the test at
`m Γ` hold as soon as `m s Γ_π` is below the fibre precision. -/
lemma testSideN_of_tp (n m : ℕ) (Dc : CPoly F) (Pc : PlaceCert F)
    (hN : ∀ j < Pc.fib.length, 0 < Pc.fN j)
    (hD : ∀ j < Pc.fib.length, Kron.evalC Dc (Pc.fα j) ≠ 0)
    (htp : ∀ j < Pc.fib.length, ∀ k < n,
      m * (Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) ≤ Pc.tp.getD j 0) :
    testSideN n Dc Pc.αs (Pc.fcerts n) (Pc.bL n m) = true := by
  have hl : Pc.αs.length = Pc.fib.length := by simp [PlaceCert.αs]
  have h0 : ∀ j < Pc.fib.length, (compC Dc (shiftC (Pc.fα j) (Pc.fN j))).getD 0 0 ≠ 0 :=
    fun j hj ↦ by rw [compC_shift_getD_zero' _ _ _ (hN j hj)]; exact hD j hj
  have hmu : ∀ j < Pc.fib.length, muD Dc (Pc.fα j) (Pc.fN j) = 0 ∧
      0 < (compC Dc (shiftC (Pc.fα j) (Pc.fN j))).length := by
    intro j hj
    have := h0 j hj
    unfold muD ordC
    cases hP : compC Dc (shiftC (Pc.fα j) (Pc.fN j)) with
    | nil => rw [hP] at this; simp at this
    | cons a P =>
      rw [hP] at this
      simp only [List.getD_cons_zero] at this
      simp [List.findIdx_cons, this]
  simp only [testSideN, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro j hj
  rw [hl] at hj
  rw [Pc.αs_getD j hj, Pc.fcerts_getD n j hj]
  refine ⟨by rw [(hmu j hj).1]; exact (hmu j hj).2, fun k hk ↦ ?_⟩
  simp only [rowsN, muAtN, Pc.αs_getD j hj, Pc.fcerts_getD n j hj, (hmu j hj).1,
    Pc.bL_getD n m j k hj hk, add_zero]
  exact htp j hj k hk

end Side

section Search

lemma firstM_isSome {α β : Type*} (f : α → Option β) :
    ∀ {l : List α} {a : α}, a ∈ l → (f a).isSome → (l.firstM f).isSome
  | b :: l, a, h, ha => by
    simp only [List.firstM]
    rcases List.mem_cons.mp h with rfl | h
    · cases hb : f a with
      | none => simp [hb] at ha
      | some x => simp
    · cases hb : f b with
      | none => simpa using firstM_isSome f h ha
      | some x => simp

lemma firstM_spec {α β : Type*} (f : α → Option β) :
    ∀ {l : List α} {x : β}, l.firstM f = some x → ∃ a ∈ l, f a = some x
  | [], x, h => by simp [List.firstM] at h
  | b :: l, x, h => by
    simp only [List.firstM] at h
    cases hb : f b with
    | none =>
      rw [hb] at h
      obtain ⟨a, ha, hfa⟩ := firstM_spec f (by simpa using h)
      exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩
    | some y =>
      rw [hb] at h
      exact ⟨b, List.mem_cons_self, hb.trans h⟩

end Search

section Step

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

local notation "𝕜" => IsLocalRing.ResidueField ℤ_[p]
local notation "ρ" => IsLocalRing.residue ℤ_[p]
local notation "ι" => algebraMap ℤ_[p] ℚ_[p]

set_option maxHeartbeats 16000000 in
include φ hR in
/-- **The multiplier `m_p` exists and the kernel search finds it** (given enough precision). -/
theorem exists_placeWit {L : Type*} [Field L] [Algebra K L]
    (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P)
    (Pc : PlaceCert K) (hPc : Pc.Facts T.Fc S.F.natDegree)
    (hpre : Pc.primePre R T.Fc T.n T.I.Dc P.xs = true) :
    ∃ mm : ℕ, 0 < mm ∧
      (testSideN T.n (T.I.Dc.map R.red) (Pc.map R.red).αs ((Pc.map R.red).fcerts T.n)
        ((Pc.map R.red).bL T.n mm) = true →
      (placeWit T.n T.I.δL (T.I.Bc.map (redBL R)) (T.I.Dc.map R.red) (Pc.map R.red) mm).isSome) := by
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
  refine ⟨mm, hmm, fun hside ↦ ?_⟩
  -- the test in the form of the kernel search
  have hfc : ∀ j : Fin m, ((Pc.map R.red).fcerts Sk.F.natDegree).getD j ⟨1, [], 0⟩ =
      ⟨Pc.fN j, (List.range Sk.F.natDegree).map ((Pc.map R.red).apx j), Pc.tp.getD j 0⟩ := by
    intro j
    rw [PlaceCert.fcerts_getD _ _ _ (by rw [PlaceCert.map_fib_length]; exact j.2),
      PlaceCert.map_fN _ _ _ j.2]
    rfl
  set Y' : Fin m → Fin Sk.F.natDegree → PowerSeries 𝕜 := fun j k ↦
    conjPS (ρ (ζO j k)) (Pc.rs j k) (PowerSeries.map ρ (ρO (πr j k))) with hY'
  have hY : ∀ (j : Fin m) (k : Fin Sk.F.natDegree), (PowerSeries.X : PowerSeries 𝕜) ^
      (((Pc.map R.red).fcerts Sk.F.natDegree).getD j ⟨1, [], 0⟩).prec ∣
        Y' j k - thetaT psiP (toPoly (((((Pc.map R.red).fcerts Sk.F.natDegree).getD j
          ⟨1, [], 0⟩).ys).getD k [])) := fun j k ↦ by
    rw [hfc]
    show (PowerSeries.X : PowerSeries 𝕜) ^ Pc.tp.getD j 0 ∣ Y' j k - thetaT psiP
      (toPoly (((List.range Sk.F.natDegree).map ((Pc.map R.red).apx j)).getD k []))
    have e2 : ((List.range Sk.F.natDegree).map ((Pc.map R.red).apx j)).getD k [] =
        (Pc.map R.red).apx j k := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    rw [e2, hapxk j k, hY']
    beta_reduce
    rw [hζρ]
    exact conj_approx psiP _ (hsr j _) _ _
      (approx_map_ρ R φ hR _ (oky _ (πr j k).2) _ (hdO (πr j k))) (htp j _)
  have htest0 := princTest_congr
    (δ' := fun i : Fin Sk.F.natDegree ↦ T.I.δL.getD i 0)
    (e' := fun q : Fin m × Fin Sk.F.natDegree ↦
      (((Pc.map R.red).fcerts Sk.F.natDegree).getD q.1 ⟨1, [], 0⟩).N)
    (a' := fun q ↦ psiP ((Pc.map R.red).αs.getD q.1 0))
    (σ' := fun q i ↦ basisSer (fun i : Fin Sk.F.natDegree ↦
        (toB ((T.I.Bc.map (redBL R)).getD i [])).map (mapRingHom psiP))
      ((toPoly (T.I.Dc.map R.red)).map psiP)
      (((Pc.map R.red).fcerts Sk.F.natDegree).getD q.1 ⟨1, [], 0⟩).N
      (psiP ((Pc.map R.red).αs.getD q.1 0)) (HahnSeries.ofPowerSeries ℤ 𝕜 (Y' q.1 q.2)) i)
    (b' := fun q ↦ (((Pc.map R.red).bL Sk.F.natDegree mm).getD q.1 []).getD q.2 0)
    (fun i ↦ rfl) (fun q ↦ by simp only [hfc]) (fun q ↦ hρα q.1) (fun q i ↦ ?_) (fun q ↦ ?_) htestk
  rotate_left
  · have hB' : (fun j : Fin Sk.F.natDegree ↦ (B j).map (mapRingHom ρ)) =
        fun i : Fin Sk.F.natDegree ↦ (toB ((T.I.Bc.map (redBL R)).getD i [])).map (mapRingHom psiP) := funext fun j ↦ hBρ j
    simp only [hfc]
    rw [← hρα, hB', hDρ, hY']
    beta_reduce
    rw [ofPS_conjPS (ρ (ζO q.1 q.2)) (hζk q.1 _) (Pc.rs q.1 q.2) (hsr q.1 q.2)]
  · show _ = (((Pc.map R.red).bL Sk.F.natDegree mm).getD q.1 []).getD q.2 0
    rw [PlaceCert.bL_getD _ _ _ _ _ (by rw [PlaceCert.map_fib_length]; exact q.1.2) q.2.2,
      PlaceCert.map_rs _ _ _ _ (hrtl q.1) (hrtk q.1 q.2),
      PlaceCert.map_rπ _ _ _ _ (hrtl q.1) (hrtk q.1 q.2)]
    rfl
  rw [← hSkn] at hside ⊢
  exact placeWit_isSome psiP hside (PlaceCert.map_fib_length _ _) Y' hY htest0

/-- **Whatever the search returns passes `primeCheck`** (given the checks not involving `m_p`). -/
theorem autoPlaceData_spec {T : GlobalCert K} {Pc : PlaceCert K} {xs : List (ZMod p)} {B : ℕ}
    {Q : PlaceCert.PrimeData p} (hpre : Pc.primePre R T.Fc T.n T.I.Dc xs = true)
    (h : autoPlaceData R T Pc B = some Q) :
    Pc.primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc xs Q = true := by
  obtain ⟨a, ha, hfa⟩ := firstM_spec _ h
  obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hfa
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
  have hw := placeWit_spec hG
  rw [PlaceCert.primeCheck_eq, hpre]
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, hw⟩

include φ hR in
/-- **The search for `m_p` succeeds**: for every bound `B ≥ m_p` (and enough precision at `m_p`),
`autoPlaceData` returns prime data accepted by `primeCheck`. -/
theorem exists_autoPlaceData {L : Type*} [Field L] [Algebra K L]
    (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P)
    (Pc : PlaceCert K) (hPc : Pc.Facts T.Fc S.F.natDegree)
    (hpre : Pc.primePre R T.Fc T.n T.I.Dc P.xs = true) :
    ∃ mm : ℕ, 0 < mm ∧ ∀ B, mm ≤ B →
      testSideN T.n (T.I.Dc.map R.red) (Pc.map R.red).αs ((Pc.map R.red).fcerts T.n)
        ((Pc.map R.red).bL T.n mm) = true →
      ∃ Q, autoPlaceData R T Pc B = some Q ∧
        Pc.primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc P.xs Q = true := by
  obtain ⟨mm, hmm, hw⟩ := exists_placeWit R φ hR S T hSF hT P hP Pc hPc hpre
  refine ⟨mm, hmm, fun B hB hside ↦ ?_⟩
  have hsome : (autoPlaceData R T Pc B).isSome := by
    refine firstM_isSome _ (a := mm) (List.mem_map.mpr ⟨mm - 1, List.mem_range.mpr (by omega),
      by omega⟩) ?_
    rw [Option.isSome_map]
    exact hw hside
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨Q, hQ, autoPlaceData_spec R hpre hQ⟩

include φ hR in
/-- **The search for `m_p` succeeds with precision chosen from the bound**: if the fibre
precisions dominate `B s Γ_π + μ_j` (`μ_j` the order of `D` at the fibre modulo `p`; a condition on
the data and `B` only), the search at every bound `B ≥ m_p` returns prime data accepted by
`primeCheck`. -/
theorem exists_autoPlaceData_tp {L : Type*} [Field L] [Algebra K L]
    (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P)
    (Pc : PlaceCert K) (hPc : Pc.Facts T.Fc S.F.natDegree)
    (hpre : Pc.primePre R T.Fc T.n T.I.Dc P.xs = true) :
    ∃ mm : ℕ, 0 < mm ∧ ∀ B, mm ≤ B →
      (∀ j < Pc.fib.length, muD (T.I.Dc.map R.red) (R.red (Pc.fα j)) (Pc.fN j) <
        (compC (T.I.Dc.map R.red) (shiftC (R.red (Pc.fα j)) (Pc.fN j))).length) →
      (∀ j < Pc.fib.length, ∀ k < T.n,
        B * (Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) +
          muD (T.I.Dc.map R.red) (R.red (Pc.fα j)) (Pc.fN j) ≤ Pc.tp.getD j 0) →
      ∃ Q, autoPlaceData R T Pc B = some Q ∧
        Pc.primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc P.xs Q = true := by
  obtain ⟨mm, hmm, h⟩ := exists_autoPlaceData R φ hR S T hSF hT P hP Pc hPc hpre
  refine ⟨mm, hmm, fun B hB hμ htp ↦ h B hB ?_⟩
  have hnS : S.F.natDegree = T.n := by rw [hSF, hT.shape.2.2.1]
  have hrtk : ∀ j < Pc.fib.length, ∀ k < T.n, j < Pc.rt.length ∧ k < (Pc.rt.getD j []).length :=
    fun j hj k hk ↦ ⟨by rw [hPc.rtl]; exact hj, by rw [(hPc.rt j hj).1, hnS]; exact hk⟩
  refine testSideN_of_tpM _ _ _ _ (fun j hj ↦ ?_) (fun j hj k hk ↦ ?_)
  · rw [PlaceCert.map_fib_length] at hj
    rw [PlaceCert.map_fα _ _ _ hj, PlaceCert.map_fN _ _ _ hj]
    exact hμ j hj
  · rw [PlaceCert.map_fib_length] at hj
    obtain ⟨h1, h2⟩ := hrtk j hj k hk
    rw [PlaceCert.map_rs _ _ _ _ h1 h2, PlaceCert.map_rπ _ _ _ _ h1 h2, PlaceCert.map_Γp,
      PlaceCert.map_tp, PlaceCert.map_fα _ _ _ hj, PlaceCert.map_fN _ _ _ hj]
    exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hB) _) (htp j hj k hk)

end Step

end Curves
