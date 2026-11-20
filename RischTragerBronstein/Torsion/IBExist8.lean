import RischTragerBronstein.Torsion.IBExist7
import RischTragerBronstein.Torsion.RaisePrec
import RischTragerBronstein.Curves.CoverComplete

/-!
# Integral bases exist (8): certified integral bases exist

**`exists_ibCert`**: for a curve defined over `F`, branch certificates at distinct points covering the
roots of the discriminant, and a certificate above infinity, there is an integral-basis certificate
accepted by `ibCheck` (with the cover polynomial `disc · D · det` of `GlobalCert.G`) and by
`normCheck`, with a monic denominator, at the same points. The basis is `exists_basis` along the
certified branch systems; the certificates are raised to a sufficient precision (`raise_certCheck`),
the systems transferred (`regAt_transfer`, …), and the checks are complete
(`basisCheckAt_complete`, `basisCheckInfS_complete`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup

section InfTransfer

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable {S : CurveData C L}

lemma infSys_root (τ τ' : S.InfSys) (hN : τ.N = τ'.N) (k' : Fin S.F.natDegree) :
    ∃ k, τ'.r k' = τ.r k := by
  have h := S.root_of_split _ τ'.r τ'.hs k'
  have hg : infSub (C := C) (K := C) τ'.N = infSub τ.N := by rw [hN]
  rw [hg, τ.hs, eval_prod] at h
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h
  exact ⟨k, by simpa [sub_eq_zero] using hk⟩

lemma infSys_ev (τ τ' : S.InfSys) (hN : τ.N = τ'.N) (k k' : Fin S.F.natDegree)
    (hk : τ'.r k' = τ.r k) (f : C⟮S.x⟯⟮S.y⟯) : τ'.ev k' f = τ.ev k f := by
  unfold InfSys.ev
  have hg : infSub (C := C) (K := C) τ'.N = infSub τ.N := by rw [hN]
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries C ↦ φ f) (S.embG_congr hg _ _ hk _ _)

lemma poleBd_transfer (τ τ' : S.InfSys) (hN : τ.N = τ'.N) (B : Fin S.F.natDegree → C[X][X])
    (D : C[X]) (δ : Fin S.F.natDegree → ℕ) (h : PoleBd τ B D δ) : PoleBd τ' B D δ := by
  intro j k'
  obtain ⟨k, hk⟩ := infSys_root τ τ' hN k'
  rw [infSys_ev τ τ' hN k k' hk, ← hN]
  exact h j k

lemma indepInf_transfer (τ τ' : S.InfSys) (hN : τ.N = τ'.N) (B : Fin S.F.natDegree → C[X][X])
    (D : C[X]) (δ : Fin S.F.natDegree → ℕ) (h : IndepInf τ B D δ) : IndepInf τ' B D δ := by
  intro c hc
  refine h c fun k ↦ ?_
  obtain ⟨k', hk'⟩ := infSys_root τ' τ hN.symm k
  have e : ∀ f, τ.ev k f = τ'.ev k' f := fun f ↦ infSys_ev τ' τ hN.symm k' k hk' f
  simp only [e]
  rw [hN]
  exact hc k'

end CurveData

end InfTransfer

section Split

variable {F K : Type*} [Field F] [Field K]

lemma root_of_split_map (ψ : F →+* K) (p : F[X]) (hp : p ≠ 0)
    (hs : Multiset.card p.roots = p.natDegree) (z : K) (hz : (p.map ψ).eval z = 0) :
    ∃ b, p.IsRoot b ∧ z = ψ b := by
  classical
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hs, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_multiset_prod, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd ((map_eq_zero_iff _ ψ.injective).mp h) (leadingCoeff_ne_zero.mpr hp)
  · obtain ⟨u, hu, hu0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hu
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      eval_sub, eval_X, eval_C] at hu0
    obtain ⟨r, hr', rfl⟩ : ∃ r', r' ∈ p.roots ∧ r' = r := ⟨r, hr, rfl⟩
    exact ⟨r, (mem_roots hp).mp hr', sub_eq_zero.mp hu0⟩

end Split

section Assemble

variable {F E : Type*} [Field F] [CharZero F] [DecidableEq F] [Field E] [Algebra F E]

namespace CurveData

lemma ofB_C (D : F[X]) : ofB (Polynomial.C D : F[X][X]) = [dcOf D] := by
  simp [ofB, dcOf]

lemma dcOf_getLast (D : F[X]) (hD : D.Monic) : (dcOf D).getLast? = some 1 := by
  rw [dcOf, List.getLast?_map, List.getLast?_range]
  simp only [Option.map_some, Nat.add_sub_cancel]
  exact congrArg some hD

variable (S : CurveData F E)

lemma toPoly_detC_bcOf (B : Fin S.F.natDegree → F[X][X]) :
    toPoly (detC S.F.natDegree (bcOf B)) = (coeffMat B).det := by
  rw [toPoly_detC]
  congr 1
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.of_apply, bcOf_getD, toB_ofB]; rfl

/-- **Certified integral bases exist.** -/
theorem exists_ibCert (Fc : BPoly F) (hSF : S.F = toB Fc) (k kD : ℕ)
    (hsh : shapeCheck Fc S.F.natDegree k = true) (pts : List (F × BranchCert F))
    (hpts : ∀ p ∈ pts, certCheck Fc S.F.natDegree p.1 p.2 = true)
    (hnd : (pts.map Prod.fst).Nodup) (hdisc0 : toPoly (discRC Fc S.F.natDegree kD) ≠ 0)
    (hdisc : coverCheck (discRC Fc S.F.natDegree kD) (pts.map Prod.fst) = true)
    (infc : BranchCert F)
    (hinf : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 infc = true) :
    ∃ I : IntBasisCert F,
      ibCheck Fc S.F.natDegree k I
        (mul (mul (discRC Fc S.F.natDegree kD) I.Dc) (detC S.F.natDegree I.Bc)) = true ∧
      normCheck S.F.natDegree I = true ∧ I.Dc.getLast? = some 1 ∧
      I.pts.map Prod.fst = pts.map Prod.fst := by
  classical
  obtain ⟨hn0, hmon, hdeg, hok, hmon', hn'⟩ := shapeCheck_spec hsh
  set A : List S.LocSys := pts.attach.map fun p ↦
    S.locSysOf Fc hSF hmon hdeg p.1.1 p.1.2 (hpts p.1 p.2) with hAdef
  have hAa : A.map LocSys.a = pts.map Prod.fst := by
    simp only [hAdef, List.map_map, Function.comp_def]
    conv_rhs => rw [← List.attach_map_subtype_val pts, List.map_map]
    rfl
  have hA : (A.map LocSys.a).Nodup := hAa ▸ hnd
  set τ := S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' infc hinf with hτ
  obtain ⟨B, D, δ, hG, hI, hP, hII, hz, hpos⟩ := exists_basis A hA τ
  set Bd : ℕ := (pts.map fun p ↦ muD (dcOf D) p.1 p.2.N + p.2.N).sum +
    ∑ j, (infc.N * synDelta k (dcOf D) (ofB (B j)) + infc.N) with hBd
  have hmemA : ∀ p (hp : p ∈ pts), S.locSysOf Fc hSF hmon hdeg p.1 p.2 (hpts p hp) ∈ A :=
    fun p hp ↦ List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩
  -- raising the precision at the points
  have hraise : ∀ p ∈ pts, ∃ c' : BranchCert F, c'.N = p.2.N ∧ Bd ≤ c'.prec ∧
      certCheck Fc S.F.natDegree p.1 c' = true := fun p hp ↦ by
    obtain ⟨c', h1, h2, -, -, -, h3⟩ := raise_certCheck (hpts p hp) Bd
    exact ⟨c', h1, h2, h3⟩
  choose cf hcfN hcfB hcfc using hraise
  have hLm : ∀ p (hp : p ∈ pts), ∃ Lm,
      basisCheckAt S.F.natDegree (bcOf B) (dcOf D) p.1 (cf p hp) Lm = true := by
    intro p hp
    set σ := S.locSysOf Fc hSF hmon hdeg p.1 p.2 (hpts p hp)
    set σ' := S.locSysOf Fc hSF hmon hdeg p.1 (cf p hp) (hcfc p hp)
    have ha : σ.a = σ'.a := rfl
    have hN : σ.N = σ'.N := (hcfN p hp).symm
    refine basisCheckAt_complete Fc hSF hmon hdeg p.1 (cf p hp) (hcfc p hp) B D hG.hD
      (regAt_transfer σ σ' ha hN B D (hG.reg σ (hmemA p hp)))
      (indepAt_transfer σ σ' ha hN B D (hI σ (hmemA p hp))) ?_
    rw [hcfN p hp]
    have h1 : muD (dcOf D) p.1 p.2.N + p.2.N ≤
        (pts.map fun p ↦ muD (dcOf D) p.1 p.2.N + p.2.N).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have := hcfB p hp
    omega
  choose Lm hLm using hLm
  -- raising the precision above infinity
  obtain ⟨ci, hciN, hciB, -, -, -, hcic⟩ := raise_certCheck hinf Bd
  set τ' := S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' ci hcic with hτ'
  have hNτ : τ.N = τ'.N := hciN.symm
  obtain ⟨Linf, hLinf⟩ := basisCheckInfS_complete Fc hSF hmon hdeg k hok hmon' hn' ci hcic B D
    hG.hD δ (poleBd_transfer τ τ' hNτ B D δ hP) (indepInf_transfer τ τ' hNτ B D δ hII)
    (fun j ↦ by
      rw [hciN]
      have h1 : infc.N * synDelta k (dcOf D) (ofB (B j)) + infc.N ≤
          ∑ j, (infc.N * synDelta k (dcOf D) (ofB (B j)) + infc.N) :=
        Finset.single_le_sum (f := fun j ↦ infc.N * synDelta k (dcOf D) (ofB (B j)) + infc.N)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      omega)
  set pts' := pts.attach.map fun p ↦ (p.1.1, cf p.1 p.2, Lm p.1 p.2) with hpts'
  have hfst : pts'.map Prod.fst = pts.map Prod.fst := by
    simp only [hpts', List.map_map, Function.comp_def]
    conv_rhs => rw [← List.attach_map_subtype_val pts, List.map_map]
    rfl
  refine ⟨⟨bcOf B, dcOf D, List.ofFn δ, pts', ci, Linf⟩, ?_, ?_, dcOf_getLast D hG.monic, hfst⟩
  · -- the integral-basis check
    have hG0 : toPoly (mul (mul (discRC Fc S.F.natDegree kD) (dcOf D)) (detC S.F.natDegree (bcOf B)))
        ≠ 0 := by
      rw [CPoly.toPoly_mul, CPoly.toPoly_mul, toPoly_dcOf, S.toPoly_detC_bcOf]
      exact mul_ne_zero (mul_ne_zero hdisc0 hG.hD) hG.det
    have hcov : coverCheck (mul (mul (discRC Fc S.F.natDegree kD) (dcOf D))
        (detC S.F.natDegree (bcOf B))) (pts'.map Prod.fst) = true := by
      refine coverCheck_complete _ _ hG0 (algebraMap F (AlgebraicClosure F)) fun z hz ↦ ?_
      rw [hfst]
      rw [CPoly.toPoly_mul, CPoly.toPoly_mul, toPoly_dcOf, S.toPoly_detC_bcOf, Polynomial.map_mul,
        Polynomial.map_mul, eval_mul, eval_mul] at hz
      rcases mul_eq_zero.mp hz with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact coverCheck_spec _ _ hdisc _ z h
        · obtain ⟨b, hb, rfl⟩ := root_of_split_map _ D hG.hD hG.split z h
          obtain ⟨σ, hσ, hσb⟩ := hG.roots b (by rw [IsRoot, eval_mul, hb.eq_zero, zero_mul])
          exact ⟨b, hAa ▸ List.mem_map.mpr ⟨σ, hσ, hσb⟩, rfl⟩
      · obtain ⟨b, hb, rfl⟩ := root_of_split_map _ _ hG.det hG.detsplit z h
        obtain ⟨σ, hσ, hσb⟩ := hG.roots b (by rw [IsRoot, eval_mul, hb.eq_zero, mul_zero])
        exact ⟨b, hAa ▸ List.mem_map.mpr ⟨σ, hσ, hσb⟩, rfl⟩
    simp only [ibCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨⟨hsh, ?_⟩, fun j hj ↦ ?_⟩, fun q hq ↦ ?_⟩, hcov⟩, hcic⟩, hLinf⟩
    · rw [Bool.eq_false_iff]
      intro h0
      exact hG.hD (by rw [← toPoly_dcOf D]; exact (isZero_iff _).mp h0)
    · rw [show (bcOf B).getD j [] = ofB (B ⟨j, hj⟩) from bcOf_getD B ⟨j, hj⟩, length_ofB]
      have := hG.deg ⟨j, hj⟩
      omega
    · obtain ⟨⟨p, hp⟩, -, rfl⟩ := List.mem_map.mp hq
      exact ⟨hcfc p hp, hLm p hp⟩
  · -- normalization
    simp only [normCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨?_, ?_⟩, fun j hj ↦ ?_⟩
    · rw [show (bcOf B).getD 0 [] = ofB (B ⟨0, hn0⟩) from bcOf_getD B ⟨0, hn0⟩, hG.one hn0, ofB_C]
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      exact hz hn0
    · by_cases hj0 : j = 0
      · exact Or.inl hj0
      · right
        rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
        exact hpos ⟨j, hj⟩ hj0

end CurveData

end Assemble

end Curves
