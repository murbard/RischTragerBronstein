import RischTragerBronstein.Torsion.IBExist5
import RischTragerBronstein.Torsion.CertBasis4
import RischTragerBronstein.Torsion.LogWitB

/-!
# Integral bases exist (6): the check at a finite point accepts the basis

Over a coefficient field `F` (the curve `S` itself defined over `F`), a branch certificate at `a`
gives a branch system with exact roots in `F⟦T⟧` (`locSysOf`). For a basis regular and locally
independent along it, the basis check passes at every precision `≥ μ + N`
(**`basisCheckAt_complete`**): the vanishing conditions are the regularity, and the coefficient
matrix, having trivial kernel, has a left inverse (`exists_leftInvCheck`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup

section LeftInv

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Left inverses exist for injective matrices.** -/
theorem exists_leftInvCheck (M : ℕ → ℕ → F) (R n : ℕ)
    (hinj : ∀ c : Fin n → F, (∀ r < R, ∑ j : Fin n, M r j * c j = 0) → c = 0) :
    ∃ Lm : List (List F), leftInvCheck Lm M R n = true := by
  classical
  set A : Matrix (Fin R) (Fin n) F := Matrix.of fun r j ↦ M r j with hA
  have hker : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    refine hinj c fun r hr ↦ ?_
    have := congrFun hc ⟨r, hr⟩
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hA] using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin
    (LinearMap.ker_eq_bot.mpr hker)
  set Lmat := LinearMap.toMatrix' g with hL
  have hLA : Lmat * A = 1 := by
    rw [hL, ← Matrix.toLin'_toMatrix' g, ← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp]
    rw [show Matrix.toLin' A = A.mulVecLin from rfl, Matrix.toLin'_toMatrix', hg]
    exact LinearMap.toMatrix'_id
  refine ⟨List.ofFn fun i : Fin n ↦ List.ofFn fun r : Fin R ↦ Lmat i r, ?_⟩
  simp only [leftInvCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi j hj
  have h1 := congrFun (congrFun hLA ⟨i, hi⟩) ⟨j, hj⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [← Fin.sum_univ_eq_sum_range]
  convert h1 using 1
  · refine Finset.sum_congr rfl fun r _ ↦ ?_
    have e : ((List.ofFn fun i : Fin n ↦ List.ofFn fun r : Fin R ↦ Lmat i r).getD i []).getD r 0 =
        Lmat ⟨i, hi⟩ r := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, r.2]
    rw [e]
    rfl
  · simp [Fin.ext_iff]

end LeftInv

section Cert

variable {F E : Type*} [Field F] [CharZero F] [DecidableEq F] [Field E] [Algebra F E]

namespace CurveData

variable (S : CurveData F E)

lemma N_pos_of_certCheck {Fc : BPoly F} {n : ℕ} {a : F} {c : BranchCert F}
    (h : certCheck Fc n a c = true) : 0 < c.N := by
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1

lemma exists_certRoots (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (a : F) (c : BranchCert F)
    (h : certCheck Fc S.F.natDegree a c = true) :
    ∃ y : Fin S.F.natDegree → PowerSeries F,
      (∀ k, (PowerSeries.X : PowerSeries F) ^ c.prec ∣
        y k - thetaT ((algebraMap F F).comp (RingHom.id F)) (toPoly (c.ys.getD k []))) ∧
      S.F.map (branchSub c.N (algebraMap F F a)) = ∏ k, (X - Polynomial.C (ofPowerSeries ℤ F (y k))) := by
  obtain ⟨y, hy, -, hs⟩ := certCheck_spec (C := F) (K := F) Fc S.F.natDegree hmon hdeg a c h
    (RingHom.id F)
  refine ⟨y, hy, ?_⟩
  rw [Polynomial.mapRingHom_id, Polynomial.map_id] at hs
  rw [show S.F.map (branchSub c.N (algebraMap F F a)) =
    (toB Fc).map (branchSub c.N (algebraMap F F a)) by rw [hSF]]
  exact hs

/-- The branch system at a certified point, with exact roots in `F⟦T⟧`. -/
noncomputable def locSysOf (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (a : F) (c : BranchCert F)
    (h : certCheck Fc S.F.natDegree a c = true) : S.LocSys where
  a := a
  N := c.N
  hN := N_pos_of_certCheck h
  r := fun k ↦ ofPowerSeries ℤ F (Classical.choose (S.exists_certRoots Fc hSF hmon hdeg a c h) k)
  hs := (Classical.choose_spec (S.exists_certRoots Fc hSF hmon hdeg a c h)).2
  hr := fun _ ↦ lowerBd_ofPS _

variable {S}

/-- The numerators as a list of `BPoly`s. -/
noncomputable def bcOf (B : Fin S.F.natDegree → F[X][X]) : List (BPoly F) :=
  List.ofFn fun j ↦ ofB (B j)

/-- The denominator as a `CPoly`. -/
noncomputable def dcOf (D : F[X]) : CPoly F := (List.range (D.natDegree + 1)).map D.coeff

lemma toPoly_dcOf (D : F[X]) : toPoly (dcOf D) = D := NFC.toPoly_coeffList D

lemma bcOf_getD (B : Fin S.F.natDegree → F[X][X]) (j : Fin S.F.natDegree) :
    (bcOf B).getD j [] = ofB (B j) := by
  rw [bcOf, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- The exact coefficients along a certified system are the truncated ones. -/
lemma ev_coeff_cert (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (a : F) (c : BranchCert F)
    (h : certCheck Fc S.F.natDegree a c = true) (B : Fin S.F.natDegree → F[X][X]) (D : F[X])
    (hD : D ≠ 0) (j k : Fin S.F.natDegree) (s : ℤ)
    (hs : s + muD (dcOf D) a c.N < c.prec) :
    ((S.locSysOf Fc hSF hmon hdeg a c h).ev k (S.fnWQ (B j) D)).coeff s =
      if 0 ≤ s + muD (dcOf D) a c.N then
        (serTrunc (ofB (B j)) (dcOf D) a c.N c.prec (c.ys.getD k [])).getD
          (s + muD (dcOf D) a c.N).toNat 0 else 0 := by
  have hD' : toPoly (dcOf D) ≠ 0 := by rw [toPoly_dcOf]; exact hD
  have hμ : muD (dcOf D) a c.N < (compC (dcOf D) (shiftC a c.N)).length := by
    unfold muD
    refine ordC_lt_length _ ?_
    rw [toPoly_compC_shiftC]
    intro h0
    rcases Polynomial.comp_eq_zero_iff.mp h0 with h1 | ⟨-, h2⟩
    · exact hD' h1
    · have hN := N_pos_of_certCheck h
      have := congrArg natDegree h2
      rw [natDegree_C, natDegree_add_eq_right_of_natDegree_lt (by
        rw [natDegree_C, natDegree_X_pow]; exact hN), natDegree_X_pow] at this
      omega
  have hSF' : S.F = (toB Fc).map (mapRingHom (RingHom.id F)) := by
    rw [Polynomial.mapRingHom_id, Polynomial.map_id]; exact hSF
  set hex := S.exists_certRoots Fc hSF hmon hdeg a c h
  have hy := (Classical.choose_spec hex).1 k
  have key := S.coeff_embG_cert (K := F) Fc (RingHom.id F) hSF' (ofB (B j)) (dcOf D) hD' a c.N
    (N_pos_of_certCheck h) hμ (Classical.choose hex k) (S.root_of_split _ _
      (S.locSysOf Fc hSF hmon hdeg a c h).hs k) (c.ys.getD k []) c.prec hy s hs
  simp only [toB_ofB, toPoly_dcOf, Polynomial.mapRingHom_id, Polynomial.map_id,
    RingHom.id_apply, Algebra.algebraMap_self] at key
  exact key

/-- **The basis check at a certified point accepts a regular, locally independent basis.** -/
theorem basisCheckAt_complete (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (a : F) (c : BranchCert F)
    (h : certCheck Fc S.F.natDegree a c = true) (B : Fin S.F.natDegree → F[X][X]) (D : F[X])
    (hD : D ≠ 0) (hreg : RegAt (S.locSysOf Fc hSF hmon hdeg a c h) B D)
    (hind : IndepAt (S.locSysOf Fc hSF hmon hdeg a c h) B D)
    (hprec : muD (dcOf D) a c.N + c.N ≤ c.prec) :
    ∃ Lm, basisCheckAt S.F.natDegree (bcOf B) (dcOf D) a c Lm = true := by
  classical
  set σ := S.locSysOf Fc hSF hmon hdeg a c h with hσ
  set μ := muD (dcOf D) a c.N with hμ
  have hN : 0 < c.N := N_pos_of_certCheck h
  have hco := S.ev_coeff_cert Fc hSF hmon hdeg a c h B D hD
  have hD' : toPoly (dcOf D) ≠ 0 := by rw [toPoly_dcOf]; exact hD
  have hμl : μ < (compC (dcOf D) (shiftC a c.N)).length := by
    refine ordC_lt_length _ ?_
    rw [toPoly_compC_shiftC]
    intro h0
    rcases Polynomial.comp_eq_zero_iff.mp h0 with h1 | ⟨-, h2⟩
    · exact hD' h1
    · have := congrArg natDegree h2
      rw [natDegree_C, natDegree_add_eq_right_of_natDegree_lt (by
        rw [natDegree_C, natDegree_X_pow]; exact hN), natDegree_X_pow] at this
      omega
  obtain ⟨Lm, hLm⟩ := exists_leftInvCheck (matEntry (bcOf B) (dcOf D) a c) (S.F.natDegree * c.N)
    S.F.natDegree (fun cc hcc ↦ hind cc fun k t ht ↦ by
      rw [HahnSeries.coeff_sum]
      simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
      by_cases ht0 : t < 0
      · exact Finset.sum_eq_zero fun j _ ↦ by rw [hreg j k t ht0, mul_zero]
      · push Not at ht0
        obtain ⟨t', rfl⟩ := Int.eq_ofNat_of_zero_le ht0
        have ht' : t' < c.N := by exact_mod_cast ht
        have hr : k * c.N + t' < S.F.natDegree * c.N := by
          have := k.2
          calc k * c.N + t' < k * c.N + c.N := by omega
            _ = (k + 1) * c.N := by ring
            _ ≤ S.F.natDegree * c.N := Nat.mul_le_mul_right _ this
        rw [← hcc _ hr]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hco j k _ (by push_cast; omega), if_pos (by positivity), mul_comm]
        congr 1
        simp only [matEntry, bcOf_getD]
        rw [show (k * c.N + t') / c.N = k by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt ht', zero_add],
          show (k * c.N + t') % c.N = t' by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht'],
          show ((t' : ℤ) + μ).toNat = μ + t' by omega])
  refine ⟨Lm, ?_⟩
  simp only [basisCheckAt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hμl, hprec⟩, fun j hj k hk t ht ↦ ?_⟩, hLm⟩
  have h1 := hco ⟨j, hj⟩ ⟨k, hk⟩ ((t : ℤ) - μ) (by omega)
  rw [hreg ⟨j, hj⟩ ⟨k, hk⟩ _ (by omega), if_pos (by omega)] at h1
  rw [show ((t : ℤ) - μ + μ).toNat = t by omega] at h1
  rw [show (bcOf B).getD j [] = ofB (B ⟨j, hj⟩) from bcOf_getD B ⟨j, hj⟩]
  exact h1.symm

end CurveData

end Cert

end Curves
