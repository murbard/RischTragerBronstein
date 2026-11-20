import RischTragerBronstein.Mixed.KYCol
import RischTragerBronstein.Mixed.KRGcdT
import RischTragerBronstein.Mixed.KYSpec

/-!
# The column computation of `kyDecide` always succeeds

`psiY : K_{m+1} ⊗ N → (Kₘ ⊗ N)(t)` (`t ↦ t`, the root `X` of `M` to itself). Through it the
coefficient codes of `kyColM` are the coefficient polynomials of the witness (`psiY_kyCoords`), and
`Yⁿ − Â` is `(Yⁿ − Â)` over `(Kₘ ⊗ N)[t]`; a non-zero witness of `Y`-degree `< n` is coprime to it
(`coprime_norm_abstract`, Eisenstein), so `kyColM` answers (`ky_gcd_coprime`).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup

section Field

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [Fact (Irreducible (toPoly (liftQ Fc m M)))]

lemma toAR_embM (a : KF Fc m) :
    NFK.toAR (liftQ Fc m M) (embM Fc m M a) = algebraMap (KF Fc m) _ a := by
  rw [embM, NFK.toAR_mk]; simp [CPoly.toPoly]

/-- `Kₘ → Kₘ ⊗ N` as a ring homomorphism. -/
noncomputable def eM : KF Fc m →+* NFM Fc m M where
  toFun := embM Fc m M
  map_one' := NFK.toAR_injective _ (by rw [toAR_embM, map_one, NFK.toAR_one])
  map_mul' a b := NFK.toAR_injective _ (by
    rw [NFK.toAR_mul, toAR_embM, toAR_embM, toAR_embM, map_mul])
  map_zero' := NFK.toAR_injective _ (by rw [toAR_embM, map_zero, NFK.toAR_zero])
  map_add' a b := NFK.toAR_injective _ (by
    rw [NFK.toAR_add, toAR_embM, toAR_embM, toAR_embM, map_add])

lemma eM_apply (a : KF Fc m) : eM Fc m M a = embM Fc m M a := rfl

/-- The root `X` of `M` in `Kₘ ⊗ N`. -/
def gammaM : NFM Fc m M := NFK.mk _ [0, 1]

lemma eval₂_gammaM : (toPoly (liftQ Fc m M)).eval₂ (eM Fc m M) (gammaM Fc m M) = 0 := by
  apply NFK.toAR_injective
  rw [NFK.toAR_zero]
  have h : NFK.toARHom (liftQ Fc m M) ((toPoly (liftQ Fc m M)).eval₂ (eM Fc m M) (gammaM Fc m M)) =
      (toPoly (liftQ Fc m M)).eval₂ ((NFK.toARHom _).comp (eM Fc m M))
        (NFK.toARHom _ (gammaM Fc m M)) := by
    rw [hom_eval₂]
  have e1 : (NFK.toARHom (liftQ Fc m M)).comp (eM Fc m M) = AdjoinRoot.of _ := by
    ext a
    change NFK.toAR _ (embM Fc m M a) = _
    rw [toAR_embM]; rfl
  have e2 : NFK.toARHom (liftQ Fc m M) (gammaM Fc m M) = AdjoinRoot.root _ := by
    change NFK.toAR _ (NFK.mk _ [0, 1]) = _
    rw [NFK.toAR_mk]; simp [CPoly.toPoly]
  change NFK.toARHom _ _ = _
  rw [h, e1, e2, AdjoinRoot.eval₂_root]

end Field

section Psi

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]

/-- The field `(Kₘ ⊗ N)(t)`. -/
abbrev RK : Type := RatFunc (NFM Fc m M)

/-- `K_{m+1} = Kₘ(t) → (Kₘ ⊗ N)(t)`. -/
noncomputable def psiK0 : KF Fc (m + 1) →+* RK Fc m M :=
  (RatFunc.mapRingHom (mapRingHom (eM Fc m M))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (eM Fc m M).injective))).comp (RFC.toRFHom (K := KF Fc m))

lemma psiK0_poly (c : CPoly (KF Fc m)) :
    psiK0 Fc m M (RFC.mk c [1] : RFC.RatFuncC (KF Fc m)) =
      algebraMap (NFM Fc m M)[X] (RK Fc m M) ((toPoly c).map (eM Fc m M)) := by
  simp only [psiK0, RingHom.comp_apply]
  change RatFunc.mapRingHom _ _ (RFC.toRF (RFC.mk c [1])) = _
  rw [RFC.toRF_mk]
  rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
  simp [CPoly.toPoly]

lemma hroot_psiK0 : (toPoly (liftQ Fc (m + 1) M)).eval₂ (psiK0 Fc m M)
    (algebraMap (NFM Fc m M) (RK Fc m M) (gammaM Fc m M)) = 0 := by
  have h1 := eval₂_gammaM Fc m M
  rw [toPoly_liftQ, eval₂_map] at h1 ⊢
  have e1 : (psiK0 Fc m M).comp (algebraMap ℚ (KF Fc (m + 1))) =
      (algebraMap (NFM Fc m M) (RK Fc m M)).comp ((eM Fc m M).comp (algebraMap ℚ (KF Fc m))) :=
    RingHom.ext_rat _ _
  rw [e1, ← hom_eval₂, h1, map_zero]

/-- **`K_{m+1} ⊗ N → (Kₘ ⊗ N)(t)`.** -/
noncomputable def psiY : NFM Fc (m + 1) M →+* RK Fc m M :=
  liftNFM (m + 1) M (psiK0 Fc m M) _ (hroot_psiK0 Fc m M)

end Psi

section Repr

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [Fact (Irreducible (toPoly (liftQ Fc m M)))]

/-- Every element is its representative evaluated at `X`. -/
lemma eval₂_gammaM_self (a : NFM Fc m M) :
    (toPoly a.1).eval₂ (eM Fc m M) (gammaM Fc m M) = a := by
  apply NFK.toAR_injective
  have h : NFK.toARHom (liftQ Fc m M) ((toPoly a.1).eval₂ (eM Fc m M) (gammaM Fc m M)) =
      (toPoly a.1).eval₂ ((NFK.toARHom _).comp (eM Fc m M)) (NFK.toARHom _ (gammaM Fc m M)) := by
    rw [hom_eval₂]
  have e1 : (NFK.toARHom (liftQ Fc m M)).comp (eM Fc m M) = AdjoinRoot.of _ := by
    ext b
    change NFK.toAR _ (embM Fc m M b) = _
    rw [toAR_embM]; rfl
  have e2 : NFK.toARHom (liftQ Fc m M) (gammaM Fc m M) = AdjoinRoot.root _ := by
    change NFK.toAR _ (NFK.mk _ [0, 1]) = _
    rw [NFK.toAR_mk]; simp [CPoly.toPoly]
  change NFK.toARHom _ _ = NFK.toARHom _ a
  rw [h, e1, e2, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
  rfl

/-- The coordinate decomposition of an element of `Kₘ ⊗ N`. -/
lemma sum_coords (d : ℕ) (a : NFM Fc m M) (ha : a.1.length ≤ d) :
    ∑ f ∈ Finset.range d, eM Fc m M (a.1.getD f 0) * gammaM Fc m M ^ f = a := by
  rw [← eval₂_list_sum' (eM Fc m M) (gammaM Fc m M) a.1 d ha, eval₂_gammaM_self]

end Repr

end Curves.MT

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

lemma trC_pcP_T (m : ℕ) (hm : T.Tr m) (P : GPoly (LC m)) :
    trC Fc (m + 1) (pcP Fc ks m P) = (RFC.mk (P.map (trC Fc m)) [1] : RFC.RatFuncC (KF Fc m)) := by
  show RFC.mk (P.map (trC Fc m)) ([(MO Fc ks m).one].map (trC Fc m)) = _
  rw [List.map_singleton, T.trC_one_T m hm]

lemma length_le_NFM (m : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    (htrim : CPoly.trim M = M) (a : NFM Fc m M) : a.1.length ≤ M.length - 1 := by
  have hdeg := NFK.degree_val (liftQ Fc m M) a
  rw [toPoly_liftQ, degree_map] at hdeg
  have htr : CPoly.trim a.1 = a.1 := by
    have := a.2; rw [NFK.norm] at this; rw [← this, CPoly.trim_trim]
  by_cases hne : CPoly.trim a.1 = []
  · rw [htr] at hne; rw [hne]; simp
  · have hl := CPoly.length_trim hne
    rw [htr] at hl
    have hM0 : toPoly M ≠ 0 := fun h ↦ by rw [h, degree_zero] at hdeg; exact absurd hdeg (by simp)
    have hMne : CPoly.trim M ≠ [] := fun h ↦ hM0 ((CPoly.trim_eq_nil_iff M).mp h)
    have hMl := CPoly.length_trim hMne
    rw [htrim] at hMl
    have h0 : toPoly a.1 ≠ 0 := fun h ↦ hne ((CPoly.trim_eq_nil_iff _).mpr h)
    rw [degree_eq_natDegree h0, degree_eq_natDegree hM0] at hdeg
    have : (toPoly a.1).natDegree < (toPoly M).natDegree := by exact_mod_cast hdeg
    omega

/-- The coefficient codes of `kyColM`, read in `(Kₘ ⊗ N)(t)`. -/
lemma psiY_kyCoords (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (htrim : CPoly.trim M = M)
    (c : CPoly (NFM Fc m M)) :
    psiY Fc m M (NFK.mk _ ((kyCoords Fc ks m M (M.length - 1) c).map (trC Fc (m + 1)))) =
      algebraMap (NFM Fc m M)[X] (RK Fc m M) (toPoly c) := by
  set d := M.length - 1
  rw [psiY, liftNFM_mk, eval₂_list_sum' _ _ _ d (by simp [kyCoords])]
  have hterm : ∀ f ∈ Finset.range d,
      psiK0 Fc m M (((kyCoords Fc ks m M d c).map (trC Fc (m + 1))).getD f 0) *
        algebraMap (NFM Fc m M) (RK Fc m M) (gammaM Fc m M) ^ f =
      algebraMap (NFM Fc m M)[X] (RK Fc m M)
        ((toPoly (c.map fun a ↦ a.1.getD f 0)).map (eM Fc m M) * C (gammaM Fc m M ^ f)) := by
    intro f hf
    have hf' := Finset.mem_range.mp hf
    rw [List.getD_eq_getElem _ _ (by simp [kyCoords]; omega), List.getElem_map]
    simp only [kyCoords, List.getElem_map, List.getElem_range]
    rw [T.trC_pcP_T m hm, List.map_map]
    have : (trC Fc m ∘ unTr Fc m) = id := funext fun y ↦ T.trC_unTr_T m hm y
    rw [this, List.map_id, psiK0_poly, map_mul, ← map_pow, IsScalarTower.algebraMap_apply
      (NFM Fc m M) (NFM Fc m M)[X] (RK Fc m M), algebraMap_eq, C_pow]
  rw [Finset.sum_congr rfl hterm, ← map_sum]
  congr 1
  ext k
  rw [finsetSum_coeff]
  simp only [coeff_mul_C, coeff_map, coeff_toPoly]
  rw [← sum_coords Fc m M d (c.getD k 0) (length_le_NFM m M htrim _)]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  congr 2
  have h0 : ((0 : NFM Fc m M).1).getD f 0 = 0 := by
    have hz : (0 : NFM Fc m M).1 = [] := by
      have h1 : toPoly (0 : NFM Fc m M).1 = 0 := by
        have := NFK.toAR_zero (liftQ Fc m M)
        have h2 := NFK.degree_val (liftQ Fc m M) 0
        change AdjoinRoot.mk _ (toPoly (0 : NFM Fc m M).1) = 0 at this
        rw [AdjoinRoot.mk_eq_zero] at this
        exact eq_zero_of_dvd_of_degree_lt this h2
      have htr : CPoly.trim (0 : NFM Fc m M).1 = (0 : NFM Fc m M).1 := by
        have := (0 : NFM Fc m M).2; rw [NFK.norm] at this; rw [← this, CPoly.trim_trim]
      rw [← htr]; exact (CPoly.trim_eq_nil_iff _).mpr h1
    rw [hz]; rfl
  exact getD_map_zero (fun a : NFM Fc m M ↦ a.1.getD f 0) h0 c k

/-- **The witness and `Yⁿ − Â` are coprime over `K_{m+1} ⊗ N`.** -/
theorem ky_gcd_coprime (m n : ℕ) (hn : 1 < n) (hm : T.Tr m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (htrim : CPoly.trim M = M) (W : BPoly (NFM Fc m M)) (hW0 : toB W ≠ 0)
    (hWd : (toB W).natDegree < n) (Ah : GPoly (LC m))
    (hAsq : Squarefree ((toPoly (Ah.map (trC Fc m))).map (eM Fc m M)))
    (hAd : 0 < ((toPoly (Ah.map (trC Fc m))).map (eM Fc m M)).natDegree) :
    IsCoprime (toPoly ((W.map (kyCoords Fc ks m M (M.length - 1))).map fun cf ↦
        (NFK.mk _ (cf.map (trC Fc (m + 1))) : NFM Fc (m + 1) M)))
      (toPoly ((-(embM Fc (m + 1) M (trC Fc (m + 1) (pcP Fc ks m Ah)))) ::
        (List.replicate (n - 1) 0 ++ [1]))) := by
  have hn0 : 0 < n := by omega
  rw [← isCoprime_map (psiY Fc m M)]
  have hW : (toPoly ((W.map (kyCoords Fc ks m M (M.length - 1))).map fun cf ↦
        (NFK.mk _ (cf.map (trC Fc (m + 1))) : NFM Fc (m + 1) M))).map (psiY Fc m M) =
      (toB W).map (algebraMap (NFM Fc m M)[X] (RK Fc m M)) := by
    rw [← toPoly_map', List.map_map, List.map_map, ← toPoly_map_toB]
    congr 1
    exact List.map_congr_left fun c _ ↦ T.psiY_kyCoords m hm M htrim c
  have hM : (toPoly ((-(embM Fc (m + 1) M (trC Fc (m + 1) (pcP Fc ks m Ah)))) ::
      (List.replicate (n - 1) 0 ++ [1]))).map (psiY Fc m M) =
      (X ^ n - C ((toPoly (Ah.map (trC Fc m))).map (eM Fc m M)) : (NFM Fc m M)[X][X]).map
        (algebraMap (NFM Fc m M)[X] (RK Fc m M)) := by
    rw [toPoly_xnSubC _ n hn0, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_pow, map_X, map_X, map_C, map_C]
    congr 2
    rw [psiY, liftNFM_embM, T.trC_pcP_T m hm, psiK0_poly]
  rw [hW, hM]
  exact coprime_norm_abstract (RingHom.id (NFM Fc m M)) n hn0 _ hAsq hAd (toB W) [toB W]
    (by simp) (by simp [hW0, hWd])

end MTower

end Curves.MT
