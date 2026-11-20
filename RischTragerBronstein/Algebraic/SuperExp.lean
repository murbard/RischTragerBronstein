import RischTragerBronstein.Algebraic.SuperAbel

/-!
# General expansions of a superelliptic function field

`SuperData.embG g hg Y hY`: for an injective ring map `g : C[x] → K⸨s⸩` (the substitution of `x`)
and `Y` with `Yⁿ = g(p)`, the ring embedding `C⟮x⟯⟮y⟯ → K⸨s⸩` with `x ↦ g(x)`, `y ↦ Y`. The
non-branch expansions (`embXY`) are one instance; the expansions at the branch points
(`x = e + sⁿ`) and at infinity (`x = s⁻ⁿ`) are others. These only need to be ring maps: they are
used to compute orders.

`power_repr`: every element of `C⟮x⟯⟮y⟯` is `∑_{i<n} aᵢ yⁱ` with `aᵢ ∈ C⟮x⟯`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

section Sub

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma order_ofPS_unit (H : PowerSeries K) (hH : PowerSeries.constantCoeff H ≠ 0) :
    (ofPowerSeries ℤ K H).order = 0 := by
  have hc : (ofPowerSeries ℤ K H).coeff 0 ≠ 0 := by
    rw [LaurentSeries.coeff_ofPS, if_pos le_rfl]; simpa using hH
  have hne : ofPowerSeries ℤ K H ≠ 0 := fun h ↦ hc (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) (not_lt.mp fun hlt ↦ ?_)
  have := (not_congr HahnSeries.coeff_order_eq_zero).mpr hne
  rw [LaurentSeries.coeff_ofPS_neg _ hlt] at this
  exact this rfl

/-- The substitution `x ↦ e + sᵐ`. -/
noncomputable def branchSub (m : ℕ) (e : K) : C[X] →+* LaurentSeries K :=
  (ofPowerSeries ℤ K).comp ((Polynomial.coeToPowerSeries.ringHom (R := K)).comp
    ((Polynomial.compRingHom (Polynomial.C e + X ^ m)).comp
      (Polynomial.mapRingHom (algebraMap C K))))

lemma branchSub_apply (m : ℕ) (e : K) (P : C[X]) :
    branchSub m e P = ofPowerSeries ℤ K
      (((P.map (algebraMap C K)).comp (Polynomial.C e + X ^ m) : K[X]) : PowerSeries K) := rfl

/-- **The order of `P(e + sᵐ)`** is `m` times the multiplicity of `e`. -/
theorem order_branchSub (m : ℕ) (hm : 0 < m) (e : K) (P : C[X]) (hP : P ≠ 0) :
    (branchSub m e P).order = (m * (P.map (algebraMap C K)).rootMultiplicity e : ℕ) := by
  have hP' : P.map (algebraMap C K) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hP
  obtain ⟨Q, hPQ, hQ⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hP' e
  set k := (P.map (algebraMap C K)).rootMultiplicity e
  have hQe : Q.eval e ≠ 0 := fun h ↦ hQ (dvd_iff_isRoot.mpr h)
  have hcomp : (P.map (algebraMap C K)).comp (Polynomial.C e + X ^ m) =
      X ^ (m * k) * Q.comp (Polynomial.C e + X ^ m) := by
    rw [hPQ, mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_left, ← pow_mul]

  have hu : PowerSeries.constantCoeff ((Q.comp (Polynomial.C e + X ^ m) : K[X]) : PowerSeries K)
      ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_eq_eval_zero, eval_comp]
    simpa [zero_pow hm.ne'] using hQe
  rw [branchSub_apply, hcomp, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, map_mul,
    map_pow, ofPowerSeries_X, single_pow, one_pow]
  have hu0 : ofPowerSeries ℤ K ((Q.comp (Polynomial.C e + X ^ m) : K[X]) : PowerSeries K) ≠ 0 :=
    fun h ↦ by
      have := order_ofPS_unit _ hu
      have hc : (ofPowerSeries ℤ K ((Q.comp (Polynomial.C e + X ^ m) : K[X]) :
          PowerSeries K)).coeff 0 ≠ 0 := by
        rw [LaurentSeries.coeff_ofPS, if_pos le_rfl]; simpa using hu
      rw [h] at hc; exact hc rfl
  rw [HahnSeries.order_single_mul_of_isRegular isRegular_one hu0, order_ofPS_unit _ hu]
  simp

lemma branchSub_injective (m : ℕ) (hm : 0 < m) (e : K) :
    Function.Injective (branchSub (C := C) m e) := by
  refine (injective_iff_map_eq_zero _).mpr fun P hP ↦ ?_
  rw [branchSub_apply] at hP
  have h1 := HahnSeries.ofPowerSeries_injective (hP.trans (map_zero _).symm)
  have h2 : (P.map (algebraMap C K)).comp (Polynomial.C e + X ^ m) = 0 :=
    Polynomial.coe_injective K (by rw [h1, Polynomial.coe_zero])
  rw [comp_eq_zero_iff] at h2
  rcases h2 with h2 | ⟨-, h2⟩
  · exact (Polynomial.map_eq_zero_iff (algebraMap C K).injective).mp h2
  · exfalso
    have := congrArg natDegree h2
    rw [natDegree_C, natDegree_add_eq_right_of_natDegree_lt (by simp; omega), natDegree_X_pow] at this
    omega

lemma order_inv' (f : LaurentSeries K) (hf : f ≠ 0) : f⁻¹.order = -f.order := by
  have h := HahnSeries.order_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, HahnSeries.order_one] at h
  omega

lemma order_div' (f g : LaurentSeries K) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f / g).order = f.order - g.order := by
  rw [div_eq_mul_inv, HahnSeries.order_mul hf (inv_ne_zero hg), order_inv' g hg]; ring

lemma shiftHom_eq_branchSub (α : K) : shiftHom (C := C) α = branchSub 1 α := by
  refine RingHom.ext fun P ↦ ?_
  rw [shiftHom_apply, branchSub_apply, pow_one, add_comm]

/-- **No poles, hence a polynomial**: an element of `C⟮x⟯` without poles at any `α ∈ K`
(`K` algebraically closed) is a polynomial in `x`. -/
theorem exists_poly_of_regular {L : Type*} [Field L] [Algebra C L] [IsAlgClosed K] (x : L)
    (htr : Transcendental C x) (a : C⟮x⟯) (h : ∀ α : K, a ≠ 0 → 0 ≤ (embX x htr α a).order) :
    ∃ P : C[X], (a : L) = aeval x P := by
  classical
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple x htr
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, map_zero]; rfl⟩
  set Nu := IsFractionRing.num C[X] a
  set De := (IsFractionRing.den C[X] a : C[X])
  have hDe0 : De ≠ 0 := nonZeroDivisors.ne_zero (IsFractionRing.den C[X] a).2
  have hak : algebraMap C[X] C⟮x⟯ Nu / algebraMap C[X] C⟮x⟯ De = a :=
    IsFractionRing.mk'_num_den' C[X] a
  have hNu0 : Nu ≠ 0 := fun h0 ↦ ha (by rw [← hak, h0, map_zero, zero_div])
  have hcop : IsCoprime Nu De := (IsFractionRing.num_den_reduced C[X] a).isCoprime
  by_cases hdeg : De.natDegree = 0
  · obtain ⟨c, hc⟩ : ∃ c, De = Polynomial.C c := ⟨De.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩
    have hc0 : c ≠ 0 := fun h0 ↦ hDe0 (by rw [hc, h0, map_zero])
    refine ⟨Polynomial.C c⁻¹ * Nu, ?_⟩
    rw [← hak, IntermediateField.coe_div, algebraMap_adjoinSimple, algebraMap_adjoinSimple, hc,
      aeval_C, map_mul, aeval_C, map_inv₀]
    field_simp
  · exfalso
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (De.map (algebraMap C K)) (by
      rw [degree_map]; exact fun h0 ↦ hdeg (natDegree_eq_of_degree_eq_some h0))
    have hDm : De.map (algebraMap C K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hDe0
    have hNm : Nu.map (algebraMap C K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hNu0
    have hNα : ¬ (Nu.map (algebraMap C K)).IsRoot α := by
      intro hN
      obtain ⟨u, v, huv⟩ := hcop.map (Polynomial.mapRingHom (algebraMap C K))
      have := congrArg (eval α) huv
      simp only [coe_mapRingHom, eval_add, eval_mul, eval_one] at this
      rw [hN.eq_zero, hα.eq_zero, mul_zero, mul_zero, add_zero] at this
      exact zero_ne_one this
    have e1 : embX x htr α a = shiftHom α Nu / shiftHom α De := by
      rw [← hak, map_div₀]
      simp only [embX, IsFractionRing.lift_algebraMap]
    have hsN : shiftHom (C := C) α Nu ≠ 0 := fun h0 ↦ hNu0 (shiftHom_injective α
      (h0.trans (map_zero _).symm))
    have hsD : shiftHom (C := C) α De ≠ 0 := fun h0 ↦ hDe0 (shiftHom_injective α
      (h0.trans (map_zero _).symm))
    have hord := h α ha
    rw [e1, order_div' _ _ hsN hsD, shiftHom_eq_branchSub, order_branchSub 1 one_pos α Nu hNu0,
      order_branchSub 1 one_pos α De hDe0, rootMultiplicity_eq_zero hNα] at hord
    have : 0 < (De.map (algebraMap C K)).rootMultiplicity α :=
      (rootMultiplicity_pos hDm).mpr hα
    push_cast at hord
    omega

end Sub

namespace SuperData

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

variable (S : SuperData C L)

/-- The expansion of `C⟮x⟯` along an injective substitution `g`. -/
noncomputable def embXG (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) :
    C⟮S.x⟯ →+* LaurentSeries K :=
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  IsFractionRing.lift hg

lemma embXG_algebraMap (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (P : C[X]) :
    letI := algebraAdjoinSimple (F := C) S.x
    S.embXG g hg (algebraMap C[X] C⟮S.x⟯ P) = g P := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  rw [embXG, IsFractionRing.lift_algebraMap]

lemma rootG_eval (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : Y ^ S.n = g S.p) :
    (minpoly C⟮S.x⟯ S.y).eval₂ (S.embXG g hg) Y = 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [S.minpoly_eq, eval₂_sub, eval₂_X_pow, eval₂_C, S.embXG_algebraMap, hY, sub_self]

/-- **The expansion along `g`, with `y ↦ Y`.** -/
noncomputable def embG (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : Y ^ S.n = g S.p) : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K :=
  (AdjoinRoot.lift (S.embXG g hg) _ (S.rootG_eval g hg Y hY)).comp
    (adjoinRootEquivAdjoin C⟮S.x⟯ S.isIntegral).symm.toRingEquiv.toRingHom

lemma embG_gen (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : Y ^ S.n = g S.p) :
    S.embG g hg Y hY (AdjoinSimple.gen C⟮S.x⟯ S.y) = Y := by
  simp only [embG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.lift_root]

lemma embG_algebraMap (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : Y ^ S.n = g S.p) (a : C⟮S.x⟯) :
    S.embG g hg Y hY (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) = S.embXG g hg a := by
  simp only [embG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  exact AdjoinRoot.lift_of _

/-- **Power-basis representation**: `w = ∑_{i<n} aᵢ yⁱ` with `aᵢ ∈ C⟮x⟯`. -/
theorem power_repr (w : C⟮S.x⟯⟮S.y⟯) :
    ∃ a : Fin S.n → C⟮S.x⟯, w = ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) := by
  letI := algebraAdjoinSimple (F := C) S.x
  set pb := IntermediateField.adjoin.powerBasis S.isIntegral
  have hdim : pb.dim = S.n := by
    rw [IntermediateField.adjoin.powerBasis_dim, S.minpoly_eq, natDegree_X_pow_sub_C]
  have hgen : pb.gen = AdjoinSimple.gen C⟮S.x⟯ S.y := IntermediateField.adjoin.powerBasis_gen _
  have := pb.basis.sum_repr w
  refine ⟨fun i ↦ pb.basis.repr w ⟨i, by rw [hdim]; exact i.2⟩, ?_⟩
  conv_lhs => rw [← this]
  rw [← Equiv.sum_comp (finCongr hdim)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [PowerBasis.coe_basis, hgen, Algebra.smul_def]
  rfl

/-! ### Branch points -/

/-- `p(x + e) / x`. -/
noncomputable def pBranch (e : K) : K[X] := (taylor e (S.p.map (algebraMap C K))).divX

lemma taylor_eq_X_mul (e : K) (he : (S.p.map (algebraMap C K)).eval e = 0) :
    taylor e (S.p.map (algebraMap C K)) = X * S.pBranch e := by
  have h := X_mul_divX_add (taylor e (S.p.map (algebraMap C K)))
  rw [taylor_coeff_zero, he, map_zero, add_zero] at h
  exact h.symm

lemma pBranch_zero (e : K) :
    (S.pBranch e).coeff 0 = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e := by
  rw [pBranch, coeff_divX, zero_add, taylor_coeff_one]



/-- The unit `U(s)` with `Uⁿ = p₁(sⁿ)`, `U(0) = γ`. -/
noncomputable def branchU (e γ : K) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) : PowerSeries K :=
  Classical.choose (LaurentSeries.exists_pow_eq S.n S.hn (S.hnK K)
    (((S.pBranch e).comp (X ^ S.n) : K[X]) : PowerSeries K) γ hγ (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        coeff_zero_eq_eval_zero, eval_comp]
      simp [zero_pow S.hn.ne', ← coeff_zero_eq_eval_zero, pBranch_zero, hγp]))

lemma branchU_spec (e γ : K) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    S.branchU e γ hγ hγp ^ S.n = (((S.pBranch e).comp (X ^ S.n) : K[X]) : PowerSeries K) ∧
      PowerSeries.constantCoeff (S.branchU e γ hγ hγp) = γ :=
  Classical.choose_spec (LaurentSeries.exists_pow_eq S.n S.hn (S.hnK K)
    (((S.pBranch e).comp (X ^ S.n) : K[X]) : PowerSeries K) γ hγ (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        coeff_zero_eq_eval_zero, eval_comp]
      simp [zero_pow S.hn.ne', ← coeff_zero_eq_eval_zero, pBranch_zero, hγp]))

/-- The branch of `y` at `e`: `s · U(s)`. -/
noncomputable def branchYe (e γ : K) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    LaurentSeries K :=
  HahnSeries.single 1 1 * ofPowerSeries ℤ K (S.branchU e γ hγ hγp)

lemma branchYe_pow (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    S.branchYe e γ hγ hγp ^ S.n = branchSub S.n e S.p := by
  rw [branchYe, mul_pow, single_pow, one_pow, ← map_pow (ofPowerSeries ℤ K),
    (S.branchU_spec e γ hγ hγp).1, branchSub_apply]
  have e1 : (S.p.map (algebraMap C K)).comp (Polynomial.C e + X ^ S.n) =
      (taylor e (S.p.map (algebraMap C K))).comp (X ^ S.n) := by
    rw [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, add_comm]
  rw [e1, S.taylor_eq_X_mul e he, mul_comp, X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_X, map_mul, map_pow, ofPowerSeries_X, single_pow, one_pow]

lemma order_branchYe (e γ : K) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    (S.branchYe e γ hγ hγp).order = 1 := by
  have hu := (S.branchU_spec e γ hγ hγp).2
  have hu0 : ofPowerSeries ℤ K (S.branchU e γ hγ hγp) ≠ 0 := by
    intro h
    have := order_ofPS_unit _ (by rw [hu]; exact hγ)
    have hc : (ofPowerSeries ℤ K (S.branchU e γ hγ hγp)).coeff 0 ≠ 0 := by
      rw [LaurentSeries.coeff_ofPS, if_pos le_rfl]; simpa [hu] using hγ
    rw [h] at hc; exact hc rfl
  rw [branchYe, HahnSeries.order_single_mul_of_isRegular isRegular_one hu0,
    order_ofPS_unit _ (by rw [hu]; exact hγ), add_zero]

/-- **The expansion at the branch point `e`.** -/
noncomputable def embB (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K :=
  S.embG (branchSub S.n e) (branchSub_injective S.n S.hn e) (S.branchYe e γ hγ hγp)
    (S.branchYe_pow e γ he hγ hγp)

/-- The branch substitution scales orders of `C⟮x⟯` by `n`. -/
lemma embXG_branch_order (e : K) (a : C⟮S.x⟯) (ha : a ≠ 0) :
    (S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) a).order =
      S.n * (embX S.x S.htr e a).order := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  set Nu := IsFractionRing.num C[X] a
  set De := (IsFractionRing.den C[X] a : C[X])
  have hDe0 : De ≠ 0 := nonZeroDivisors.ne_zero (IsFractionRing.den C[X] a).2
  have hak : algebraMap C[X] C⟮S.x⟯ Nu / algebraMap C[X] C⟮S.x⟯ De = a :=
    IsFractionRing.mk'_num_den' C[X] a
  have hNu0 : Nu ≠ 0 := fun h0 ↦ ha (by rw [← hak, h0, map_zero, zero_div])
  have e1 : S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) a =
      branchSub S.n e Nu / branchSub S.n e De := by
    rw [← hak, map_div₀, S.embXG_algebraMap, S.embXG_algebraMap]
  have e2 : embX S.x S.htr e a = shiftHom e Nu / shiftHom e De := by
    rw [← hak, map_div₀]
    simp only [embX, IsFractionRing.lift_algebraMap]
  have hN : branchSub (C := C) S.n e Nu ≠ 0 := fun h0 ↦ hNu0 (branchSub_injective S.n S.hn e
    (h0.trans (map_zero _).symm))
  have hD : branchSub (C := C) S.n e De ≠ 0 := fun h0 ↦ hDe0 (branchSub_injective S.n S.hn e
    (h0.trans (map_zero _).symm))
  have hN1 : shiftHom (C := C) e Nu ≠ 0 := fun h0 ↦ hNu0 (shiftHom_injective e
    (h0.trans (map_zero _).symm))
  have hD1 : shiftHom (C := C) e De ≠ 0 := fun h0 ↦ hDe0 (shiftHom_injective e
    (h0.trans (map_zero _).symm))
  rw [e1, e2, order_div' _ _ hN hD, order_div' _ _ hN1 hD1, shiftHom_eq_branchSub,
    order_branchSub S.n S.hn e Nu hNu0, order_branchSub S.n S.hn e De hDe0,
    order_branchSub 1 one_pos e Nu hNu0, order_branchSub 1 one_pos e De hDe0]
  push_cast
  ring

/-- **Regularity at a branch point**: if the expansion of `∑ aᵢ yⁱ` at `e` has non-negative
order, every `aᵢ` is regular at `e`. -/
theorem branch_regular (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e)
    (a : Fin S.n → C⟮S.x⟯)
    (h : 0 ≤ (S.embB e γ he hγ hγp (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))).orderTop) :
    ∀ i, a i ≠ 0 → 0 ≤ (embX S.x S.htr e (a i)).order := by
  classical
  set φ := S.embB e γ he hγ hγp
  set t : Fin S.n → LaurentSeries K := fun i ↦
    S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) (a i) *
      S.branchYe e γ hγ hγp ^ (i : ℕ)
  have hφ : ∀ i, φ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) =
      t i := fun i ↦ by
    rw [map_mul, map_pow]
    simp only [φ, embB, S.embG_algebraMap, S.embG_gen, t]
  have hY0 : S.branchYe e γ hγ hγp ≠ 0 := fun h0 ↦ by
    have := S.order_branchYe e γ hγ hγp; rw [h0, HahnSeries.order_zero] at this; omega
  have hord : ∀ i, a i ≠ 0 → (t i).order = S.n * (embX S.x S.htr e (a i)).order + i := by
    intro i hi
    have hG : S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) (a i) ≠ 0 :=
      (map_ne_zero_iff _ (RingHom.injective _)).mpr hi
    simp only [t]
    rw [HahnSeries.order_mul hG (pow_ne_zero _ hY0), S.embXG_branch_order e (a i) hi,
      HahnSeries.order_pow, S.order_branchYe]
    simp
  set s := Finset.univ.filter fun i : Fin S.n ↦ a i ≠ 0
  have hsum : φ (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) =
      ∑ i ∈ s, t i := by
    rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ a i ≠ 0)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i ↦ ¬ a i ≠ 0) fun i hi ↦ by
      rw [Finset.mem_filter, not_not] at hi; rw [hφ, show t i = 0 by simp [t, hi.2]], add_zero]
    exact Finset.sum_congr rfl fun i _ ↦ hφ i
  have hne : ∀ i ∈ s, t i ≠ 0 := fun i hi ↦ by
    have hi' : a i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact mul_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr hi') (pow_ne_zero _ hY0)
  have hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (t i).orderTop ≠ (t j).orderTop := by
    intro i hi j hj hij heq
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero (hne i hi),
      ← HahnSeries.order_eq_orderTop_of_ne_zero (hne j hj),
      WithTop.coe_eq_coe, hord i (Finset.mem_filter.mp hi).2, hord j (Finset.mem_filter.mp hj).2]
      at heq
    have hi2 := i.2
    have hj2 := j.2
    have : (i : ℤ) % S.n = (j : ℤ) % S.n := by
      have := congrArg (fun z : ℤ ↦ z % S.n) heq
      simpa [Int.add_mul_emod_self_left] using this
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi2),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj2)] at this
    exact hij (Fin.ext (by exact_mod_cast this))
  rw [hsum] at h
  intro i hi
  have hts := LaurentSeries.le_orderTop_of_sum_distinct s t hd 0 h i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (hne i (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hi⟩)), hord i hi] at hts
  have h0 : (0 : ℤ) ≤ S.n * (embX S.x S.htr e (a i)).order + i := by exact_mod_cast hts
  have hi2 := i.2
  by_contra hneg
  push_neg at hneg
  have : S.n * (embX S.x S.htr e (a i)).order ≤ -(S.n : ℤ) := by nlinarith
  omega

end SuperData

end Differential
