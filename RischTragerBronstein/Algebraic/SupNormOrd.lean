import RischTragerBronstein.Algebraic.SupNorm
import RischTragerBronstein.Algebraic.SuperPrincipalSem
import RischTragerBronstein.Algebraic.SuperOrd

/-!
# The resultant norm and the orders on the curve

For `S : SuperData C L`, `ψ ∈ C[X][X]` of degree `< n` in `y` and an algebraically closed `K ⊇ C`
containing a primitive `n`-th root of unity `ζ`, the expansion of `N = resN p n ψ` at an ordinary
point is the product of the expansions of `elemW ψ` at the `n` points above it
(`shiftHom_resN`); hence `mult_α N = ∑ₖ ord_{(α, ζᵏβ)} ψ` (`rootMult_resN`).
No assumption on the characteristic (only `n` invertible).
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

open Sup

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K]

variable (S : SuperData C L)

/-- The coefficient map `C → K⸨s⸩`. -/
noncomputable abbrev cφ (C K : Type*) [Field C] [Field K] [Algebra C K] : C →+* LaurentSeries K :=
  (HahnSeries.C).comp (algebraMap C K)

omit [PerfectField C] in
lemma shiftHom_eq_eval (α : K) (P : C[X]) :
    shiftHom (C := C) α P = (P.map (cφ C K)).eval (shiftX α) := by
  have h : shiftHom (C := C) α = (evalRingHom (shiftX α)).comp (mapRingHom (cφ C K)) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp [shiftHom_C]
    · simp [shiftHom_X]
  exact congrArg (fun φ : C[X] →+* LaurentSeries K ↦ φ P) h

omit [PerfectField C] in
lemma evalW_map_eq (ψ : C[X][X]) (hψ : ψ.natDegree < S.n) (α : K) (Y : LaurentSeries K) :
    evalW (ψ.map (mapRingHom (cφ C K))) (shiftX α) Y =
      ∑ j ∈ Finset.range S.n, shiftHom α (ψ.coeff j) * Y ^ j := by
  rw [evalW, eval_map, eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hψ)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coeff_map, coe_mapRingHom, coe_evalRingHom, ← shiftHom_eq_eval]

omit [PerfectField C] in
/-- The branch at `(α, ζᵏβ)` is `ζᵏ` times the branch at `(α, β)`. -/
lemma branchY_root (ζ : K) (hζ : ζ ^ S.n = 1) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (k : ℕ)
    (hβk : ζ ^ k * β ≠ 0) (hβpk : (ζ ^ k * β) ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    branchY S.n S.hn (S.hnK K) S.p α (ζ ^ k * β) hβk hβpk =
      PowerSeries.C (ζ ^ k) * branchY S.n S.hn (S.hnK K) S.p α β hβ hβp := by
  refine LaurentSeries.pow_eq_pow_unique S.n S.hn (S.hnK K) ?_ ?_ ?_
  · rw [mul_pow, ← map_pow, ← pow_mul, mul_comm k, pow_mul, hζ, one_pow, map_one, one_mul,
      branchY_pow, branchY_pow]
  · rw [map_mul, PowerSeries.constantCoeff_C, branchY_const, branchY_const]
  · rw [map_mul, PowerSeries.constantCoeff_C, branchY_const]; exact hβk

variable [IsAlgClosed K]

/-- **The expansion of the norm is the product of the expansions above.** -/
theorem shiftHom_resN (ζ : K) (hζ : IsPrimitiveRoot ζ S.n) (ψ : C[X][X])
    (hψ : ψ.natDegree < S.n) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    shiftHom α (resN S.p S.n ψ) = ∏ k ∈ Finset.range S.n,
      S.embXY α (ζ ^ k * β) (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero S.hn.ne')) hβ)
        (by rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hβp])
        (S.elemW ψ) := by
  set φ := cφ C K
  set Y := ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp)
  have hY : Y ^ S.n = (S.p.map φ).eval (shiftX α) := by
    rw [← shiftHom_eq_eval, ← map_pow, branchY_pow]; rfl
  have hζL : IsPrimitiveRoot (HahnSeries.C ζ : LaurentSeries K) S.n :=
    hζ.map_of_injective HahnSeries.C_injective
  rw [shiftHom_eq_eval, resN_map, resN_eval (S.p.map φ) S.hn hζL _
    (Nat.le_sub_one_of_lt (lt_of_le_of_lt natDegree_map_le hψ)) (shiftX α) Y hY]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [evalW_map_eq S ψ hψ, elemW, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_pow, S.embXY_polyX, ← shiftHom_apply, S.embXY_gen,
    S.branchY_root ζ hζ.pow_eq_one α β hβ hβp k, map_mul, ofPowerSeries_C, map_pow]

omit [PerfectField C] [IsAlgClosed K] in
lemma embG_elemW (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (Y : LaurentSeries K)
    (hY : Y ^ S.n = g S.p) (ψ : C[X][X]) :
    S.embG g hg Y hY (S.elemW ψ) = ∑ j ∈ Finset.range S.n, g (ψ.coeff j) * Y ^ j := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [elemW, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_pow, polyX, S.embG_algebraMap, S.embXG_algebraMap, S.embG_gen]

omit [PerfectField C] [IsAlgClosed K] in
/-- **The norm under any substitution** `x ↦ Z` with branch `Y`. -/
theorem subst_resN (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (Z : LaurentSeries K)
    (hgZ : ∀ P, g P = (P.map (cφ C K)).eval Z) (ζ : K) (hζ : IsPrimitiveRoot ζ S.n)
    (ψ : C[X][X]) (hψ : ψ.natDegree < S.n) (Y : LaurentSeries K) (hY : Y ^ S.n = g S.p) :
    g (resN S.p S.n ψ) = ∏ k ∈ Finset.range S.n, S.embG g hg (HahnSeries.C (ζ ^ k) * Y)
      (by rw [mul_pow, ← map_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, map_one,
        one_mul, hY]) (S.elemW ψ) := by
  have hζL : IsPrimitiveRoot (HahnSeries.C ζ : LaurentSeries K) S.n :=
    hζ.map_of_injective HahnSeries.C_injective
  rw [hgZ, resN_map, resN_eval (S.p.map (cφ C K)) S.hn hζL _
    (Nat.le_sub_one_of_lt (lt_of_le_of_lt natDegree_map_le hψ)) Z Y (by rw [hY, hgZ])]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [S.embG_elemW, evalW, eval_map, eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hψ)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coeff_map, coe_mapRingHom, coe_evalRingHom, ← hgZ, map_pow]

omit [PerfectField C] [IsAlgClosed K] in
lemma branchSub_eq_eval (m : ℕ) (e : K) (P : C[X]) :
    branchSub m e P = (P.map (cφ C K)).eval (HahnSeries.C e + single (m : ℤ) 1) := by
  have h : branchSub (C := C) m e = (evalRingHom (HahnSeries.C e + single (m : ℤ) 1)).comp
      (mapRingHom (cφ C K)) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp [branchSub_apply, ofPowerSeries_C]
    · simp only [branchSub_apply, Polynomial.map_X, X_comp, Polynomial.coe_add, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X, map_add, ofPowerSeries_C, ofPowerSeries_X_pow,
        RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_evalRingHom, eval_X]
  exact congrArg (fun φ : C[X] →+* LaurentSeries K ↦ φ P) h

omit [PerfectField C] [IsAlgClosed K] in
lemma infSub_eq_eval (m : ℕ) (P : C[X]) :
    infSub (C := C) (K := K) m P = (P.map (cφ C K)).eval (single (-(m : ℤ)) 1) := by
  simp only [infSub, coe_eval₂RingHom, eval_map]

/-- **Multiplicity of the norm at an ordinary abscissa.** -/
theorem rootMult_resN (ζ : K) (hζ : IsPrimitiveRoot ζ S.n) (ψ : C[X][X]) (hψ : ψ.natDegree < S.n)
    (hψ0 : S.elemW ψ ≠ 0) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (((resN S.p S.n ψ).map (algebraMap C K)).rootMultiplicity α : ℤ) =
      ∑ k ∈ Finset.range S.n, S.ordAt K (S.elemW ψ) α (ζ ^ k * β) := by
  have h := S.shiftHom_resN ζ hζ ψ hψ α β hβ hβp
  have hne : ∀ k ∈ Finset.range S.n, S.embXY α (ζ ^ k * β)
      (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero S.hn.ne')) hβ)
      (by rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hβp])
      (S.elemW ψ) ≠ 0 := fun k _ ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr hψ0
  have hN0 : resN S.p S.n ψ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact (Finset.prod_ne_zero_iff.mpr hne) h.symm
  have hord := congrArg HahnSeries.order h
  have hprod := order_hom_prod (RingHom.id (LaurentSeries K)) (Finset.range S.n) _ hne
  simp only [RingHom.id_apply] at hprod
  rw [shiftHom_eq_branchSub, order_branchSub 1 one_pos α _ hN0, one_mul, hprod] at hord
  rw [hord]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [S.ordAt_nb]

/-- **Multiplicity of the norm at a branch abscissa.** -/
theorem rootMult_resN_branch (ζ : K) (hζ : IsPrimitiveRoot ζ S.n) (ψ : C[X][X])
    (hψ : ψ.natDegree < S.n) (hψ0 : S.elemW ψ ≠ 0) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) :
    (((resN S.p S.n ψ).map (algebraMap C K)).rootMultiplicity e : ℤ) = S.ordAt K (S.elemW ψ) e 0 := by
  obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma e he
  set Y := S.branchYe e γ hγ hγp
  have hY := S.branchYe_pow e γ he hγ hγp
  have h := S.subst_resN (branchSub S.n e) (branchSub_injective S.n S.hn e) _
    (branchSub_eq_eval S.n e) ζ hζ ψ hψ Y hY
  have hY0 := S.branchYe_ne_zero e γ hγ hγp
  have hζk : ∀ k : ℕ, HahnSeries.C (ζ ^ k) * Y ≠ 0 := fun k ↦
    mul_ne_zero (fun h0 ↦ pow_ne_zero k (hζ.ne_zero S.hn.ne') (HahnSeries.C_injective
      (h0.trans (map_zero _).symm))) hY0
  have hordk : ∀ k : ℕ, (HahnSeries.C (ζ ^ k) * Y).order = Y.order := fun k ↦ by
    rw [HahnSeries.order_mul (fun h0 ↦ pow_ne_zero k (hζ.ne_zero S.hn.ne') (HahnSeries.C_injective
      (h0.trans (map_zero _).symm))) hY0, HahnSeries.order_C, zero_add]
  have hfac : ∀ k ∈ Finset.range S.n, (S.embG (branchSub S.n e) (branchSub_injective S.n S.hn e)
      (HahnSeries.C (ζ ^ k) * Y) (by rw [mul_pow, ← map_pow, ← pow_mul, mul_comm k, pow_mul,
        hζ.pow_eq_one, one_pow, map_one, one_mul, hY]) (S.elemW ψ)).order =
      S.ordAt K (S.elemW ψ) e 0 := fun k _ ↦ by
    rw [S.ordAt_br _ e γ he hγ hγp]
    unfold embB
    exact order_eq_of_orderTop_eq (S.orderTop_embG_indep _ _ _ _ _ _ (S.branch_hmod e) hY0 (hζk k)
      (by rw [S.order_branchYe]; exact isCoprime_one_left) (hordk k) _)
  have hne : ∀ k ∈ Finset.range S.n, S.embG (branchSub S.n e) (branchSub_injective S.n S.hn e)
      (HahnSeries.C (ζ ^ k) * Y) (by rw [mul_pow, ← map_pow, ← pow_mul, mul_comm k, pow_mul,
        hζ.pow_eq_one, one_pow, map_one, one_mul, hY]) (S.elemW ψ) ≠ 0 := fun k _ ↦
    (map_ne_zero_iff _ (RingHom.injective _)).mpr hψ0
  have hN0 : resN S.p S.n ψ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact (Finset.prod_ne_zero_iff.mpr hne) h.symm
  have hord := congrArg HahnSeries.order h
  have hprod := order_hom_prod (RingHom.id (LaurentSeries K)) (Finset.range S.n) _ hne
  simp only [RingHom.id_apply] at hprod
  rw [order_branchSub S.n S.hn e _ hN0, hprod, Finset.sum_congr rfl hfac, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hord
  have hn0 : (S.n : ℤ) ≠ 0 := by exact_mod_cast S.hn.ne'
  push_cast at hord
  exact mul_left_cancel₀ hn0 hord

/-- **The degree of the norm is the pole order at infinity.** -/
theorem natDegree_resN (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : K) (hζ : IsPrimitiveRoot ζ S.n)
    (ψ : C[X][X]) (hψ : ψ.natDegree < S.n) (hψ0 : S.elemW ψ ≠ 0) :
    ((resN S.p S.n ψ).natDegree : ℤ) = -S.ordInf K (S.elemW ψ) := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  set Y := S.infY lam hlam hlp
  have hY := S.infY_pow lam hlam hlp
  have h := S.subst_resN (infSub S.n) (infSub_injective S.n S.hn) _ (infSub_eq_eval S.n) ζ hζ ψ hψ
    Y hY
  have hY0 := S.infY_ne_zero lam hlam hlp
  have hζk : ∀ k : ℕ, HahnSeries.C (ζ ^ k) * Y ≠ 0 := fun k ↦
    mul_ne_zero (fun h0 ↦ pow_ne_zero k (hζ.ne_zero S.hn.ne') (HahnSeries.C_injective
      (h0.trans (map_zero _).symm))) hY0
  have hordk : ∀ k : ℕ, (HahnSeries.C (ζ ^ k) * Y).order = Y.order := fun k ↦ by
    rw [HahnSeries.order_mul (fun h0 ↦ pow_ne_zero k (hζ.ne_zero S.hn.ne') (HahnSeries.C_injective
      (h0.trans (map_zero _).symm))) hY0, HahnSeries.order_C, zero_add]
  have hfac : ∀ k ∈ Finset.range S.n, (S.embG (infSub S.n) (infSub_injective S.n S.hn)
      (HahnSeries.C (ζ ^ k) * Y) (by rw [mul_pow, ← map_pow, ← pow_mul, mul_comm k, pow_mul,
        hζ.pow_eq_one, one_pow, map_one, one_mul, hY]) (S.elemW ψ)).order =
      S.ordInf K (S.elemW ψ) := fun k _ ↦ by
    rw [S.ordInf_eq hcop _ lam hlam hlp]
    unfold embI
    exact order_eq_of_orderTop_eq (S.orderTop_embG_indep _ _ _ _ _ _ S.embXG_inf_order hY0 (hζk k)
      (S.isCoprime_infY hcop lam hlam hlp) (hordk k) _)
  have hne : ∀ k ∈ Finset.range S.n, S.embG (infSub S.n) (infSub_injective S.n S.hn)
      (HahnSeries.C (ζ ^ k) * Y) (by rw [mul_pow, ← map_pow, ← pow_mul, mul_comm k, pow_mul,
        hζ.pow_eq_one, one_pow, map_one, one_mul, hY]) (S.elemW ψ) ≠ 0 := fun k _ ↦
    (map_ne_zero_iff _ (RingHom.injective _)).mpr hψ0
  have hN0 : resN S.p S.n ψ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact (Finset.prod_ne_zero_iff.mpr hne) h.symm
  have hord := congrArg HahnSeries.order h
  have hprod := order_hom_prod (RingHom.id (LaurentSeries K)) (Finset.range S.n) _ hne
  simp only [RingHom.id_apply] at hprod
  rw [order_infSub S.n S.hn _ hN0, hprod, Finset.sum_congr rfl hfac, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hord
  have hn0 : (S.n : ℤ) ≠ 0 := by exact_mod_cast S.hn.ne'
  have : (S.n : ℤ) * (resN S.p S.n ψ).natDegree = S.n * (-S.ordInf K (S.elemW ψ)) := by
    linarith
  exact mul_left_cancel₀ hn0 this

end SuperData

end Differential
