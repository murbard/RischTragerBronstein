import RischTragerBronstein.Algebraic.SuperNorm
import Mathlib.Algebra.BigOperators.WithTop

/-!
# Orders at the places of a superelliptic curve, and the degree theorem

Over an algebraically closed `K ⊇ C`, the finite places of `yⁿ = p(x)` are the points `(α, β)`
with `βⁿ = p(α)` (`β = 0` exactly at the branch points), and there is one place at infinity when
`gcd(n, deg p) = 1`.

* `ordAt w α β`, `ordInf w`: the orders of `w` at these places;
* `ordAt_branch`: at a branch point the order does not depend on the chosen expansion;
* norm relations: `ord_α N(w) = ∑_{β} ord_{(α,β)} w`, `ord_∞ N(w) = n ord_∞ w`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K]

variable (S : SuperData C L)

lemma order_eq_of_orderTop_eq {f g : LaurentSeries K} (h : f.orderTop = g.orderTop) :
    f.order = g.order := by
  by_cases hf : f = 0
  · have hg : g = 0 := by
      rw [hf, HahnSeries.orderTop_zero] at h
      exact HahnSeries.orderTop_eq_top.mp h.symm
    rw [hf, hg]
  · have hg : g ≠ 0 := fun hg ↦ hf (by
      rw [hg, HahnSeries.orderTop_zero] at h
      exact HahnSeries.orderTop_eq_top.mp h)
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hf, ← HahnSeries.order_eq_orderTop_of_ne_zero hg]
      at h
    exact WithTop.coe_injective h

/-- **Independence of the branch**: two graded expansions along the same substitution whose
`y`-images have the same order give the same orders. -/
theorem orderTop_embG_indep (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y Y' : LaurentSeries K) (hY : Y ^ S.n = g S.p) (hY' : Y' ^ S.n = g S.p)
    (hmod : ∀ a : C⟮S.x⟯, a ≠ 0 → ∃ k : ℤ, (S.embXG g hg a).order = S.n * k) (hY0 : Y ≠ 0)
    (hY0' : Y' ≠ 0) (hr : IsCoprime Y.order (S.n : ℤ)) (hord : Y'.order = Y.order)
    (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embG g hg Y' hY' w).orderTop = (S.embG g hg Y hY w).orderTop := by
  classical
  obtain ⟨a, rfl⟩ := S.power_repr w
  set t : Fin S.n → LaurentSeries K := fun i ↦ S.embXG g hg (a i) * Y ^ (i : ℕ)
  set t' : Fin S.n → LaurentSeries K := fun i ↦ S.embXG g hg (a i) * Y' ^ (i : ℕ)
  have e1 : ∀ (Z : LaurentSeries K) (hZ : Z ^ S.n = g S.p), S.embG g hg Z hZ
      (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) =
      ∑ i, S.embXG g hg (a i) * Z ^ (i : ℕ) := fun Z hZ ↦ by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, S.embG_algebraMap, S.embG_gen]
  rw [e1 Y hY, e1 Y' hY']
  change (∑ i, t' i).orderTop = (∑ i, t i).orderTop
  set s := Finset.univ.filter fun i : Fin S.n ↦ a i ≠ 0
  have hsplit : ∀ u : Fin S.n → LaurentSeries K, (∀ i : Fin S.n, a i = 0 → u i = 0) →
      ∑ i, u i = ∑ i ∈ s, u i := fun u hu ↦ by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ a i ≠ 0),
      Finset.sum_eq_zero (s := Finset.univ.filter fun i ↦ ¬ a i ≠ 0) (fun i hi ↦ hu i
        (not_not.mp (Finset.mem_filter.mp hi).2)), add_zero]
  rw [hsplit t (fun i hi ↦ by simp [t, hi]), hsplit t' (fun i hi ↦ by simp [t', hi])]
  refine LaurentSeries.orderTop_sum_congr s t t' (fun i hi ↦ ?_)
    (S.embG_terms_distinct g hg Y hmod hY0 hr a s (fun i hi ↦ (Finset.mem_filter.mp hi).2))
  have hG : S.embXG g hg (a i) ≠ 0 :=
    (map_ne_zero_iff _ (RingHom.injective _)).mpr (Finset.mem_filter.mp hi).2
  simp only [t, t']
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero hG (pow_ne_zero _ hY0')),
    ← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero hG (pow_ne_zero _ hY0)),
    HahnSeries.order_mul hG (pow_ne_zero _ hY0'), HahnSeries.order_mul hG (pow_ne_zero _ hY0),
    HahnSeries.order_pow, HahnSeries.order_pow, hord]

/-! ### The branch and infinity substitutions are graded -/

lemma branchSub_C (m : ℕ) (e : K) (c : C) :
    branchSub m e (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [branchSub_apply, Polynomial.map_C, C_comp, Polynomial.coe_C, ofPowerSeries_C]

lemma infSub_C (m : ℕ) (c : C) :
    infSub (K := K) m (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [infSub, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]

lemma branchYe_ne_zero (e γ : K) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    S.branchYe e γ hγ hγp ≠ 0 := fun h0 ↦ by
  have := S.order_branchYe e γ hγ hγp
  rw [h0, HahnSeries.order_zero] at this
  exact zero_ne_one this

lemma infY_ne_zero (lam : K) (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    S.infY lam hlam hlp ≠ 0 := fun h0 ↦ by
  have := S.order_infY lam hlam hlp
  rw [h0, HahnSeries.order_zero] at this
  have := S.hp; omega

lemma branch_hmod (e : K) (a : C⟮S.x⟯) (ha : a ≠ 0) :
    ∃ k : ℤ, (S.embXG (branchSub (K := K) S.n e) (branchSub_injective S.n S.hn e) a).order =
      S.n * k :=
  ⟨_, S.embXG_branch_order e a ha⟩

lemma isCoprime_infY (hcop : Nat.Coprime S.n S.p.natDegree) (lam : K) (hlam : lam ≠ 0)
    (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    IsCoprime (S.infY lam hlam hlp).order (S.n : ℤ) := by
  rw [S.order_infY, IsCoprime.neg_left_iff]
  exact (Nat.isCoprime_iff_coprime.mpr hcop).symm

/-- Branch-point orders do not depend on the chosen `γ`. -/
lemma orderTop_embB_indep (e γ γ' : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) (hγ' : γ' ≠ 0)
    (hγp' : γ' ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e)
    (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embB e γ' he hγ' hγp' w).orderTop = (S.embB e γ he hγ hγp w).orderTop :=
  S.orderTop_embG_indep _ _ _ _ _ _ (S.branch_hmod e) (S.branchYe_ne_zero e γ hγ hγp)
    (S.branchYe_ne_zero e γ' hγ' hγp') (by rw [S.order_branchYe]; exact isCoprime_one_left)
    (by rw [S.order_branchYe, S.order_branchYe]) w

/-- Infinity orders do not depend on the chosen `λ`. -/
lemma orderTop_embI_indep (hcop : Nat.Coprime S.n S.p.natDegree) (lam lam' : K) (hlam : lam ≠ 0)
    (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) (hlam' : lam' ≠ 0)
    (hlp' : lam' ^ S.n = algebraMap C K S.p.leadingCoeff) (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embI lam' hlam' hlp' w).orderTop = (S.embI lam hlam hlp w).orderTop :=
  S.orderTop_embG_indep _ _ _ _ _ _ (S.embXG_inf_order) (S.infY_ne_zero lam hlam hlp)
    (S.infY_ne_zero lam' hlam' hlp') (S.isCoprime_infY hcop lam hlam hlp)
    (by rw [S.order_infY, S.order_infY]) w

/-! ### Norm relations -/

lemma orderTop_embB_normS (ζ : C) (hζ : ζ ^ S.n = 1) (e γ : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e)
    (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embB e γ he hγ hγp (S.normS ζ hζ w)).orderTop =
      S.n • (S.embB e γ he hγ hγp w).orderTop :=
  S.orderTop_embG_normS _ _ _ _ (branchSub_C S.n e) (S.branch_hmod e)
    (S.branchYe_ne_zero e γ hγ hγp) (by rw [S.order_branchYe]; exact isCoprime_one_left) ζ hζ w

lemma orderTop_embI_normS (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : ζ ^ S.n = 1)
    (lam : K) (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff)
    (w : C⟮S.x⟯⟮S.y⟯) :
    (S.embI lam hlam hlp (S.normS ζ hζ w)).orderTop = S.n • (S.embI lam hlam hlp w).orderTop :=
  S.orderTop_embG_normS _ _ _ _ (infSub_C S.n) (S.embXG_inf_order)
    (S.infY_ne_zero lam hlam hlp) (S.isCoprime_infY hcop lam hlam hlp) ζ hζ w

/-! ### Canonical orders over an algebraically closed field -/

section Closed

variable [IsAlgClosed K]

lemma exists_gamma (e : K) (he : (S.p.map (algebraMap C K)).eval e = 0) :
    ∃ γ : K, γ ≠ 0 ∧ γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e := by
  have hsep : S.p.Separable := PerfectField.separable_iff_squarefree.mpr S.hsq
  have hd : (Polynomial.derivative (S.p.map (algebraMap C K))).eval e ≠ 0 := by
    rw [derivative_map, eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (by rwa [← eval_map_algebraMap])
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq
    ((Polynomial.derivative (S.p.map (algebraMap C K))).eval e) S.hn
  exact ⟨γ, fun h0 ↦ hd (by rw [← hγ, h0, zero_pow S.hn.ne']), hγ⟩

lemma exists_lam : ∃ lam : K, lam ≠ 0 ∧ lam ^ S.n = algebraMap C K S.p.leadingCoeff := by
  obtain ⟨lam, hl⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap C K S.p.leadingCoeff) S.hn
  refine ⟨lam, fun h0 ↦ ?_, hl⟩
  rw [h0, zero_pow S.hn.ne', eq_comm, map_eq_zero_iff _ (algebraMap C K).injective,
    Polynomial.leadingCoeff_eq_zero] at hl
  exact S.hsq.ne_zero hl

lemma exists_beta (α : K) : ∃ β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α :=
  IsAlgClosed.exists_pow_nat_eq _ S.hn

open Classical in
/-- The order of `w` at the point `(α, β)` of `yⁿ = p(x)` (junk `0` off the curve). -/
noncomputable def ordAt (K : Type*) [Field K] [Algebra C K] [IsAlgClosed K]
    (w : C⟮S.x⟯⟮S.y⟯) (α β : K) : ℤ :=
  if h : β ≠ 0 ∧ β ^ S.n = (S.p.map (algebraMap C K)).eval α then
    (S.embXY α β h.1 h.2 w).order
  else if he : (S.p.map (algebraMap C K)).eval α = 0 then
    (S.embB α (Classical.choose (S.exists_gamma α he)) he
      (Classical.choose_spec (S.exists_gamma α he)).1
      (Classical.choose_spec (S.exists_gamma α he)).2 w).order
  else 0

/-- The order of `w` at infinity. -/
noncomputable def ordInf (K : Type*) [Field K] [Algebra C K] [IsAlgClosed K]
    (w : C⟮S.x⟯⟮S.y⟯) : ℤ :=
  (S.embI (Classical.choose (S.exists_lam (K := K))) (Classical.choose_spec S.exists_lam).1
    (Classical.choose_spec S.exists_lam).2 w).order

lemma ordAt_nb (w : C⟮S.x⟯⟮S.y⟯) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K w α β = (S.embXY α β hβ hβp w).order := by
  rw [ordAt, dif_pos ⟨hβ, hβp⟩]

lemma ordAt_br (w : C⟮S.x⟯⟮S.y⟯) (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0)
    (hγ : γ ≠ 0) (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    S.ordAt K w e 0 = (S.embB e γ he hγ hγp w).order := by
  rw [ordAt, dif_neg (fun h ↦ h.1 rfl), dif_pos he]
  exact order_eq_of_orderTop_eq (S.orderTop_embB_indep e γ _ he hγ hγp _ _ w)

lemma ordInf_eq (hcop : Nat.Coprime S.n S.p.natDegree) (w : C⟮S.x⟯⟮S.y⟯) (lam : K)
    (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    S.ordInf K w = (S.embI lam hlam hlp w).order :=
  order_eq_of_orderTop_eq (S.orderTop_embI_indep hcop lam _ hlam hlp _ _ w)

lemma embXY_ne_zero (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    {w : C⟮S.x⟯⟮S.y⟯} (hw : w ≠ 0) : S.embXY α β hβ hβp w ≠ 0 :=
  (map_ne_zero_iff _ (RingHom.injective _)).mpr hw

/-- Norm relation at a non-branch point. -/
theorem order_norm_nb (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (a : C⟮S.x⟯) (ha : S.normS ζ hζ.pow_eq_one w = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) (α β : K)
    (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (embX S.x S.htr α a).order =
      ∑ j ∈ Finset.range S.n, S.ordAt K w α (algebraMap C K (ζ ^ j) * β) := by
  have h := S.orderTop_embXY_normS ζ hζ.pow_eq_one α β hβ hβp w
  rw [ha, S.embXY_algebraMap] at h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, normS] at ha
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp ha
    exact hw ((map_eq_zero_iff _ (RingHom.injective _)).mp hj)
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr ha0)]
    at h
  rw [Finset.sum_congr rfl fun j _ ↦ (HahnSeries.order_eq_orderTop_of_ne_zero
    (S.embXY_ne_zero _ _ _ _ hw)).symm, ← WithTop.coe_sum] at h
  rw [WithTop.coe_injective h]
  refine Finset.sum_congr rfl fun j _ ↦ (S.ordAt_nb w α _ _ _).symm

lemma normS_ne_zero (ζ : C) (hζ : ζ ^ S.n = 1) {w : C⟮S.x⟯⟮S.y⟯} (hw : w ≠ 0) :
    S.normS ζ hζ w ≠ 0 := by
  rw [normS]
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr hw

/-- Norm relation at a branch point. -/
theorem order_norm_br (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (a : C⟮S.x⟯) (ha : S.normS ζ hζ.pow_eq_one w = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) :
    (embX S.x S.htr e a).order = S.ordAt K w e 0 := by
  obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma e he
  have h := S.orderTop_embB_normS ζ hζ.pow_eq_one e γ he hγ hγp w
  have ha0 : a ≠ 0 := fun h0 ↦ S.normS_ne_zero ζ hζ.pow_eq_one hw (by rw [ha, h0, map_zero])
  rw [ha] at h
  have e1 : S.embB e γ he hγ hγp (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) =
      S.embXG (branchSub S.n e) (branchSub_injective S.n S.hn e) a := S.embG_algebraMap _ _ _ _ a
  rw [e1, ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
    ha0), ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
    hw), S.embXG_branch_order e a ha0, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at h
  rw [S.ordAt_br w e γ he hγ hγp]
  have hn : (S.n : ℤ) ≠ 0 := by exact_mod_cast S.hn.ne'
  exact mul_left_cancel₀ hn h

/-- Norm relation at infinity. -/
theorem order_norm_inf (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0) (a : C⟮S.x⟯)
    (ha : S.normS ζ hζ.pow_eq_one w = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) :
    (S.embXG (infSub (K := K) S.n) (infSub_injective S.n S.hn) a).order = S.n * S.ordInf K w := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have h := S.orderTop_embI_normS hcop ζ hζ.pow_eq_one lam hlam hlp w
  have ha0 : a ≠ 0 := fun h0 ↦ S.normS_ne_zero ζ hζ.pow_eq_one hw (by rw [ha, h0, map_zero])
  rw [ha] at h
  have e1 : S.embI lam hlam hlp (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) =
      S.embXG (infSub S.n) (infSub_injective S.n S.hn) a := S.embG_algebraMap _ _ _ _ a
  rw [e1, ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
    ha0), ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
    hw), ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at h
  rw [h, S.ordInf_eq hcop w lam hlam hlp]

/-- Integrality: non-negative order at every finite point. -/
def IsIntegralS (K : Type*) [Field K] [Algebra C K] [IsAlgClosed K]
    (w : C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → 0 ≤ S.ordAt K w α β

/-- **The norm of an integral element is a polynomial**, of degree the pole order at infinity,
whose root multiplicities are the sums of the orders at the points above. -/
theorem normS_poly (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0) (hint : S.IsIntegralS K w) :
    ∃ P : C[X], P ≠ 0 ∧
      (P.natDegree : ℤ) = -S.ordInf K w ∧
      (∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
        ((P.map (algebraMap C K)).rootMultiplicity α : ℤ) =
          ∑ j ∈ Finset.range S.n, S.ordAt K w α (algebraMap C K (ζ ^ j) * β)) ∧
      (∀ e : K, (S.p.map (algebraMap C K)).eval e = 0 →
        ((P.map (algebraMap C K)).rootMultiplicity e : ℤ) = S.ordAt K w e 0) := by
  letI := algebraAdjoinSimple (F := C) S.x
  obtain ⟨a, ha⟩ := S.normS_mem ζ hζ w
  have ha0 : a ≠ 0 := fun h0 ↦ S.normS_ne_zero ζ hζ.pow_eq_one hw (by rw [ha, h0, map_zero])
  have hreg : ∀ α : K, a ≠ 0 → 0 ≤ (embX S.x S.htr α a).order := by
    intro α _
    by_cases he : (S.p.map (algebraMap C K)).eval α = 0
    · rw [S.order_norm_br ζ hζ w hw a ha α he]
      exact hint α 0 (by rw [he, zero_pow S.hn.ne'])
    · obtain ⟨β, hβ⟩ := S.exists_beta (K := K) α
      have hβ0 : β ≠ 0 := fun h0 ↦ he (by rw [← hβ, h0, zero_pow S.hn.ne'])
      rw [S.order_norm_nb ζ hζ w hw a ha α β hβ0 hβ]
      exact Finset.sum_nonneg fun j _ ↦ hint α _ (by
        rw [mul_pow, ← map_pow, ← pow_mul, mul_comm j S.n, pow_mul, hζ.pow_eq_one, one_pow,
          map_one, one_mul, hβ])
  obtain ⟨P, hP⟩ := exists_poly_of_regular (K := K) S.x S.htr a hreg
  have haP : a = algebraMap C[X] C⟮S.x⟯ P := Subtype.ext (by rw [hP, algebraMap_adjoinSimple])
  have hP0 : P ≠ 0 := fun h0 ↦ ha0 (by rw [haP, h0, map_zero])
  have hmult : ∀ α : K, (embX S.x S.htr α a).order =
      ((P.map (algebraMap C K)).rootMultiplicity α : ℤ) := fun α ↦ by
    rw [haP, S.embX_algebraMap, shiftHom_eq_branchSub, order_branchSub 1 one_pos α P hP0, one_mul]
  refine ⟨P, hP0, ?_, fun α β hβ0 hβ ↦ ?_, fun e he ↦ ?_⟩
  · have h := S.order_norm_inf (K := K) hcop ζ hζ w hw a ha
    rw [haP, S.embXG_inf_poly P hP0] at h
    have hn : (S.n : ℤ) ≠ 0 := by exact_mod_cast S.hn.ne'
    have := mul_left_cancel₀ hn (show (S.n : ℤ) * -(P.natDegree : ℤ) = S.n * S.ordInf K w by
      rw [← h]; ring)
    omega
  · rw [← hmult, S.order_norm_nb ζ hζ w hw a ha α β hβ0 hβ]
  · rw [← hmult, S.order_norm_br ζ hζ w hw a ha e he]

open Classical in
/-- The points of the curve above `α`. -/
noncomputable def placesOver (ζ : C) (α : K) : Finset (K × K) :=
  if (S.p.map (algebraMap C K)).eval α = 0 then {(α, 0)}
  else (Finset.range S.n).image fun j ↦ (α, algebraMap C K (ζ ^ j) *
    Classical.choose (S.exists_beta (K := K) α))

lemma mem_placesOver (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (Q : K × K)
    (hQ : Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1) : Q ∈ S.placesOver ζ Q.1 := by
  classical
  rw [placesOver]
  split_ifs with he
  · rw [he, pow_eq_zero_iff S.hn.ne'] at hQ
    rw [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨rfl, hQ⟩
  · set β₀ := Classical.choose (S.exists_beta (K := K) Q.1)
    have hβ₀ : β₀ ^ S.n = _ := Classical.choose_spec (S.exists_beta (K := K) Q.1)
    have hβ0 : β₀ ≠ 0 := fun h0 ↦ he (by rw [← hβ₀, h0, zero_pow S.hn.ne'])
    have hz : IsPrimitiveRoot (algebraMap C K ζ) S.n := hζ.map_of_injective (algebraMap C K).injective
    haveI : NeZero S.n := ⟨S.hn.ne'⟩
    obtain ⟨j, hj, hjx⟩ := hz.eq_pow_of_pow_eq_one (ξ := Q.2 / β₀) (by
      rw [div_pow, hQ, hβ₀, div_self (by rw [← hβ₀]; exact pow_ne_zero _ hβ0)])
    rw [Finset.mem_image]
    refine ⟨j, Finset.mem_range.mpr hj, Prod.ext rfl ?_⟩
    simp only
    rw [map_pow, hjx, div_mul_cancel₀ _ hβ0]

lemma placesOver_spec (ζ : C) (hζ : ζ ^ S.n = 1) (α : K) (Q : K × K) (hQ : Q ∈ S.placesOver ζ α) :
    Q.1 = α ∧ Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := by
  classical
  rw [placesOver] at hQ
  split_ifs at hQ with he
  · rw [Finset.mem_singleton] at hQ
    subst hQ
    exact ⟨rfl, by rw [he, zero_pow S.hn.ne']⟩
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hQ
    refine ⟨rfl, ?_⟩
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm j S.n, pow_mul, hζ, one_pow, map_one, one_mul,
      Classical.choose_spec (S.exists_beta (K := K) α)]

/-- The orders at the points above `α` add up to the multiplicity of `α` in the norm. -/
lemma sum_placesOver (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    (w : C⟮S.x⟯⟮S.y⟯) (P : C[X])
    (hnb : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
        ((P.map (algebraMap C K)).rootMultiplicity α : ℤ) =
          ∑ j ∈ Finset.range S.n, S.ordAt K w α (algebraMap C K (ζ ^ j) * β))
    (hbr : ∀ e : K, (S.p.map (algebraMap C K)).eval e = 0 →
        ((P.map (algebraMap C K)).rootMultiplicity e : ℤ) = S.ordAt K w e 0) (α : K) :
    ∑ Q ∈ S.placesOver ζ α, S.ordAt K w Q.1 Q.2 =
      ((P.map (algebraMap C K)).rootMultiplicity α : ℤ) := by
  classical
  rw [placesOver]
  split_ifs with he
  · rw [Finset.sum_singleton, hbr α he]
  · set β₀ := Classical.choose (S.exists_beta (K := K) α)
    have hβ₀ : β₀ ^ S.n = _ := Classical.choose_spec (S.exists_beta (K := K) α)
    have hβ0 : β₀ ≠ 0 := fun h0 ↦ he (by rw [← hβ₀, h0, zero_pow S.hn.ne'])
    have hz : IsPrimitiveRoot (algebraMap C K ζ) S.n := hζ.map_of_injective (algebraMap C K).injective
    rw [Finset.sum_image fun i hi j hj hij ↦ by
      have h2 := (Prod.ext_iff.mp hij).2
      simp only [map_pow] at h2
      exact hz.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        (mul_right_cancel₀ hβ0 h2), hnb α β₀ hβ0 hβ₀]

/-- **The degree theorem** (inequality): the zeros of an integral `w ≠ 0` at any finite set of
points number at most its pole order at infinity. -/
theorem degree_le (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0) (hint : S.IsIntegralS K w) (T : Finset (K × K))
    (hT : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1) :
    ∑ Q ∈ T, S.ordAt K w Q.1 Q.2 ≤ -S.ordInf K w := by
  classical
  obtain ⟨P, hP0, hdeg, hnb, hbr⟩ := S.normS_poly hcop ζ hζ w hw hint
  rw [← Finset.sum_fiberwise_of_maps_to (t := T.image Prod.fst) (g := Prod.fst)
    (fun Q hQ ↦ Finset.mem_image_of_mem _ hQ), ← hdeg]
  have hfib : ∀ α ∈ T.image Prod.fst, ∑ Q ∈ T with Q.1 = α, S.ordAt K w Q.1 Q.2 ≤
      ((P.map (algebraMap C K)).rootMultiplicity α : ℤ) := fun α _ ↦ by
    rw [← S.sum_placesOver hcop ζ hζ w P hnb hbr α]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun Q hQ ↦ ?_) (fun Q hQ _ ↦ ?_)
    · rw [Finset.mem_filter] at hQ
      rw [← hQ.2]
      exact S.mem_placesOver ζ hζ Q (hT Q hQ.1)
    · exact hint Q.1 Q.2 (S.placesOver_spec ζ hζ.pow_eq_one α Q hQ).2
  refine (Finset.sum_le_sum hfib).trans ?_
  have hPm : P.map (algebraMap C K) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hP0
  simp_rw [← count_roots]
  have h1 : ∑ α ∈ T.image Prod.fst, (P.map (algebraMap C K)).roots.count α ≤
      (P.map (algebraMap C K)).roots.card := by
    calc ∑ α ∈ T.image Prod.fst, (P.map (algebraMap C K)).roots.count α
        ≤ ∑ α ∈ T.image Prod.fst ∪ (P.map (algebraMap C K)).roots.toFinset,
            (P.map (algebraMap C K)).roots.count α :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ ↦ Nat.zero_le _)
      _ = ∑ α ∈ (P.map (algebraMap C K)).roots.toFinset, (P.map (algebraMap C K)).roots.count α :=
          (Finset.sum_subset Finset.subset_union_right (fun α _ hα ↦
            Multiset.count_eq_zero.mpr (fun h ↦ hα (Multiset.mem_toFinset.mpr h)))).symm
      _ = _ := Multiset.toFinset_sum_count_eq _
  have h2 := card_roots' (P.map (algebraMap C K))
  rw [natDegree_map] at h2
  exact_mod_cast h1.trans h2

/-- **The degree theorem** (equality): if `T` contains every finite point where `w` has non-zero
order, the orders at `T` add up to the pole order at infinity. -/
theorem degree_eq (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0) (hint : S.IsIntegralS K w) (T : Finset (K × K))
    (hT : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1)
    (hsupp : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → (α, β) ∉ T →
      S.ordAt K w α β = 0) :
    ∑ Q ∈ T, S.ordAt K w Q.1 Q.2 = -S.ordInf K w := by
  classical
  obtain ⟨P, hP0, hdeg, hnb, hbr⟩ := S.normS_poly hcop ζ hζ w hw hint
  rw [← Finset.sum_fiberwise_of_maps_to (t := T.image Prod.fst) (g := Prod.fst)
    (fun Q hQ ↦ Finset.mem_image_of_mem _ hQ), ← hdeg]
  have hfib : ∀ α ∈ T.image Prod.fst, ∑ Q ∈ T with Q.1 = α, S.ordAt K w Q.1 Q.2 =
      ((P.map (algebraMap C K)).rootMultiplicity α : ℤ) := fun α _ ↦ by
    rw [← S.sum_placesOver hcop ζ hζ w P hnb hbr α]
    refine Finset.sum_subset (fun Q hQ ↦ ?_) (fun Q hQ hQT ↦ ?_)
    · rw [Finset.mem_filter] at hQ
      rw [← hQ.2]
      exact S.mem_placesOver ζ hζ Q (hT Q hQ.1)
    · obtain ⟨h1, h2⟩ := S.placesOver_spec ζ hζ.pow_eq_one α Q hQ
      exact hsupp Q.1 Q.2 h2 (fun hm ↦ hQT (Finset.mem_filter.mpr ⟨hm, h1⟩))
  rw [Finset.sum_congr rfl hfib]
  have hPm : P.map (algebraMap C K) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hP0
  -- every root lies under a point of `T`
  have hroots : (P.map (algebraMap C K)).roots.toFinset ⊆ T.image Prod.fst := by
    intro α hα
    have hpos : 0 < (P.map (algebraMap C K)).rootMultiplicity α :=
      (rootMultiplicity_pos hPm).mpr (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hα))
    rw [← Nat.cast_pos (α := ℤ), ← S.sum_placesOver hcop ζ hζ w P hnb hbr α] at hpos
    obtain ⟨Q, hQ, hQne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    obtain ⟨h1, h2⟩ := S.placesOver_spec ζ hζ.pow_eq_one α Q hQ
    by_contra hnot
    refine hQne (hsupp Q.1 Q.2 h2 fun hm ↦ hnot ?_)
    rw [← h1]
    exact Finset.mem_image_of_mem Prod.fst hm
  simp_rw [← count_roots]
  have h1 : ∑ α ∈ T.image Prod.fst, (P.map (algebraMap C K)).roots.count α =
      (P.map (algebraMap C K)).roots.card := by
    rw [← Multiset.toFinset_sum_count_eq]
    exact (Finset.sum_subset hroots (fun α _ hα ↦
      Multiset.count_eq_zero.mpr (fun h ↦ hα (Multiset.mem_toFinset.mpr h)))).symm
  rw [← natDegree_map (f := algebraMap C K), ← IsAlgClosed.card_roots_eq_natDegree]
  exact_mod_cast h1

end Closed

end SuperData

end Differential
