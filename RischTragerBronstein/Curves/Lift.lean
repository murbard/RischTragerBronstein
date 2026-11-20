import RischTragerBronstein.Curves.ConstIndep
import RischTragerBronstein.Liouville.Transcendence
import RischTragerBronstein.Liouville.Strong
import RischTragerBronstein.Differential.Constants

/-!
# Lifting an elementary integral to a Liouville form on a general curve

* `const_of_deriv_zero`: over an algebraically closed `C`, the constants of `C⟮x⟯⟮y⟯` are `C`
  (a constant has no pole along any branch);
* `curve_lift`: if `g ∈ E = Kc(x, y)` has an elementary integral, then in some differential field
  `L ⊇ E` with constants `Cc ⊇ Kc`, `g = v′ + ∑ dᵢ uᵢ′/uᵢ` with `v, uᵢ` in the function field
  `Cc(x, y)` of the same curve (whose equation stays irreducible over `Cc(x)`, by
  `const_independent`). Stated in continuation-passing style.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section ConstBase

variable {K : Type*} [Field K] [CharZero K]

lemma lowerBd_of_derivation_zero (z : LaurentSeries K) (hz : LaurentSeries.derivation z = 0) :
    LowerBd z 0 := by
  intro k hk
  have h := congrArg (fun w : LaurentSeries K ↦ w.coeff (k - 1)) hz
  simp only [LaurentSeries.derivation_apply, derivative_coeff, sub_add_cancel,
    HahnSeries.coeff_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hk.ne)

lemma order_nonneg_of_lowerBd (z : LaurentSeries K) (hz : LowerBd z 0) : 0 ≤ z.order := by
  by_cases h0 : z = 0
  · rw [h0, HahnSeries.order_zero]
  by_contra hneg
  push Not at hneg
  exact HahnSeries.coeff_order_eq_zero.not.mpr h0 (hz _ hneg)

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma branch_regular_of_deriv_zero (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (z : C⟮S.x⟯⟮S.y⟯) (hz : (z : L)′ = 0) :
    0 ≤ (S.embG g hg Y hY z).order := by
  refine order_nonneg_of_lowerBd _ (lowerBd_of_derivation_zero _ ?_)
  have h := S.embG_derivG Xh hX g hg hgX hC hx Y hY z z.2
  have e : (⟨(z : L)′, S.derivClosedXY hC hx _ z.2⟩ : C⟮S.x⟯⟮S.y⟯) = 0 := Subtype.ext hz
  rw [e, map_zero, SuperData.deltaX_apply] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (inv_ne_zero hX)

/-- **The constants of `C⟮x⟯⟮y⟯` are `C`** (`C` algebraically closed). -/
theorem const_of_deriv_zero [IsAlgClosed C] (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (z : C⟮S.x⟯⟮S.y⟯) (hz : (z : L)′ = 0) : (z : L) ∈ Set.range (algebraMap C L) := by
  have hfin : S.RegularFinite C z := fun a N hN l hl r hr ↦
    S.branch_regular_of_deriv_zero hC hx _ (by
      rw [SuperData.derivation_branchX N (Nat.pos_of_ne_zero hN) a]
      exact HahnSeries.single_ne_zero (by exact_mod_cast hN)) _ _
      (fun P ↦ by rw [SuperData.branchSub_eq_subst]) _ _ z hz
  have hinf : S.RegularInf C z := fun N hN l hl r hr ↦
    S.branch_regular_of_deriv_zero hC hx _ (by
      rw [SuperData.derivation_infX N]
      refine HahnSeries.single_ne_zero ?_
      simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
      exact hN) _ _ (fun P ↦ by rw [SuperData.infSub_eq_subst]) _ _ z hz
  obtain ⟨M0, hM0, h⟩ := S.algebraic_of_regular (K := C) z hfin hinf
  have hint : IsIntegral C (z : L) := ⟨M0, hM0, by rwa [← aeval_def]⟩
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible C (minpoly.irreducible hint)
  have hm := minpoly.monic hint
  have hnat : (minpoly C (z : L)).natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg
  have heq : minpoly C (z : L) = X + Polynomial.C ((minpoly C (z : L)).coeff 0) := by
    conv_lhs => rw [hm.as_sum, hnat]
    simp
  have h0 := minpoly.aeval C (z : L)
  rw [heq, map_add, aeval_X, aeval_C] at h0
  exact ⟨-(minpoly C (z : L)).coeff 0, by rw [map_neg]; linear_combination -h0⟩

end CurveData

end ConstBase

section LiftSec

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **The Liouville lift** on a general curve. -/
theorem curve_lift {P : Prop} (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (g : E) (hel : HasElementaryIntegral g)
    (k : ∀ (Cc L : Type u) [Field Cc] [CharZero Cc] [Field L] [CharZero L] [Algebra Cc L]
      [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] (φ : Kc →+* Cc)
      (jE : E →+* L) (SL : CurveData Cc L),
      (∀ c : Cc, c′ = 0) → SL.x′ = 1 → (∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L)) →
      SL.x = jE S.x → SL.y = jE S.y → SL.F = S.F.map (mapRingHom φ) →
      (∀ z : E, (jE z)′ = jE z′) → (∀ c : Kc, jE (algebraMap Kc E c) = algebraMap Cc L (φ c)) →
      (∀ z : E, jE z ∈ Cc⟮SL.x⟯⟮SL.y⟯) →
      (∀ (v : L), v ∈ Cc⟮SL.x⟯⟮SL.y⟯ → ∀ (ιI : Type) (sI : Finset ιI) (d w : ιI → L),
        (∀ i ∈ sI, (d i)′ = 0) → (∀ i ∈ sI, w i ≠ 0 ∧ w i ∈ Cc⟮SL.x⟯⟮SL.y⟯) →
        jE g = v′ + ∑ i ∈ sI, d i * logDeriv (w i) → P)) : P := by
  classical
  obtain ⟨L, _, _, _, _, hE, G, hG⟩ := hel
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  obtain ⟨ιL, sL, cL, u, v, hdata, hv, heq⟩ := liouville_strong hE _ G hG
  let Cc := constants L
  let _ : Differential Cc := ⟨0⟩
  have hDAc : DifferentialAlgebra Cc L := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun a b h ↦ by
    have := congrArg (fun z : Cc ↦ (z : L)) h
    simpa using this⟩
  set jE := algebraMap E L with hjdef
  have hj : ∀ z : E, (jE z)′ = jE z′ := fun z ↦ deriv_algebraMap z
  have hCc : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hxL : (jE S.x)′ = 1 := by rw [hj, hx, map_one]
  have htr : Transcendental Cc (jE S.x) :=
    transcendental_of_deriv_ne_zero hCc (by rw [hxL]; exact one_ne_zero)
  have hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L) := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩
  have hconstE : ∀ k : Kc, (jE (algebraMap Kc E k))′ = 0 := fun k ↦ by
    rw [hj, deriv_algebraMap, hC, map_zero, map_zero]
  let φ : Kc →+* Cc :=
    { toFun := fun k ↦ ⟨jE (algebraMap Kc E k), hconstE k⟩
      map_one' := by ext; simp
      map_mul' := fun u w ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun u w ↦ by ext; simp }
  have hφL : ∀ k : Kc, algebraMap Cc L (φ k) = jE (algebraMap Kc E k) := fun _ ↦ rfl
  have haevK : ∀ P : Kc[X], aeval (jE S.x) (P.map φ) = jE (aeval S.x P) := by
    intro P
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]; rfl
  set Fc : Cc[X][X] := S.F.map (mapRingHom φ) with hFc
  have hmapF : ∀ Q : Kc[X][X], ((Q.map (mapRingHom φ)).map (aeval (jE S.x)).toRingHom).eval
      (jE S.y) = jE ((Q.map (aeval S.x).toRingHom).eval S.y) := by
    intro Q
    rw [Polynomial.map_map, eval_map, eval_map, hom_eval₂]
    congr 1
    ext P
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact haevK (Polynomial.C P)
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact haevK X
  have hFcdeg : Fc.natDegree = S.F.natDegree := S.monic.natDegree_map _
  let SL : CurveData Cc L :=
    { x := jE S.x
      y := jE S.y
      F := Fc
      htr := htr
      monic := S.monic.map _
      irr := by
        intro Gc hGc hGc0
        rw [hFcdeg] at hGc
        set n := S.F.natDegree with hn
        set D := ∑ i ∈ Finset.range n, (Gc.coeff i).natDegree with hD
        set s : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range (D + 1) with hs
        set e : ℕ × ℕ → E := fun p ↦ S.x ^ p.2 * S.y ^ p.1 with he
        set c : ℕ × ℕ → L := fun p ↦ algebraMap Cc L ((Gc.coeff p.1).coeff p.2) with hcdef
        have hDi : ∀ i < n, (Gc.coeff i).natDegree ≤ D := fun i hi ↦
          Finset.single_le_sum (f := fun i ↦ (Gc.coeff i).natDegree) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_range.mpr hi)
        have hrel : ∑ p ∈ s, c p * jE (e p) = 0 := by
          rw [← hGc0, eval_eq_sum_range' (n := n) (natDegree_map_le.trans_lt hGc),
            Finset.sum_product]
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            aeval_eq_sum_range' (n := D + 1)
              (Nat.lt_succ_of_le (hDi i (Finset.mem_range.mp hi))), Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          simp only [hcdef, he, map_mul, map_pow, Algebra.smul_def]
          ring
        have hind : ∀ κ : ℕ × ℕ → E, (∀ p ∈ s, (κ p)′ = 0) → ∑ p ∈ s, κ p * e p = 0 →
            ∀ p ∈ s, κ p = 0 := by
          intro κ hκ hsum
          have hK : ∀ p ∈ s, ∃ a : Kc, algebraMap Kc E a = κ p := fun p hp ↦
            S.const_of_deriv_zero hC hx ⟨κ p, hgen _⟩ (hκ p hp)
          choose! κc hκc using hK
          set H : Kc[X][X] := ∑ i ∈ Finset.range n, Polynomial.C
            (∑ k ∈ Finset.range (D + 1), Polynomial.C (κc (i, k)) * X ^ k) * X ^ i with hH
          have hHc : ∀ i, H.coeff i = if i < n then
              ∑ k ∈ Finset.range (D + 1), Polynomial.C (κc (i, k)) * X ^ k else 0 := by
            intro i
            simp only [hH, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
              Finset.sum_ite_eq, Finset.mem_range]
          have hHdeg : H.natDegree < n := by
            have hn0 := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
            refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_)
              (by omega : n - 1 < n)
            rw [hHc, if_neg (by have : n - 1 < i := by exact_mod_cast hi
                                omega)]
          have hH0 : (H.map (aeval S.x).toRingHom).eval S.y = 0 := by
            rw [← hsum, Finset.sum_product, hH, Polynomial.map_sum, eval_finsetSum]
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
              eval_C, eval_pow, eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum,
              Finset.sum_mul]
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            rw [map_mul, aeval_C, map_pow, aeval_X,
              hκc (i, k) (Finset.mem_product.mpr ⟨hi, hk⟩), he]
            ring
          have hHz := S.irr H hHdeg hH0
          intro p hp
          obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
          have h1 := congrArg (fun Q ↦ (Q.coeff p.1).coeff p.2) hHz
          simp only [hHc, if_pos (Finset.mem_range.mp hp1), finsetSum_coeff, coeff_C_mul,
            coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
            Polynomial.coeff_zero, coeff_C] at h1
          rw [← hκc p hp]
          simp only [if_pos (Finset.mem_range.mp hp2)] at h1
          rw [show p = (p.1, p.2) from rfl, h1, map_zero]
        have hc0 := const_independent jE hj s e hind c
          (fun p _ ↦ by simp only [hcdef]; exact deriv_algebraMap _ |>.trans (by rw [hCc, map_zero]))
          hrel
        refine Polynomial.ext fun i ↦ Polynomial.ext fun k ↦ ?_
        rw [Polynomial.coeff_zero, Polynomial.coeff_zero]
        by_cases hi : i < n
        · by_cases hk : k ≤ D
          · have := hc0 (i, k) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi,
              Finset.mem_range.mpr (Nat.lt_succ_of_le hk)⟩)
            simp only [hcdef] at this
            exact (map_eq_zero_iff _ (algebraMap Cc L).injective).mp this
          · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hDi i hi) (not_le.mp hk))
        · rw [coeff_eq_zero_of_natDegree_lt (p := Gc) (by omega), Polynomial.coeff_zero]
      root := by rw [hmapF, S.root, map_zero] }
  have hKx : ∀ w : E, w ∈ Kc⟮S.x⟯ → jE w ∈ Cc⟮jE S.x⟯ := by
    let T : IntermediateField Kc E :=
      { carrier := {w | jE w ∈ Cc⟮jE S.x⟯}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
        one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
        zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
        algebraMap_mem' := fun c ↦ by
          simp only [Set.mem_setOf_eq]
          rw [← hφL]
          exact IntermediateField.algebraMap_mem _ _
        inv_mem' := fun a ha ↦ by
          simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
    have hle : Kc⟮S.x⟯ ≤ T := by
      rw [adjoin_simple_le_iff]
      exact mem_adjoin_simple_self Cc (jE S.x)
    exact fun w hw ↦ hle hw
  have hEs : ∀ e : E, jE e ∈ Cc⟮SL.x⟯⟮SL.y⟯ := by
    let T : IntermediateField Kc⟮S.x⟯ E :=
      { carrier := {w | jE w ∈ Cc⟮SL.x⟯⟮SL.y⟯}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
        one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
        zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
        algebraMap_mem' := fun c ↦ by
          simp only [Set.mem_setOf_eq]
          exact IntermediateField.algebraMap_mem (Cc⟮SL.x⟯⟮SL.y⟯)
            (⟨jE c, hKx c c.2⟩ : Cc⟮jE S.x⟯)
        inv_mem' := fun a ha ↦ by
          simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
    have hle : Kc⟮S.x⟯⟮S.y⟯ ≤ T := by
      rw [adjoin_simple_le_iff]
      exact mem_adjoin_simple_self _ (jE S.y)
    exact fun e ↦ hle (hgen e)
  have hcf : ∀ w ∈ Differential.constField E L, w ∈ Cc⟮SL.x⟯⟮SL.y⟯ := by
    let N : IntermediateField E L :=
      { (Cc⟮SL.x⟯⟮SL.y⟯).toSubfield with algebraMap_mem' := hEs }
    have : Differential.constField E L ≤ N := adjoin_le_iff.mpr fun w hw ↦ by
      obtain ⟨c', rfl⟩ := hconst w hw
      exact SL.const_mem c'
    exact fun w hw ↦ this hw
  refine k Cc L φ jE SL hCc hxL hconst rfl rfl rfl hj (fun c ↦ rfl) hEs v (hcf v hv) ιL sL cL u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩) ?_
  rw [heq, add_comm]

end LiftSec

end Curves
