import RischTragerBronstein.Algebraic.SupPrincipalMul
import Mathlib.NumberTheory.ClassNumber.FunctionField

/-!
# Divisor classes on superelliptic curves over a finite field have finite order

* `isIntegralS_of_monic`: an element satisfying a monic equation over `C[x]` is integral at every
  finite place;
* `exists_principalMulN` (over a finite field `k`, `n` invertible): for `Γ` supported on
  non-branch `k`-points with distinct abscissae, some positive multiple `h Γ` is principal
  (`PrincipalMulN`). Through the finiteness of the class group of the ring of integers of
  `k(x)[y]/(yⁿ − f)` (Mathlib: `FunctionField.RingOfIntegers`).
-/

open Polynomial IntermediateField Differential Differential.SuperData
open scoped nonZeroDivisors

namespace Differential.SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- **Integral elements are integral at every finite place.** -/
theorem isIntegralS_of_monic (w : C⟮S.x⟯⟮S.y⟯) (d : ℕ) (a : ℕ → C[X])
    (h : w ^ d + ∑ i ∈ Finset.range d, S.polyX (a i) * w ^ i = 0) : S.IsIntegralS K w := by
  classical
  intro α β hv
  by_contra hneg
  push_neg at hneg
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [hφ, map_zero, HahnSeries.order_zero] at hneg
    exact lt_irrefl _ hneg
  set e := S.ordAt K w α β with he_def
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h'
    · simp at h
    · exact h'
  have hsum0 : ∑ i ∈ Finset.range d, S.polyX (a i) * w ^ i ≠ 0 := by
    intro h0
    rw [h0, add_zero] at h
    exact pow_ne_zero _ hw0 h
  have hbound := le_order_hom_sum (K := K) φ (Finset.range d)
    (fun i ↦ S.polyX (a i) * w ^ i) ((d : ℤ) * e + 1) (fun i hi hti ↦ by
      have hi' := Finset.mem_range.mp hi
      have hP : S.polyX (a i) ≠ 0 := fun h0 ↦ hti (by rw [h0, zero_mul])
      have haP : a i ≠ 0 := fun h0 ↦ hP (by rw [h0]; simp [polyX])
      have h1 : (0 : ℤ) ≤ S.ordAt K (S.polyX (a i)) α β := by
        rw [S.ordAt_polyX _ haP α β hv]; split_ifs <;> positivity
      rw [order_hom_mul φ hP (pow_ne_zero _ hw0), order_hom_pow, ← hφ, ← hφ]
      have h2 : ((d : ℤ) - i) * (-e) ≥ 1 := by
        have : (1 : ℤ) ≤ d - i := by omega
        nlinarith
      nlinarith) hsum0
  have heq : φ (w ^ d) = -φ (∑ i ∈ Finset.range d, S.polyX (a i) * w ^ i) := by
    rw [← map_neg, ← eq_neg_iff_add_eq_zero.mpr h]
  have hlead : (φ (w ^ d)).order = d * e := by rw [order_hom_pow, ← hφ]
  rw [heq, HahnSeries.order_neg] at hlead
  linarith

end Differential.SuperData

namespace Sup.PicFinN

variable {k : Type*} [Field k] [PerfectField k]

/-- `Yⁿ − f` over `k(x)`. -/
noncomputable def cpolyN (f : k[X]) (n : ℕ) : (RatFunc k)[X] :=
  X ^ n - Polynomial.C (algebraMap k[X] (RatFunc k) f)

variable (f : k[X]) (n : ℕ) [hn : Fact (0 < n)] [hsq : Fact (Squarefree f)]
  [hp : Fact (0 < f.natDegree)]

instance irreducible_cpolyN : Fact (Irreducible (cpolyN f n)) :=
  ⟨irreducible_X_pow_sub_C_fraction n hn.out f hsq.out hp.out (RatFunc k)⟩

/-- The function field of `yⁿ = f`. -/
abbrev LN := AdjoinRoot (cpolyN f n)

/-- The class `y`. -/
noncomputable abbrev yN : LN f n := AdjoinRoot.root (cpolyN f n)

/-- The class `x`. -/
noncomputable abbrev xN : LN f n := algebraMap (RatFunc k) (LN f n) RatFunc.X

instance : FunctionField k (LN f n) :=
  (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible (cpolyN f n)))).finite

lemma aeval_xN (P : k[X]) : aeval (xN f n) P = algebraMap k[X] (LN f n) P := by
  rw [xN, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]

lemma yN_pow : yN f n ^ n = aeval (xN f n) f := by
  have h : aeval (yN f n) (cpolyN f n) = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [cpolyN, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  rw [h, aeval_xN, IsScalarTower.algebraMap_apply k[X] (RatFunc k) (LN f n)]

variable [hnk : Fact ((n : k) ≠ 0)]

instance : Algebra.IsSeparable (RatFunc k) (LN f n) := by
  have hsep : IsSeparable (RatFunc k) (yN f n) := by
    unfold IsSeparable
    rw [AdjoinRoot.minpoly_root (Irreducible.ne_zero (Fact.out : Irreducible (cpolyN f n)))]
    have hmon : (cpolyN f n).leadingCoeff = 1 :=
      (monic_X_pow_sub_C _ hn.out.ne').leadingCoeff
    rw [hmon, inv_one, Polynomial.C_1, mul_one]
    have hf0 : algebraMap k[X] (RatFunc k) f ≠ 0 := by
      intro h0
      have : f = 0 := IsFractionRing.injective k[X] (RatFunc k) (by rw [h0, map_zero])
      have := hp.out; simp_all
    have hnR : ((n : ℕ) : RatFunc k) ≠ 0 := by
      have : (algebraMap k (RatFunc k)) (n : k) ≠ 0 :=
        (_root_.map_ne_zero _).mpr (Fact.out : ((n : k) ≠ 0))
      rwa [map_natCast] at this
    exact separable_X_pow_sub_C _ hnR hf0
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc k) (LN f n)).2 hsep
  rw [IntermediateField.adjoin_root_eq_top] at this
  exact Algebra.IsSeparable.of_algHom (E' := ↥(⊤ : IntermediateField (RatFunc k) (LN f n)))
    (f := IntermediateField.topEquiv.symm.toAlgHom)

/-- The curve `yⁿ = f` as `SuperData` on `k(x)[y]/(yⁿ − f)`. -/
noncomputable def SN : SuperData k (LN f n) where
  x := xN f n
  y := yN f n
  n := n
  p := f
  htr := (transcendental_algebraMap_iff (algebraMap (RatFunc k) (LN f n)).injective).mpr
    RatFunc.transcendental_X
  hn := hn.out
  hsq := hsq.out
  hp := hp.out
  hy := yN_pow f n
  hnC := hnk.out

@[simp] lemma SN_n : (SN f n).n = n := rfl
@[simp] lemma SN_p : (SN f n).p = f := rfl
@[simp] lemma SN_x : (SN f n).x = xN f n := rfl
@[simp] lemma SN_y : (SN f n).y = yN f n := rfl

/-- Every element of `k(x)[y]/(yⁿ − f)` lies in `k⟮x⟯⟮y⟯`. -/
lemma mem_gen (z : LN f n) : z ∈ (k⟮(SN f n).x⟯⟮(SN f n).y⟯ : IntermediateField _ (LN f n)) := by
  set E := (k⟮(SN f n).x⟯⟮(SN f n).y⟯ : IntermediateField _ (LN f n))
  have hpoly : ∀ P : k[X], algebraMap (RatFunc k) (LN f n) (algebraMap k[X] (RatFunc k) P) ∈ E := by
    intro P
    rw [← IsScalarTower.algebraMap_apply, ← aeval_xN]
    have h1 : aeval (xN f n) P ∈ k⟮(SN f n).x⟯ :=
      IntermediateField.algebra_adjoin_le_adjoin k _
        (Polynomial.aeval_mem_adjoin_singleton k (xN f n) (p := P))
    exact E.algebraMap_mem (⟨_, h1⟩ : k⟮(SN f n).x⟯)
  have hbase : ∀ c : RatFunc k, algebraMap (RatFunc k) (LN f n) c ∈ E := by
    intro c
    rw [← RatFunc.num_div_denom c, map_div₀]
    exact E.div_mem (hpoly _) (hpoly _)
  have hy : yN f n ∈ E := IntermediateField.mem_adjoin_simple_self _ _
  induction z using AdjoinRoot.induction_on with
  | ih P =>
    rw [← AdjoinRoot.aeval_eq, aeval_eq_sum_range]
    refine E.sum_mem fun i _ ↦ ?_
    rw [Algebra.smul_def]
    exact E.mul_mem (hbase _) (pow_mem hy i)

/-- The identification of `k(x)[y]/(yⁿ − f)` with `k⟮x⟯⟮y⟯`. -/
noncomputable def toF : LN f n →+* k⟮(SN f n).x⟯⟮(SN f n).y⟯ where
  toFun z := ⟨z, mem_gen f n z⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma toF_coe (z : LN f n) : ((toF f n z : k⟮(SN f n).x⟯⟮(SN f n).y⟯) : LN f n) = z := rfl

lemma toF_injective : Function.Injective (toF f n) := (toF f n).injective

lemma toF_algebraMap (P : k[X]) : toF f n (algebraMap k[X] (LN f n) P) = (SN f n).polyX P := by
  apply Subtype.ext
  rw [toF_coe, (SN f n).polyX_coe, SN_x, aeval_xN]

/-- **Elements of the ring of integers are integral at every finite place.** -/
lemma isIntegralS_of_isIntegral (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    {z : LN f n} (hz : IsIntegral k[X] z) : (SN f n).IsIntegralS K (toF f n z) := by
  obtain ⟨P, hPm, hP⟩ := hz
  apply (SN f n).isIntegralS_of_monic (toF f n z) P.natDegree (fun i ↦ P.coeff i)
  apply Subtype.ext
  have e := hP
  rw [hPm.as_sum, eval₂_add, eval₂_X_pow, eval₂_finset_sum] at e
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow] at e
  simp only [map_add, map_sum, map_mul, map_pow, IntermediateField.coe_add,
    AddSubmonoidClass.coe_finset_sum, IntermediateField.coe_mul, IntermediateField.coe_pow,
    toF_coe, IntermediateField.coe_zero]
  rw [← e]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← toF_algebraMap, toF_coe]

lemma toF_yN_sub (hn2 : 2 ≤ n) (c : k) :
    toF f n (yN f n - algebraMap k[X] (LN f n) (Polynomial.C c)) =
      (SN f n).elemW (X - Polynomial.C (Polynomial.C c)) := by
  apply Subtype.ext
  rw [toF_coe, ← aeval_xN, aeval_C, elemW, Finset.sum_eq_add 0 1 (by norm_num)
    (fun i _ hi ↦ by rw [coeff_sub, coeff_X, coeff_C, if_neg (Ne.symm hi.2),
      if_neg hi.1, sub_zero, polyX]; erw [map_zero, map_zero, zero_mul])
    (fun h ↦ absurd (Finset.mem_range.mpr (by simp; omega)) h)
    (fun h ↦ absurd (Finset.mem_range.mpr (by simp; omega)) h)]
  simp only [coeff_sub, coeff_X_zero, zero_sub, coeff_X_one, coeff_C,
    one_ne_zero, if_false, sub_zero, pow_zero, mul_one, pow_one, IntermediateField.coe_add,
    IntermediateField.coe_mul, (SN f n).polyX_coe, aeval_neg, aeval_C, aeval_one, one_mul]
  rw [AdjoinSimple.coe_gen]
  simp [SN, sub_eq_neg_add]

/-- The order of `y − c` at a point `(a, b)`, `b ≠ 0`: positive iff `b = c`. -/
lemma one_le_ordAt_yN_sub (hn2 : 2 ≤ n) (c : k) (a b : AlgebraicClosure k) (hb : b ≠ 0)
    (hv : b ^ (SN f n).n = ((SN f n).p.map (algebraMap k (AlgebraicClosure k))).eval a) :
    1 ≤ (SN f n).ordAt (AlgebraicClosure k)
      (toF f n (yN f n - algebraMap k[X] (LN f n) (Polynomial.C c))) a b ↔
      b = algebraMap k _ c := by
  set W : k[X][X] := X - Polynomial.C (Polynomial.C c)
  have hW : ∀ i, (SN f n).n ≤ i → W.coeff i = 0 := by
    intro i hi
    change n ≤ i at hi
    rw [coeff_sub, coeff_X, coeff_C, if_neg (by omega), if_neg (by omega), sub_zero]
  have hW0 : W ≠ 0 := X_sub_C_ne_zero _
  rw [toF_yN_sub f n hn2]
  have h := (SN f n).le_ordAt_iff_vanish W hW ((SN f n).elemW_ne_zero W hW0 hW) a b hb hv 1
  rw [Nat.cast_one] at h
  rw [h]
  have hev : evalW (W.map (mapRingHom (algebraMap k (AlgebraicClosure k)))) a b =
      b - algebraMap k _ c := by
    simp [W, evalW]
  constructor
  · intro hv1
    have := evalW_of_vanish le_rfl hv1
    rw [hev] at this
    exact sub_eq_zero.mp this
  · intro hb'
    exact vanish1_of_evalW hv (by rw [hev, hb', sub_self])

/-- The ring of integers of `k(x)[y]/(yⁿ − f)`. -/
noncomputable abbrev O := FunctionField.ringOfIntegers k (LN f n)

section Ideal

variable {r : ℕ} (α β : Fin r → k) (mq : Fin r → ℕ) (hβf : ∀ q, β q ^ n = f.eval (α q))

/-- The points of `Γ` over `k̄`. -/
noncomputable abbrev pt (q : Fin r) : AlgebraicClosure k × AlgebraicClosure k :=
  (algebraMap k (AlgebraicClosure k) (α q), algebraMap k (AlgebraicClosure k) (β q))

include hβf in
lemma pt_valid (q : Fin r) : (pt α β q).2 ^ (SN f n).n =
    ((SN f n).p.map (algebraMap k (AlgebraicClosure k))).eval (pt α β q).1 := by
  show (algebraMap k _ (β q)) ^ n = (f.map (algebraMap k _)).eval (algebraMap k _ (α q))
  rw [← map_pow, hβf q, eval_map, eval₂_hom]

/-- `{z : z vanishes on m Γ}`. -/
noncomputable def J (m : ℕ) : Ideal (O f n) where
  carrier := {z | (z : LN f n) ≠ 0 → ∀ q, ((m * mq q : ℕ) : ℤ) ≤
    (SN f n).ordAt (AlgebraicClosure k) (toF f n z) (pt α β q).1 (pt α β q).2}
  add_mem' := by
    intro u v hu hv huv q
    by_cases hu0 : (u : LN f n) = 0
    · have e : ((u + v : O f n) : LN f n) = v := by
        rw [Subalgebra.coe_add, hu0, zero_add]
      rw [e] at huv ⊢; exact hv huv q
    by_cases hv0 : (v : LN f n) = 0
    · have e : ((u + v : O f n) : LN f n) = u := by
        rw [Subalgebra.coe_add, hv0, add_zero]
      rw [e] at huv ⊢; exact hu hu0 q
    obtain ⟨φ, hφ⟩ := (SN f n).ordAt_hom (K := AlgebraicClosure k) _ _ (pt_valid f n α β hβf q)
    have hne : ∀ z : LN f n, z ≠ 0 → φ (toF f n z) ≠ 0 := fun z hz ↦
      (map_ne_zero_iff _ φ.injective).mpr ((map_ne_zero_iff _ (toF_injective f n)).mpr hz)
    rw [hφ, Subalgebra.coe_add, map_add, map_add]
    have h := HahnSeries.min_order_le_order_add (x := φ (toF f n u)) (y := φ (toF f n v))
      (by rw [← map_add, ← map_add]; exact hne _ (by rwa [← Subalgebra.coe_add]))
    have h1 := hu hu0 q
    have h2 := hv hv0 q
    rw [hφ] at h1 h2
    exact le_trans (le_min h1 h2) h
  zero_mem' := fun h ↦ absurd rfl h
  smul_mem' := by
    intro c z hz hcz q
    have hc0 : (c : LN f n) ≠ 0 := fun h0 ↦ hcz (by rw [smul_eq_mul, Subalgebra.coe_mul, h0, zero_mul])
    have hz0 : (z : LN f n) ≠ 0 := fun h0 ↦ hcz (by rw [smul_eq_mul, Subalgebra.coe_mul, h0, mul_zero])
    have hv := pt_valid f n α β hβf q
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul,
      (SN f n).ordAt_mul hv ((map_ne_zero_iff _ (toF_injective f n)).mpr hc0)
        ((map_ne_zero_iff _ (toF_injective f n)).mpr hz0)]
    have h1 := isIntegralS_of_isIntegral f n (AlgebraicClosure k) c.2 _ _ hv
    have h2 := hz hz0 q
    linarith

variable {f n α β mq}

lemma J_mul_le (a b : ℕ) : J f n α β mq hβf a * J f n α β mq hβf b ≤ J f n α β mq hβf (a + b) := by
  rw [Submodule.mul_le]
  intro u hu v hv huv q
  have hu0 : (u : LN f n) ≠ 0 := fun h0 ↦ huv (by rw [Subalgebra.coe_mul, h0, zero_mul])
  have hv0 : (v : LN f n) ≠ 0 := fun h0 ↦ huv (by rw [Subalgebra.coe_mul, h0, mul_zero])
  have hv' := pt_valid f n α β hβf q
  rw [Subalgebra.coe_mul, map_mul,
    (SN f n).ordAt_mul hv' ((map_ne_zero_iff _ (toF_injective f n)).mpr hu0)
      ((map_ne_zero_iff _ (toF_injective f n)).mpr hv0)]
  have h1 := hu hu0 q
  have h2 := hv hv0 q
  push_cast at h1 h2 ⊢
  linarith

lemma J_pow_le (m : ℕ) : J f n α β mq hβf 1 ^ (m + 1) ≤ J f n α β mq hβf (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono_left ih).trans (J_mul_le hβf _ _)

end Ideal

section Main

variable [Fintype k] [DecidableEq k]

omit [Fintype k] [DecidableEq k] in
lemma isIntegral_yN : IsIntegral k[X] (yN f n) :=
  ⟨X ^ n - Polynomial.C f, monic_X_pow_sub_C _ hn.out.ne', by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, yN_pow, aeval_xN, sub_self]⟩

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Finite order** of divisor classes over a finite field. -/
theorem exists_principalMulN_aux (hn2 : 2 ≤ n) (hcop : Nat.Coprime n f.natDegree) {r : ℕ}
    (α β : Fin r → k) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) :
    ∃ h, 1 ≤ h ∧ PrincipalMulN f n f.natDegree α β mq h := by
  set S := SN f n with hS
  set Kb := AlgebraicClosure k
  set ι := algebraMap k Kb with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcop
  have hv : ∀ q, (pt α β q).2 ^ S.n = (S.p.map ι).eval (pt α β q).1 := pt_valid f n α β hβf
  have hβK : ∀ q, ι (β q) ≠ 0 := fun q ↦ (map_ne_zero_iff _ hιi).mpr (hβ q)
  have hFne : ∀ z : LN f n, z ≠ 0 → toF f n z ≠ 0 := fun z hz ↦
    (map_ne_zero_iff _ (toF_injective f n)).mpr hz
  have hint : ∀ z : O f n, S.IsIntegralS Kb (toF f n z) := fun z ↦
    isIntegralS_of_isIntegral f n Kb z.2
  -- `w = ∏ (x − α_q)^{m_q}`
  set W : k[X] := ∏ q, (X - Polynomial.C (α q)) ^ mq q with hW_def
  have hW0 : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  set zw : O f n := algebraMap k[X] (O f n) W with hzw_def
  have hzwF : toF f n zw = S.polyX W := toF_algebraMap f n W
  have hzw0 : (zw : LN f n) ≠ 0 := fun h0 ↦ S.polyX_ne_zero hW0 (by rw [← hzwF, h0, map_zero])
  set I := J f n α β mq hβf 1 with hI_def
  have hWord : ∀ (e : Fin r → ℕ) (a b : Kb), b ^ S.n = (S.p.map ι).eval a → b ≠ 0 →
      S.ordAt Kb (S.polyX (∏ q, (X - Polynomial.C (α q)) ^ e q)) a b =
        ∑ q, if ι (α q) = a then (e q : ℤ) else 0 := by
    intro e a b hvab hb
    rw [S.ordAt_polyX_prod _ _ _ _ _ hvab]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [S.ordAt_polyX_lin _ _ _ hvab, if_neg hb]
    by_cases h : a = ι (α q)
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  have hzwI : zw ∈ I := fun _ q ↦ by
    rw [hzwF, hW_def, hWord mq _ _ (hv q) (hβK q)]
    have := Finset.single_le_sum (f := fun q' ↦ if ι (α q') = (pt α β q).1 then (mq q' : ℤ) else 0)
      (fun q' _ ↦ by split_ifs <;> positivity) (Finset.mem_univ q)
    rw [if_pos (show ι (α q) = (pt α β q).1 from rfl)] at this
    push_cast
    linarith
  have hI0 : I ≠ ⊥ := fun h0 ↦ hzw0 (by
    have := (Submodule.eq_bot_iff _).mp h0 _ hzwI
    rw [this]; rfl)
  have hI : I ∈ (Ideal (O f n))⁰ := mem_nonZeroDivisors_of_ne_zero hI0
  set c := ClassGroup.mk0 (⟨I, hI⟩ : (Ideal (O f n))⁰)
  set h := orderOf c
  have hpos : 0 < h := orderOf_pos c
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI h)]
    have : (⟨I ^ h, pow_mem hI h⟩ : (Ideal (O f n))⁰) = ⟨I, hI⟩ ^ h := Subtype.ext (by simp)
    rw [this, map_pow, pow_orderOf_eq_one]
  obtain ⟨z₀, hz₀⟩ := hprin
  have hz₀' : Ideal.span {z₀} = I ^ h := hz₀.symm
  have hle : I ^ h ≤ J f n α β mq hβf h := by
    have := J_pow_le (mq := mq) hβf (h - 1); rwa [Nat.sub_add_cancel hpos] at this
  have hdiv : ∀ u ∈ I, ∃ c : O f n, c * z₀ = u ^ h := fun u hu ↦
    Ideal.mem_span_singleton'.mp (by rw [hz₀']; exact Ideal.pow_mem_pow hu h)
  have hz00 : (z₀ : LN f n) ≠ 0 := by
    intro h0
    obtain ⟨c', hc'⟩ := hdiv zw hzwI
    have : ((zw ^ h : O f n) : LN f n) = 0 := by
      rw [← hc', Subalgebra.coe_mul, h0, mul_zero]
    rw [SubmonoidClass.coe_pow] at this
    exact hzw0 (pow_eq_zero_iff hpos.ne' |>.mp this)
  -- upper bounds from divisibility
  have hupper : ∀ u ∈ I, (u : LN f n) ≠ 0 → ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt Kb (toF f n z₀) a b ≤ h * S.ordAt Kb (toF f n u) a b := by
    intro u hu hu0 a b hvab
    obtain ⟨c', hc'⟩ := hdiv u hu
    have hc0 : (c' : LN f n) ≠ 0 := fun h0 ↦ hu0 (by
      have : ((u ^ h : O f n) : LN f n) = 0 := by rw [← hc', Subalgebra.coe_mul, h0, zero_mul]
      rw [SubmonoidClass.coe_pow] at this
      exact pow_eq_zero_iff hpos.ne' |>.mp this)
    have e : S.ordAt Kb (toF f n ((c' * z₀ : O f n) : LN f n)) a b =
        S.ordAt Kb (toF f n ((u ^ h : O f n) : LN f n)) a b := by rw [hc']
    rw [Subalgebra.coe_mul, map_mul, S.ordAt_mul hvab (hFne _ hc0) (hFne _ hz00),
      SubmonoidClass.coe_pow, map_pow, S.ordAt_pow hvab] at e
    have := hint c' a b hvab
    linarith
  -- the elements `y − β_q`
  have hyint : ∀ c : k, IsIntegral k[X] (yN f n - algebraMap k[X] (LN f n) (Polynomial.C c)) :=
    fun c ↦ (isIntegral_yN f n).sub isIntegral_algebraMap
  have hptinj : Function.Injective (pt α β) := fun q q' h ↦
    hP (Prod.ext (hιi (Prod.ext_iff.mp h).1) (hιi (Prod.ext_iff.mp h).2))
  set yq : Fin r → O f n := fun q ↦ ⟨_, hyint (β q)⟩ with hyq_def
  have hyq1 : ∀ q, 1 ≤ S.ordAt Kb (toF f n (yq q)) (pt α β q).1 (pt α β q).2 := fun q ↦
    (one_le_ordAt_yN_sub f n hn2 (β q) _ _ (hβK q) (hv q)).mpr rfl
  have hyq0 : ∀ q (a b : Kb), b ^ S.n = (S.p.map ι).eval a → b ≠ 0 → b ≠ ι (β q) →
      S.ordAt Kb (toF f n (yq q)) a b = 0 := by
    intro q a b hvab hb hbq
    refine le_antisymm ?_ (hint (yq q) a b hvab)
    by_contra hlt
    push_neg at hlt
    exact hbq ((one_le_ordAt_yN_sub f n hn2 (β q) _ _ hb hvab).mp hlt)
  have hyqne : ∀ q, toF f n (yq q) ≠ 0 := fun q h0 ↦ by
    have := hyq1 q
    rw [h0] at this
    simp [ordAt, HahnSeries.order_zero] at this
  -- the elements `∏ (y − β_q)^{e_q} ∏ (x − α_q)^{m_q − e_q}`
  set Ee : (Fin r → ℕ) → O f n := fun e ↦
    (∏ q, yq q ^ e q) * algebraMap k[X] (O f n) (∏ q, (X - Polynomial.C (α q)) ^ (mq q - e q))
    with hEe_def
  have hPe0 : ∀ e : Fin r → ℕ, (∏ q, (X - Polynomial.C (α q)) ^ (mq q - e q) : k[X]) ≠ 0 :=
    fun e ↦ Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hEF : ∀ e, toF f n (Ee e) = (∏ q, toF f n (yq q) ^ e q) *
      S.polyX (∏ q, (X - Polynomial.C (α q)) ^ (mq q - e q)) := by
    intro e
    rw [hEe_def, Subalgebra.coe_mul, map_mul, SubmonoidClass.coe_finset_prod, map_prod]
    simp only [SubmonoidClass.coe_pow, map_pow]
    rw [← toF_algebraMap]
    rfl
  have hEne : ∀ e, toF f n (Ee e) ≠ 0 := fun e ↦ by
    rw [hEF]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (hyqne q))
      (S.polyX_ne_zero (hPe0 e))
  have hE0 : ∀ e, (Ee e : LN f n) ≠ 0 := fun e h0 ↦ hEne e (by rw [h0, map_zero])
  have hEord : ∀ e (a b : Kb), b ^ S.n = (S.p.map ι).eval a → b ≠ 0 →
      S.ordAt Kb (toF f n (Ee e)) a b =
        (∑ q, (e q : ℤ) * S.ordAt Kb (toF f n (yq q)) a b) +
          ∑ q, if ι (α q) = a then ((mq q - e q : ℕ) : ℤ) else 0 := by
    intro e a b hvab hb
    rw [hEF, S.ordAt_mul hvab (Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (hyqne q))
      (S.polyX_ne_zero (hPe0 e)), S.ordAt_prod hvab _ _ fun q _ ↦ pow_ne_zero _ (hyqne q),
      hWord (fun q ↦ mq q - e q) a b hvab hb]
    congr 1
    exact Finset.sum_congr rfl fun q _ ↦ S.ordAt_pow hvab _ _
  have hEI : ∀ e : Fin r → ℕ, (∀ q, e q ≤ mq q) → Ee e ∈ I := by
    intro e he _ q
    rw [hEord e _ _ (hv q) (hβK q)]
    have h1 : (e q : ℤ) ≤ ∑ q', (e q' : ℤ) * S.ordAt Kb (toF f n (yq q')) (pt α β q).1
        (pt α β q).2 := by
      have := Finset.single_le_sum (f := fun q' ↦ (e q' : ℤ) *
        S.ordAt Kb (toF f n (yq q')) (pt α β q).1 (pt α β q).2)
        (fun q' _ ↦ mul_nonneg (by positivity) (hint _ _ _ (hv q))) (Finset.mem_univ q)
      have h2 := hyq1 q
      have h3 : (0 : ℤ) ≤ e q := by positivity
      nlinarith
    have h2 : ((mq q - e q : ℕ) : ℤ) ≤ ∑ q', if ι (α q') = (pt α β q).1 then
        ((mq q' - e q' : ℕ) : ℤ) else 0 := by
      have := Finset.single_le_sum (f := fun q' ↦ if ι (α q') = (pt α β q).1 then
        ((mq q' - e q' : ℕ) : ℤ) else 0) (fun q' _ ↦ by split_ifs <;> positivity)
        (Finset.mem_univ q)
      rw [if_pos (show ι (α q) = (pt α β q).1 from rfl)] at this
      exact this
    have h3 : ((mq q - e q : ℕ) : ℤ) = mq q - e q := by push_cast [Nat.cast_sub (he q)]; ring
    push_cast
    linarith
  -- the orders of `z₀`
  have hz0q : ∀ q, S.ordAt Kb (toF f n z₀) (pt α β q).1 (pt α β q).2 = h * mq q := by
    intro q0
    apply le_antisymm
    · set e : Fin r → ℕ := fun q ↦ if α q = α q0 ∧ q ≠ q0 then mq q else 0 with he_def
      have hle' : ∀ q, e q ≤ mq q := fun q ↦ by simp only [e]; split_ifs <;> omega
      have := hupper (Ee e) (hEI e hle') (hE0 e) _ _ (hv q0)
      rw [hEord e _ _ (hv q0) (hβK q0)] at this
      have hs1 : (∑ q, (e q : ℤ) * S.ordAt Kb (toF f n (yq q)) (pt α β q0).1 (pt α β q0).2) = 0 := by
        refine Finset.sum_eq_zero fun q _ ↦ ?_
        by_cases hq : α q = α q0 ∧ q ≠ q0
        · rw [hyq0 q _ _ (hv q0) (hβK q0) (fun h ↦ hq.2 (hP (Prod.ext hq.1 (hιi h).symm))),
            mul_zero]
        · simp [e, if_neg hq]
      have hs2 : (∑ q, if ι (α q) = (pt α β q0).1 then ((mq q - e q : ℕ) : ℤ) else 0) = mq q0 := by
        rw [Finset.sum_eq_single q0 ?_ (fun h ↦ absurd (Finset.mem_univ q0) h)]
        · rw [if_pos (show ι (α q0) = (pt α β q0).1 from rfl)]; simp [e]
        · intro q _ hq
          by_cases hα' : ι (α q) = (pt α β q0).1
          · rw [if_pos hα']
            have hαe : α q = α q0 := hιi hα'
            simp [e, hαe, hq]
          · rw [if_neg hα']
      rw [hs1, hs2, zero_add] at this
      exact this
    · have := hle (hz₀' ▸ Ideal.mem_span_singleton_self z₀) hz00 q0
      exact_mod_cast this
  have hz0off : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a → (∀ q, (a, b) ≠ pt α β q) →
      S.ordAt Kb (toF f n z₀) a b = 0 := by
    intro a b hvab hne
    refine le_antisymm ?_ (hint z₀ a b hvab)
    by_cases hA : ∃ q, a = ι (α q)
    · obtain ⟨q1, rfl⟩ := hA
      have hb0 : b ≠ 0 := fun h0 ↦ by
        have h1 : b ^ S.n = (ι (β q1)) ^ S.n := hvab.trans (hv q1).symm
        rw [h0, zero_pow S.hn.ne'] at h1
        exact pow_ne_zero _ (hβK q1) h1.symm
      set e : Fin r → ℕ := fun q ↦ if α q = α q1 then mq q else 0 with he_def
      have hle' : ∀ q, e q ≤ mq q := fun q ↦ by simp only [e]; split_ifs <;> omega
      have := hupper (Ee e) (hEI e hle') (hE0 e) _ _ hvab
      rw [hEord e _ _ hvab hb0] at this
      have hs1 : (∑ q, (e q : ℤ) * S.ordAt Kb (toF f n (yq q)) (ι (α q1)) b) = 0 := by
        refine Finset.sum_eq_zero fun q _ ↦ ?_
        by_cases hq : α q = α q1
        · rw [hyq0 q _ _ hvab hb0 (fun h ↦ hne q (by
            show (ι (α q1), b) = (ι (α q), ι (β q)); rw [h, hq])), mul_zero]
        · simp [e, if_neg hq]
      have hs2 : (∑ q, if ι (α q) = ι (α q1) then ((mq q - e q : ℕ) : ℤ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun q _ ↦ ?_
        by_cases hq : ι (α q) = ι (α q1)
        · simp [e, hιi hq]
        · rw [if_neg hq]
      rw [hs1, hs2, zero_add, mul_zero] at this
      exact this
    · push_neg at hA
      have := hupper zw hzwI hzw0 _ _ hvab
      rwa [hzwF, S.ordAt_polyX_prod_off α _ _ _ hvab hA, mul_zero] at this
  -- the order at infinity
  have hinfz : S.ordInf Kb (toF f n z₀) = -((h * ∑ q, mq q : ℕ) : ℤ) := by
    have hdeg := S.degree_eq' Kb hcopS (toF f n z₀) (hFne _ hz00) (hint z₀)
      (Finset.univ.image (pt α β)) (fun Q hQ ↦ by
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQ; exact hv q)
      (fun a b hvab hn' ↦ hz0off a b hvab fun q hq ↦ hn' (Finset.mem_image.mpr ⟨q, Finset.mem_univ _,
        hq.symm⟩))
    rw [Finset.sum_image fun q _ q' _ hq ↦ hptinj hq] at hdeg
    simp only [hz0q] at hdeg
    push_cast
    rw [Finset.mul_sum]
    linarith
  obtain ⟨Wz, hWz, hWz0, hWzs⟩ := S.elem_repr (K := Kb) hcopS (toF f n z₀) (hFne _ hz00) (hint z₀)
    (h * ∑ q, mq q) (by rw [hinfz])
  have hWW : ∀ i, S.n ≤ i → Wz.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨a', ha'⟩ : ∃ a', (Wz.coeff i).coeff a' ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hWzs i a' ha').1
    omega
  refine ⟨h, hpos, Wz, hWz0, hWzs, fun q ↦ ?_⟩
  have h1 := (S.le_ordAt_iff_vanish Wz hWW (by rw [hWz]; exact hFne _ hz00) _ _ (hβK q) (hv q)
    (h * mq q)).mp (by rw [hWz, hz0q]; push_cast; rfl)
  obtain ⟨V, hV⟩ := exists_branchN f hn.out
    (IsUnit.mk0 _ (mul_ne_zero hnk.out (pow_ne_zero _ (hβ q)))) (hβf q) (h * mq q)
  exact vanishAtN_of_map ι hιi hn.out (hV.mono (Nat.le_succ _)) (S.unit_branch _ (hβK q)) h1

end Main

end Sup.PicFinN

namespace Sup

/-- **Divisors over a finite field have finite order** (`Pic⁰(k)` is finite): for `f` squarefree
of positive degree prime to `n` over a finite field `k` with `n ≠ 0` in `k`, and `Γ` supported on
non-branch `k`-points with distinct abscissae, `h Γ` is principal for some `h ≥ 1`. -/
theorem exists_principalMulN {k : Type*} [Field k] [Fintype k] [DecidableEq k] (f : k[X])
    {n : ℕ} (hn : 0 < n) (hsq : Squarefree f) (hd : 0 < f.natDegree)
    (hcop : Nat.Coprime n f.natDegree) (hnk : (n : k) ≠ 0) {r : ℕ} (α β : Fin r → k)
    (mq : Fin r → ℕ) (hn2 : 2 ≤ n) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0) (hβf : ∀ q, β q ^ n = f.eval (α q)) :
    ∃ h, 1 ≤ h ∧ PrincipalMulN f n f.natDegree α β mq h := by
  haveI : Fact (0 < n) := ⟨hn⟩
  haveI : Fact (Squarefree f) := ⟨hsq⟩
  haveI : Fact (0 < f.natDegree) := ⟨hd⟩
  haveI : Fact ((n : k) ≠ 0) := ⟨hnk⟩
  exact PicFinN.exists_principalMulN_aux f n hn2 hcop α β mq hP hβ hβf

end Sup
