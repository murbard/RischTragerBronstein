import RischTragerBronstein.Algebraic.SuperDerivG
import RischTragerBronstein.Curves.Puiseux

/-!
# Branches of an arbitrary plane curve

`CurveData C L`: `x ∈ L` transcendental over `C`, `y ∈ L` a root of `F(x, Y)`, `F ∈ C[x][Y]` monic in
`Y` and irreducible over `C⟮x⟯` (so it is the minimal polynomial of `y`).

* `embXG`, `embG`: for an injective substitution `g : C[x] → K⸨T⸩` and a Laurent series `Y` with
  `F(g, Y) = 0`, the ring embedding of `C⟮x⟯⟮y⟯` into `K⸨T⸩` with `y ↦ Y`;
* `deriv_y`: `y′ = −F_x(x, y) / F_y(x, y)` (implicit differentiation);
* `embG_derivG`: along `x ↦ X̂(T)`, `d/dx` becomes `(dX̂/dT)⁻¹ d/dT`;
* `res_liouvilleG`: the residue of a Liouville form `v′ + ∑ cᵢ uᵢ′/uᵢ` along a branch is
  `∑ cᵢ ord uᵢ`.
-/

open Polynomial IntermediateField HahnSeries

namespace Curves

open Differential

section Deriv

variable {R : Type*} [CommRing R]

/-- An additive map satisfying the Leibniz rule. -/
def IsLeibniz (D : R →+ R) : Prop := ∀ a b, D (a * b) = a * D b + b * D a

lemma IsLeibniz.pow {D : R →+ R} (hD : IsLeibniz D) (r : R) (i : ℕ) :
    D (r ^ i) = (i : R) * r ^ (i - 1) * D r := by
  induction i with
  | zero =>
    have h1 := hD 1 1
    simp only [mul_one] at h1
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h1
  | succ i ih =>
    rw [pow_succ, hD, ih]
    rcases i with _ | i
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      push_cast
      ring

/-- A derivation applied to a polynomial expression with variable coefficients. -/
lemma derivation_eval (D : R →+ R) (hD : IsLeibniz D) (Q : R[X]) (r : R) (N : ℕ)
    (hN : Q.natDegree < N) :
    D (Q.eval r) = (∑ i ∈ Finset.range N, D (Q.coeff i) * r ^ i) +
      (derivative Q).eval r * D r := by
  rw [eval_eq_sum_range' hN, map_sum, derivative_eval,
    Polynomial.sum_over_range' _ (fun n ↦ by simp) _ hN, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hD, hD.pow]
  ring

lemma isLeibniz_derivation {A : Type*} {_ : CommSemiring A} {_ : Algebra A R}
    (D : Derivation A R R) : IsLeibniz D.toLinearMap.toAddMonoidHom := fun a b ↦ by
  show D (a * b) = a * D b + b * D a
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

end Deriv

/-- The coefficientwise `x`-derivative `F_x` of `F ∈ C[x][Y]`. -/
noncomputable def dX {C : Type*} [CommRing C] (F : C[X][X]) : C[X][X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1), Polynomial.C (derivative (F.coeff i)) * X ^ i

lemma dX_coeff {C : Type*} [CommRing C] (F : C[X][X]) (i : ℕ) :
    (dX F).coeff i = derivative (F.coeff i) := by
  classical
  simp only [dX, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), derivative_zero]

lemma dX_natDegree_le {C : Type*} [CommRing C] (F : C[X][X]) :
    (dX F).natDegree ≤ F.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    rw [dX_coeff, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi), derivative_zero]

section Deriv2

variable {R : Type*} [CommRing R]

lemma derivation_eval_map {C : Type*} [CommRing C] (D : R →+ R) (hD : IsLeibniz D)
    (φ : C[X] →+* R) (hφ : ∀ P, D (φ P) = φ (derivative P)) (Q : C[X][X]) (r : R) :
    D ((Q.map φ).eval r) = ((dX Q).map φ).eval r + ((derivative Q).map φ).eval r * D r := by
  rw [derivation_eval D hD _ r (Q.natDegree + 1)
      (natDegree_map_le.trans_lt (Nat.lt_succ_self _)),
    derivative_map]
  congr 1
  rw [eval_eq_sum_range' (n := Q.natDegree + 1)
    (natDegree_map_le.trans_lt (Nat.lt_succ_of_le (dX_natDegree_le Q)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_map, coeff_map, hφ, dX_coeff]

end Deriv2

section Embed

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- **A plane algebraic curve** `F(x, y) = 0`, `F` monic in `y` and irreducible over `C⟮x⟯`
(stated without reference to `C⟮x⟯`: no non-zero `G ∈ C[x][Y]` of smaller degree vanishes at `y`). -/
structure CurveData (C L : Type*) [Field C] [Field L] [Algebra C L] where
  x : L
  y : L
  F : C[X][X]
  htr : Transcendental C x
  monic : F.Monic
  irr : ∀ G : C[X][X], G.natDegree < F.natDegree → (G.map (aeval x).toRingHom).eval y = 0 → G = 0
  root : (F.map (aeval x).toRingHom).eval y = 0

namespace CurveData

variable (S : CurveData C L)

/-- `Q(x, y)` for `Q ∈ C[x][Y]`. -/
noncomputable def evXY (Q : C[X][X]) : L := (Q.map (aeval S.x).toRingHom).eval S.y

lemma evXY_F : S.evXY S.F = 0 := S.root

lemma evXY_eq_aeval (Q : C[X][X]) :
    letI := algebraAdjoinSimple (F := C) S.x
    aeval S.y (Q.map (algebraMap C[X] C⟮S.x⟯)) = S.evXY Q := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [aeval_def, eval₂_map, evXY, eval_map]
  congr 1
  ext P
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    exact algebraMap_adjoinSimple S.x (Polynomial.C P)
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    exact algebraMap_adjoinSimple S.x X

lemma isIntegral : IsIntegral C⟮S.x⟯ S.y := by
  letI := algebraAdjoinSimple (F := C) S.x
  refine ⟨_, S.monic.map (algebraMap C[X] C⟮S.x⟯), ?_⟩
  rw [← aeval_def, S.evXY_eq_aeval]; exact S.root

lemma minpoly_eq :
    letI := algebraAdjoinSimple (F := C) S.x
    minpoly C⟮S.x⟯ S.y = S.F.map (algebraMap C[X] C⟮S.x⟯) := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have hroot : aeval S.y (S.F.map (algebraMap C[X] C⟮S.x⟯)) = 0 := by
    rw [S.evXY_eq_aeval]; exact S.root
  have hdvd := minpoly.dvd C⟮S.x⟯ S.y hroot
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic S.isIntegral)
    (S.monic.map _) hdvd ?_).symm
  rw [S.monic.natDegree_map]
  by_contra hlt
  push Not at hlt
  set m := minpoly C⟮S.x⟯ S.y with hm
  set G := IsLocalization.integerNormalization (nonZeroDivisors C[X]) m with hG
  have hG0 : G ≠ 0 :=
    (IsFractionRing.integerNormalization_eq_zero_iff).not.mpr (minpoly.ne_zero S.isIntegral)
  have hGdeg : G.natDegree < S.F.natDegree := by
    refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_) hlt
    have hk' : k ∉ m.support := fun h ↦ absurd (le_natDegree_of_mem_supp k h)
      (not_le.mpr (by exact_mod_cast hk))
    exact notMem_support_iff.mp fun h ↦ hk'
      (IsLocalization.integerNormalization_support (nonZeroDivisors C[X]) m h)
  have hGy : (G.map (aeval S.x).toRingHom).eval S.y = 0 := by
    have h := IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors C[X])
      (algebraMap C⟮S.x⟯ L) m (x := S.y) (by rw [← aeval_def]; exact minpoly.aeval _ _)
    rw [eval_map]
    convert h using 2
    ext P
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
        Function.comp_apply]
      exact (algebraMap_adjoinSimple S.x (Polynomial.C P)).symm
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
        Function.comp_apply]
      exact (algebraMap_adjoinSimple S.x X).symm
  exact hG0 (S.irr G hGdeg hGy)

lemma natDegree_minpoly :
    (minpoly C⟮S.x⟯ S.y).natDegree = S.F.natDegree := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [S.minpoly_eq, S.monic.natDegree_map]

/-- `Q(x, y)` as an element of `C⟮x⟯⟮y⟯`. -/
noncomputable def evT (Q : C[X][X]) : C⟮S.x⟯⟮S.y⟯ :=
  letI := algebraAdjoinSimple (F := C) S.x
  (Q.map ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).comp (algebraMap C[X] C⟮S.x⟯))).eval
    (AdjoinSimple.gen C⟮S.x⟯ S.y)

lemma coe_evT (Q : C[X][X]) : (S.evT Q : L) = S.evXY Q := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [evT, ← S.evXY_eq_aeval, aeval_def, eval_map, eval₂_map]
  show (C⟮S.x⟯⟮S.y⟯).val.toRingHom (eval₂ _ _ Q) = _
  rw [Polynomial.hom_eval₂]
  rfl

lemma evXY_mem (Q : C[X][X]) : S.evXY Q ∈ C⟮S.x⟯⟮S.y⟯ := by
  rw [← S.coe_evT]; exact SetLike.coe_mem _

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

lemma embXG_comp (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) :
    letI := algebraAdjoinSimple (F := C) S.x
    (S.embXG g hg).comp (algebraMap C[X] C⟮S.x⟯) = g :=
  RingHom.ext fun P ↦ S.embXG_algebraMap g hg P

lemma rootG_eval (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    (minpoly C⟮S.x⟯ S.y).eval₂ (S.embXG g hg) Y = 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [S.minpoly_eq, eval₂_map, S.embXG_comp, ← eval_map, hY]

/-- **The expansion along `g`, with `y ↦ Y`.** -/
noncomputable def embG (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K :=
  (AdjoinRoot.lift (S.embXG g hg) _ (S.rootG_eval g hg Y hY)).comp
    (adjoinRootEquivAdjoin C⟮S.x⟯ S.isIntegral).symm.toRingEquiv.toRingHom

variable (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
  (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0)

lemma embG_gen : S.embG g hg Y hY (AdjoinSimple.gen C⟮S.x⟯ S.y) = Y := by
  simp only [embG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.lift_root]

lemma embG_algebraMap (a : C⟮S.x⟯) :
    S.embG g hg Y hY (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) = S.embXG g hg a := by
  simp only [embG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  exact AdjoinRoot.lift_of _

lemma embG_evT (Q : C[X][X]) : S.embG g hg Y hY (S.evT Q) = (Q.map g).eval Y := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [evT, eval_map, Polynomial.hom_eval₂, embG_gen, eval_map]
  congr 1
  ext P <;> simp only [RingHom.coe_comp, Function.comp_apply, embG_algebraMap, embXG_algebraMap]

lemma embG_injective : Function.Injective (S.embG g hg Y hY) := (S.embG g hg Y hY).injective

end CurveData

end Embed

section Deriv3

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma deriv_evXY (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (Q : C[X][X]) :
    (S.evXY Q)′ = S.evXY (dX Q) + S.evXY (derivative Q) * S.y′ :=
  derivation_eval_map (Differential.deriv (R := L)).toLinearMap.toAddMonoidHom
    (isLeibniz_derivation _) _ (fun P ↦ deriv_aeval_x S.x hC hx P) Q S.y

lemma evXY_derivative_ne_zero : S.evXY (derivative S.F) ≠ 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hsep := (minpoly.irreducible S.isIntegral).separable
  have h := hsep.aeval_derivative_ne_zero (minpoly.aeval C⟮S.x⟯ S.y)
  rwa [S.minpoly_eq, derivative_map, S.evXY_eq_aeval] at h

/-- **Implicit differentiation**: `y′ = −F_x(x, y) / F_y(x, y)`. -/
lemma deriv_y (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    S.y′ = -S.evXY (dX S.F) / S.evXY (derivative S.F) := by
  have h := S.deriv_evXY hC hx S.F
  rw [S.evXY_F, map_zero] at h
  rw [eq_div_iff S.evXY_derivative_ne_zero]
  linear_combination -h

/-- `C⟮x⟯⟮y⟯` is closed under the derivation. -/
lemma derivClosedXY (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    ∀ w ∈ C⟮S.x⟯⟮S.y⟯, w′ ∈ C⟮S.x⟯⟮S.y⟯ := by
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x 1 (by rw [hx, map_one])
  set T := C⟮S.x⟯⟮S.y⟯
  have hF : ∀ a ∈ C⟮S.x⟯, a ∈ T := fun a ha ↦ by
    have := IntermediateField.algebraMap_mem T (⟨a, ha⟩ : C⟮S.x⟯)
    exact this
  let U : IntermediateField C⟮S.x⟯ L :=
    { carrier := {w | w ∈ T ∧ w′ ∈ T}
      mul_mem' := fun {u v} hu hv ↦ ⟨mul_mem hu.1 hv.1, by
        rw [Derivation.leibniz]
        exact add_mem (mul_mem hu.1 hv.2) (mul_mem hv.1 hu.2)⟩
      one_mem' := ⟨one_mem _, by simp⟩
      add_mem' := fun {u v} hu hv ↦ ⟨add_mem hu.1 hv.1, by
        rw [map_add]; exact add_mem hu.2 hv.2⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      algebraMap_mem' := fun a ↦ ⟨T.algebraMap_mem a, hF _ (hcl _ a.2)⟩
      inv_mem' := fun u hu ↦ ⟨inv_mem hu.1, by
        rw [Derivation.leibniz_inv]
        exact mul_mem (neg_mem (pow_mem (inv_mem hu.1) 2)) hu.2⟩ }
  have hyU : S.y ∈ U := by
    refine ⟨mem_adjoin_simple_self _ _, ?_⟩
    rw [S.deriv_y hC hx]
    exact div_mem (neg_mem (S.evXY_mem _)) (S.evXY_mem _)
  have hle : T ≤ U := adjoin_simple_le_iff.mpr hyU
  intro w hw
  exact (hle hw).2

lemma const_mem (c : C) : algebraMap C L c ∈ C⟮S.x⟯⟮S.y⟯ :=
  IntermediateField.algebraMap_mem _
    (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮S.x⟯)

section Generic

variable (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hX hgX

/-- `embXG g` intertwines `d/dx` and `δ`. -/
theorem embXG_derivG (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    ∀ a (ha : a ∈ C⟮S.x⟯), ∃ ha' : a′ ∈ C⟮S.x⟯,
      S.embXG g hg ⟨a′, ha'⟩ = SuperData.deltaX Xh (S.embXG g hg ⟨a, ha⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x 1 (by rw [hx, map_one])
  intro a ha
  refine ⟨hcl a ha, ?_⟩
  induction ha using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have e1 : (⟨S.x′, hcl S.x (mem_adjoin_simple_self C S.x)⟩ : C⟮S.x⟯) = 1 := Subtype.ext hx
    have e2 : (⟨S.x, mem_adjoin_simple_self C S.x⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ X :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_X])
    rw [e1, map_one, e2, S.embXG_algebraMap, hgX, SuperData.deltaX_subst Xh hX, derivative_X, map_one]
  | algebraMap c =>
    have e1 : (⟨(algebraMap C L c)′, hcl _ (IntermediateField.algebraMap_mem _ c)⟩ : C⟮S.x⟯) = 0 :=
      Subtype.ext (by
        show (algebraMap C L c)′ = 0
        rw [deriv_algebraMap, hC, map_zero])
    have e2 : (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮S.x⟯) =
        algebraMap C[X] C⟮S.x⟯ (Polynomial.C c) :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_C])
    rw [e1, map_zero, e2, S.embXG_algebraMap, hgX, SuperData.deltaX_subst Xh hX, derivative_C, map_zero]
  | add u v hu hv ihu ihv =>
    have e1 : (⟨(u + v)′, hcl _ (add_mem hu hv)⟩ : C⟮S.x⟯) =
        ⟨u′, hcl u hu⟩ + ⟨v′, hcl v hv⟩ := Subtype.ext (by simp)
    have e2 : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e1 : (⟨(u * v)′, hcl _ (mul_mem hu hv)⟩ : C⟮S.x⟯) =
        ⟨u, hu⟩ * ⟨v′, hcl v hv⟩ + ⟨v, hv⟩ * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz])
    have e2 : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_mul, map_mul, ihu, ihv, map_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
  | inv u hu ihu =>
    have e1 : (⟨u⁻¹′, hcl _ (inv_mem hu)⟩ : C⟮S.x⟯) = -(⟨u, hu⟩ : C⟮S.x⟯)⁻¹ ^ 2 * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz_inv])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯) = (⟨u, hu⟩ : C⟮S.x⟯)⁻¹ := rfl
    rw [e1, e2, map_mul, map_neg, map_pow, map_inv₀, ihu, Derivation.leibniz_inv, smul_eq_mul]

/-- `embG` intertwines `d/dx` and `δ`. -/
theorem embG_derivG (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) :
    ∀ w (hw : w ∈ C⟮S.x⟯⟮S.y⟯),
      S.embG g hg Y hY ⟨w′, S.derivClosedXY hC hx w hw⟩ =
        SuperData.deltaX Xh (S.embG g hg Y hY ⟨w, hw⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hdc := S.derivClosedXY hC hx
  set φ := S.embG g hg Y hY
  intro w hw
  induction hw using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have e : (⟨S.y′, hdc _ (mem_adjoin_simple_self _ _)⟩ : C⟮S.x⟯⟮S.y⟯) =
        -S.evT (dX S.F) / S.evT (derivative S.F) :=
      Subtype.ext (by
        show S.y′ = _
        rw [S.deriv_y hC hx]
        simp [S.coe_evT])
    have e2 : (⟨S.y, mem_adjoin_simple_self _ _⟩ : C⟮S.x⟯⟮S.y⟯) = AdjoinSimple.gen C⟮S.x⟯ S.y :=
      rfl
    have hB : S.evT (derivative S.F) ≠ 0 := fun h ↦
      S.evXY_derivative_ne_zero (by rw [← S.coe_evT, h]; rfl)
    have hB' : ((derivative S.F).map g).eval Y ≠ 0 := by
      rw [← S.embG_evT g hg Y hY]
      exact (map_ne_zero_iff _ (S.embG_injective g hg Y hY)).mpr hB
    rw [e, e2, map_div₀, map_neg, S.embG_evT, S.embG_evT, S.embG_gen]
    have hφ : ∀ P, SuperData.deltaX Xh (g P) = g (derivative P) := fun P ↦ by
      rw [hgX, SuperData.deltaX_subst Xh hX, hgX]
    set D0 : LaurentSeries K →+ LaurentSeries K :=
      AddMonoidHom.mk' (SuperData.deltaX Xh) (fun a b ↦ map_add _ a b) with hD0
    have hL : IsLeibniz D0 := fun a b ↦ by
      simp only [hD0, AddMonoidHom.mk'_apply, Derivation.leibniz, smul_eq_mul]
    have hd := derivation_eval_map D0 hL g hφ S.F Y
    have hD0Y : D0 Y = SuperData.deltaX Xh Y := rfl
    rw [hD0Y] at hd
    rw [hY, map_zero] at hd
    rw [div_eq_iff hB']
    linear_combination hd
  | algebraMap a =>
    have e1 : (⟨(algebraMap C⟮S.x⟯ L a)′, hdc _ (IntermediateField.algebraMap_mem _ a)⟩ :
        C⟮S.x⟯⟮S.y⟯) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨(a : L)′,
          derivClosed_adjoin_simple S.x 1 (by rw [hx, map_one]) _ a.2⟩ := rfl
    have e2 : (⟨algebraMap C⟮S.x⟯ L a, IntermediateField.algebraMap_mem _ a⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := rfl
    rw [e1, e2, S.embG_algebraMap, S.embG_algebraMap]
    obtain ⟨ha', h⟩ := S.embXG_derivG Xh hX g hg hgX hC hx (a : L) a.2
    exact h
  | add u v hu hv ihu ihv =>
    have e1 : (⟨(u + v)′, hdc _ (add_mem hu hv)⟩ : C⟮S.x⟯⟮S.y⟯) =
        ⟨u′, hdc u hu⟩ + ⟨v′, hdc v hv⟩ := Subtype.ext (by simp)
    have e2 : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e1 : (⟨(u * v)′, hdc _ (mul_mem hu hv)⟩ : C⟮S.x⟯⟮S.y⟯) =
        ⟨u, hu⟩ * ⟨v′, hdc v hv⟩ + ⟨v, hv⟩ * ⟨u′, hdc u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz])
    have e2 : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_mul, map_mul, ihu, ihv, map_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
  | inv u hu ihu =>
    have e1 : (⟨u⁻¹′, hdc _ (inv_mem hu)⟩ : C⟮S.x⟯⟮S.y⟯) =
        -(⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ ^ 2 * ⟨u′, hdc u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz_inv])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯⟮S.y⟯) = (⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ := rfl
    rw [e1, e2, map_mul, map_neg, map_pow, map_inv₀, ihu, Derivation.leibniz_inv, smul_eq_mul]

/-- **The residue of a Liouville form along any branch.** -/
theorem res_liouvilleG (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) {ι : Type*} (s : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    LaurentSeries.res (S.embG g hg Y hY ⟨f, hf⟩ * LaurentSeries.derivation Xh) =
      ∑ i ∈ s, algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K) := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embG g hg Y hY
  have hdc := S.derivClosedXY hC hx
  have hT : (⟨f, hf⟩ : T) = ⟨v′, hdc v hv⟩ + ∑ i ∈ s,
      (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) *
        ((⟨(u i)′, hdc _ (hu i)⟩ : T) / ⟨u i, hu i⟩) :=
    Subtype.ext (by simp [heq])
  have hφ0 : ∀ i, φ ⟨u i, hu i⟩ ≠ 0 := fun i ↦
    (map_ne_zero_iff φ φ.injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
  have hcst : ∀ i, φ ⟨algebraMap C L (c i), S.const_mem (c i)⟩ =
      HahnSeries.C (algebraMap C K (c i)) := fun i ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    have e : (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) =
        algebraMap C⟮S.x⟯ T (algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i))) :=
      Subtype.ext (by
        show algebraMap C L (c i) = ((algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i)) : C⟮S.x⟯) : L)
        rw [algebraMap_adjoinSimple, aeval_C])
    rw [e, S.embG_algebraMap, S.embXG_algebraMap, hgX, substHom_apply, Polynomial.map_C, aeval_C,
      HahnSeries.algebraMap_apply']
    exact ofPowerSeries_C _
  have hδ : ∀ F : LaurentSeries K, SuperData.deltaX Xh F * LaurentSeries.derivation Xh =
      LaurentSeries.derivation F := fun F ↦ by
    rw [SuperData.deltaX_apply]; field_simp
  rw [hT, map_add, map_sum, S.embG_derivG Xh hX g hg hgX hC hx Y hY v hv, add_mul, hδ,
    LaurentSeries.res_add, LaurentSeries.derivation_apply, LaurentSeries.res_derivative, zero_add,
    Finset.sum_mul, SuperData.res_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_derivG Xh hX g hg hgX hC hx Y hY (u i) (hu i), hcst,
    show HahnSeries.C (algebraMap C K (c i)) * (SuperData.deltaX Xh (φ ⟨u i, hu i⟩) / φ ⟨u i, hu i⟩) *
      LaurentSeries.derivation Xh = HahnSeries.C (algebraMap C K (c i)) *
        (SuperData.deltaX Xh (φ ⟨u i, hu i⟩) * LaurentSeries.derivation Xh / φ ⟨u i, hu i⟩) by ring,
    hδ, SuperData.res_C_mul, LaurentSeries.derivation_apply, LaurentSeries.res_logDeriv _ (hφ0 i)]

end Generic

end CurveData

end Deriv3

end Curves
