import RischTragerBronstein.Mixed.KWEmbed
import RischTragerBronstein.Curves.Branch

/-!
# General curves over a differential base with `x′ = ω(x)`: differential local expansions

For a plane curve `S : CurveData C L` (`F(x, y) = 0`, `F` monic in `y`) over a differential field `C`
(not necessarily constants) with `x′ = ω(x)`, `ω ∈ C[x]`:

* `deriv_evXYW`, `deriv_yW'`: implicit differentiation with the coefficient derivation
  `implicitDeriv ω` (`P ↦ P^δ + ω P′`) in place of `d/dx`;
* `derivClosedXYW'`: `C(x, y)` is closed under the derivation;
* `embXG_dSW'`, `embG_dSW'`: along any branch (`x ↦ X̂`, `y ↦ Y`), with `dS s X̂ = ω(X̂)`, the
  embedding intertwines the derivation with `dS s = δ + s d/dT` (`KPLaurent`).

This is `Curves/Branch` (`x′ = 1`, constant `C`) and `KWEmbed` (`yⁿ = p(x)`) for arbitrary curves.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Differential

namespace Curves

/-- The coefficientwise `implicitDeriv ω` of `F ∈ C[x][Y]`. -/
noncomputable def dXW {C : Type*} [CommRing C] [Differential C] (ω : C[X]) (F : C[X][X]) : C[X][X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1), Polynomial.C (implicitDeriv ω (F.coeff i)) * X ^ i

lemma dXW_coeff {C : Type*} [CommRing C] [Differential C] (ω : C[X]) (F : C[X][X]) (i : ℕ) :
    (dXW ω F).coeff i = implicitDeriv ω (F.coeff i) := by
  classical
  simp only [dXW, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

lemma dXW_natDegree_le {C : Type*} [CommRing C] [Differential C] (ω : C[X]) (F : C[X][X]) :
    (dXW ω F).natDegree ≤ F.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    rw [dXW_coeff, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi), map_zero]

/-- **Differentiating `Q(x, r)`** for a derivation `D` with `D (φ P) = φ (implicitDeriv ω P)`. -/
lemma derivation_eval_mapW {R C : Type*} [CommRing R] [CommRing C] [Differential C] (ω : C[X])
    (D : R →+ R) (hD : IsLeibniz D) (φ : C[X] →+* R) (hφ : ∀ P, D (φ P) = φ (implicitDeriv ω P))
    (Q : C[X][X]) (r : R) :
    D ((Q.map φ).eval r) = ((dXW ω Q).map φ).eval r + ((derivative Q).map φ).eval r * D r := by
  rw [derivation_eval D hD _ r (Q.natDegree + 1)
      (natDegree_map_le.trans_lt (Nat.lt_succ_self _)),
    Polynomial.derivative_map]
  congr 1
  rw [eval_eq_sum_range' (n := Q.natDegree + 1)
    (natDegree_map_le.trans_lt (Nat.lt_succ_of_le (dXW_natDegree_le ω Q)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_map, coeff_map, hφ, dXW_coeff]

section DerivW

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]

namespace CurveData

variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)

omit [CharZero C] [CharZero L] [Field K] [CharZero K] [Algebra C K] [Differential K] in
include hx in
lemma deriv_evXYW (Q : C[X][X]) :
    (S.evXY Q)′ = S.evXY (dXW ω Q) + S.evXY (derivative Q) * S.y′ :=
  derivation_eval_mapW ω (Differential.deriv (R := L)).toLinearMap.toAddMonoidHom
    (isLeibniz_derivation _) _ (fun P ↦ deriv_aeval_eq_implicitDeriv S.x ω hx P) Q S.y

omit [Field K] [CharZero K] [Algebra C K] [Differential K] in
include hx in
/-- **Implicit differentiation** over a differential base. -/
lemma deriv_yW' : S.y′ = -S.evXY (dXW ω S.F) / S.evXY (derivative S.F) := by
  have h := S.deriv_evXYW ω hx S.F
  rw [S.evXY_F, map_zero] at h
  rw [eq_div_iff S.evXY_derivative_ne_zero]
  linear_combination -h

omit [Field K] [CharZero K] [Algebra C K] [Differential K] in
include hx in
/-- **`C⟮x⟯⟮y⟯` is closed under the derivation.** -/
lemma derivClosedXYW' : ∀ w ∈ C⟮S.x⟯⟮S.y⟯, w′ ∈ C⟮S.x⟯⟮S.y⟯ := by
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x ω hx
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
    rw [S.deriv_yW' ω hx]
    exact div_mem (neg_mem (S.evXY_mem _)) (S.evXY_mem _)
  have hle : T ≤ U := adjoin_simple_le_iff.mpr hyU
  intro w hw
  exact (hle hw).2

end CurveData

end DerivW

lemma implicitDeriv_eq {C : Type*} [CommRing C] [Differential C] (ω P : C[X]) :
    implicitDeriv ω P = mapCoeffs P + ω * derivative P := by
  simp [implicitDeriv]

section EmbW

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]

namespace CurveData

variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (s Xh : LaurentSeries K) (hXh : dS s Xh = substHom Xh ω)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hx hK hXh hgX

omit [CharZero L] in
/-- `embXG g` intertwines the derivations. -/
theorem embXG_dSW' : ∀ a (ha : a ∈ C⟮S.x⟯),
    S.embXG g hg ⟨a′, derivClosed_adjoin_simple S.x ω hx a ha⟩ = dS s (S.embXG g hg ⟨a, ha⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x ω hx
  have hP : ∀ P : C[X], ∃ h, S.embXG g hg ⟨(aeval S.x P)′, h⟩ =
      dS s (S.embXG g hg (algebraMap C[X] C⟮S.x⟯ P)) := fun P ↦ by
    refine ⟨hcl _ (by rw [← algebraMap_adjoinSimple (F := C) S.x P]; exact SetLike.coe_mem _), ?_⟩
    have e : (⟨(aeval S.x P)′, hcl _ (by
        rw [← algebraMap_adjoinSimple (F := C) S.x P]; exact SetLike.coe_mem _)⟩ : C⟮S.x⟯) =
        algebraMap C[X] C⟮S.x⟯ (mapCoeffs P + ω * derivative P) :=
      Subtype.ext (by
        show (aeval S.x P)′ = _
        rw [algebraMap_adjoinSimple S.x (mapCoeffs P + ω * derivative P),
          deriv_aeval_eq_implicitDeriv S.x ω hx P, implicitDeriv_eq])
    rw [e, S.embXG_algebraMap, S.embXG_algebraMap, hgX, hgX, dS_substHomW hK ω s Xh hXh]
  intro a ha
  induction ha using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    obtain ⟨h, e⟩ := hP X
    have e2 : (⟨S.x, mem_adjoin_simple_self C S.x⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ X :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_X])
    have e3 : (⟨S.x′, hcl S.x (mem_adjoin_simple_self C S.x)⟩ : C⟮S.x⟯) =
        ⟨(aeval S.x X)′, h⟩ := Subtype.ext (by show S.x′ = (aeval S.x X)′; rw [aeval_X])
    rw [e3, e, e2]
  | algebraMap c =>
    obtain ⟨h, e⟩ := hP (Polynomial.C c)
    have e2 : (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮S.x⟯) =
        algebraMap C[X] C⟮S.x⟯ (Polynomial.C c) :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_C])
    have e3 : (⟨(algebraMap C L c)′, hcl _ (IntermediateField.algebraMap_mem _ c)⟩ : C⟮S.x⟯) =
        ⟨(aeval S.x (Polynomial.C c))′, h⟩ :=
      Subtype.ext (by show (algebraMap C L c)′ = (aeval S.x (Polynomial.C c))′; rw [aeval_C])
    rw [e3, e, e2]
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

/-- **`embG` intertwines the derivations** along any branch of a general curve. -/
theorem embG_dSW' (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    ∀ w (hw : w ∈ C⟮S.x⟯⟮S.y⟯),
      S.embG g hg Y hY ⟨w′, S.derivClosedXYW' ω hx w hw⟩ = dS s (S.embG g hg Y hY ⟨w, hw⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hdc := S.derivClosedXYW' ω hx
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x ω hx
  set φ := S.embG g hg Y hY
  intro w hw
  induction hw using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have e : (⟨S.y′, hdc _ (mem_adjoin_simple_self _ _)⟩ : C⟮S.x⟯⟮S.y⟯) =
        -S.evT (dXW ω S.F) / S.evT (derivative S.F) :=
      Subtype.ext (by
        show S.y′ = _
        rw [S.deriv_yW' ω hx]
        simp [S.coe_evT])
    have e2 : (⟨S.y, mem_adjoin_simple_self _ _⟩ : C⟮S.x⟯⟮S.y⟯) = AdjoinSimple.gen C⟮S.x⟯ S.y :=
      rfl
    have hB : S.evT (derivative S.F) ≠ 0 := fun h ↦
      S.evXY_derivative_ne_zero (by rw [← S.coe_evT, h]; rfl)
    have hB' : ((derivative S.F).map g).eval Y ≠ 0 := by
      rw [← S.embG_evT g hg Y hY]
      exact (map_ne_zero_iff _ (S.embG_injective g hg Y hY)).mpr hB
    rw [e, e2, map_div₀, map_neg, S.embG_evT, S.embG_evT, S.embG_gen]
    have hφ : ∀ P, dS s (g P) = g (implicitDeriv ω P) := fun P ↦ by
      rw [hgX, dS_substHomW hK ω s Xh hXh, hgX, implicitDeriv_eq]
    set D0 : LaurentSeries K →+ LaurentSeries K :=
      AddMonoidHom.mk' (dS s) (fun a b ↦ map_add _ a b) with hD0
    have hL : IsLeibniz D0 := fun a b ↦ by
      simp only [hD0, AddMonoidHom.mk'_apply, Derivation.leibniz, smul_eq_mul]
    have hd := derivation_eval_mapW ω D0 hL g hφ S.F Y
    have hD0Y : D0 Y = dS s Y := rfl
    rw [hD0Y] at hd
    rw [hY, map_zero] at hd
    rw [div_eq_iff hB']
    linear_combination hd
  | algebraMap a =>
    have e1 : (⟨(algebraMap C⟮S.x⟯ L a)′, hdc _ (IntermediateField.algebraMap_mem _ a)⟩ :
        C⟮S.x⟯⟮S.y⟯) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨(a : L)′, hcl _ a.2⟩ := rfl
    have e2 : (⟨algebraMap C⟮S.x⟯ L a, IntermediateField.algebraMap_mem _ a⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := rfl
    rw [e1, e2, S.embG_algebraMap, S.embG_algebraMap]
    exact S.embXG_dSW' ω hx hK s Xh hXh g hg hgX (a : L) a.2
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

end CurveData

end EmbW

end Curves
