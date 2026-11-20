import RischTragerBronstein.Mixed.KECore
import RischTragerBronstein.Mixed.KLDecide
import RischTragerBronstein.Algebraic.EllLog
import RischTragerBronstein.Computable.PrimNElem

/-!
# Square roots over an exponential level: the decision is correct

`keDecide_correct`: whenever `keDecide` answers `some b`, `∫ B(t) θ / tᵏ` (`θ² = A(t)`, `t` an
exponential level of a certified tower) is elementary iff `b = true`.

* `sqrt_ext`: a finite (hence elementary) extension containing a square root of a rational `κ`;
* `hei_colIn`: `c B_W y = c W′/W − (c/2) N′/N` (`N = W₀² − W₁² P`) is elementary, for constant `c`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

universe v

/-- **Adjoining `√κ`** (`κ ∈ ℚ`, `κ ≠ 0`): a finite, hence elementary, extension with a constant
square root of `κ`. -/
theorem sqrt_ext (E : Type v) [Field E] [Differential E] [CharZero E] (κ : ℚ) (hκ : κ ≠ 0) :
    ∃ (E₂ : Type v) (_ : Field E₂) (_ : Differential E₂) (_ : Algebra E E₂)
      (_ : DifferentialAlgebra E E₂), IsElementaryExtension E E₂ ∧ Algebra.IsAlgebraic E E₂ ∧
        ∃ s : E₂, s ^ 2 = κ ∧ s′ = 0 := by
  set q : E[X] := X ^ 2 - Polynomial.C (κ : E)
  letI : Differential (SplittingField q) := differentialFiniteDimensional E (SplittingField q)
  haveI : DifferentialAlgebra E (SplittingField q) := differentialAlgebraFiniteDimensional
  haveI : CharZero (SplittingField q) :=
    charZero_of_injective_algebraMap (algebraMap E (SplittingField q)).injective
  have hdeg : (q.map (algebraMap E (SplittingField q))).degree ≠ 0 := by
    rw [degree_map, degree_X_pow_sub_C (by norm_num)]; norm_num
  obtain ⟨r, hr⟩ := (SplittingField.splits q).exists_eval_eq_zero hdeg
  have hr2 : r ^ 2 = (κ : SplittingField q) := by
    simp only [q, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      eval_sub, eval_pow, eval_X, eval_C, map_ratCast] at hr
    linear_combination hr
  refine ⟨SplittingField q, inferInstance, inferInstance, inferInstance, inferInstance,
    isElementaryExtension_of_finiteDimensional, Algebra.IsAlgebraic.of_finite _ _, r, hr2, ?_⟩
  have hr0 : r ≠ 0 := fun h ↦ by
    rw [h, zero_pow two_ne_zero] at hr2
    exact hκ (by exact_mod_cast hr2.symm)
  have hd := congrArg (fun w ↦ w′) hr2
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
  rw [Tower.NestP.deriv_ratCastK (K := SplittingField q) κ] at hd
  have : (2 : SplittingField q) * r ≠ 0 := mul_ne_zero two_ne_zero hr0
  have h2 : ((2 : ℕ) : SplittingField q) * r ^ (2 - 1) * r′ = 0 := by
    rw [← hd]; ring
  norm_num at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hr0
  · exact h2

/-- **The logarithmic column is elementary**: `c B y = c W′/W − (c/2) N′/N`. -/
theorem hei_colIn {F : Type*} [Field F] [Differential F] [CharZero F] (y W0 W1 P r : F)
    (hy : y ^ 2 = P) (hyd : y′ = r * y) (hNm : W0 ^ 2 - W1 ^ 2 * P ≠ 0) (c : F) (hc : c′ = 0) :
    HasElementaryIntegralIn (c * ((W0 * (W1′ + W1 * r) - W0′ * W1) / (W0 ^ 2 - W1 ^ 2 * P) * y)) := by
  have hW : W0 + W1 * y ≠ 0 := by
    intro h0; apply hNm
    rw [← hy, show W0 = -(W1 * y) by linear_combination h0]; ring
  have hab := logDeriv_ab (y := y) W0 W1 P r hy hyd hNm
  have hP' : P′ = 2 * r * P := by
    rw [← hy, Derivation.leibniz_pow, hyd]; simp; ring
  have hN : logDeriv (W0 ^ 2 - W1 ^ 2 * P) =
      2 * ((W0 * W0′ - W1 * (W1′ + W1 * r) * P) / (W0 ^ 2 - W1 ^ 2 * P)) := by
    unfold logDeriv
    rw [map_sub, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, hP']
    simp only [smul_eq_mul, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  have hc2 : (-(c / 2))′ = 0 := by
    rw [map_neg, div_eq_mul_inv, Derivation.leibniz, hc, Derivation.leibniz_inv,
      show (2 : F) = ((2 : ℕ) : F) by norm_num, Derivation.map_natCast]
    simp
  have := hasElementaryIntegralIn_logDeriv₂ c (-(c / 2)) (W0 + W1 * y) (W0 ^ 2 - W1 ^ 2 * P) hc hc2
    hW hNm
  rw [hab, hN] at this
  convert this using 1
  ring

end Differential

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **A solution of the Risch equation gives an antiderivative.** -/
theorem ke_backward_plain (m : ℕ) (hTr : T.Tr (m + 1)) (A B : GPoly (LC m)) (k l : ℕ) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (h : rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) ((B, denC Fc ks m k l A) : LC (m + 1)) = true) :
    HasElementaryIntegralIn (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) := by
  obtain ⟨z, hz⟩ := (T.rdeOKFr_iff (m + 1) hTr _ hspec _).mpr h
  have hzL := congrArg Subtype.val hz
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
    T.sem_frac_code m hTr, T.evP_denC m hTr.of_succ] at hzL
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (z : L) 1
  simp only [pow_one] at h1
  rw [show T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = ((z : L) * θ)′ by rw [h1, ← hzL]]
  exact hasElementaryIntegralIn_deriv _

lemma evP_mapMul (m : ℕ) (h : T.Tr m) (c : LC m) (A : GPoly (LC m)) :
    T.evP m (A.map ((MO Fc ks m).mul c)) = T.ev m c * T.evP m A := by
  have e : A.map ((MO Fc ks m).mul c) = GPoly.smul (MO Fc ks m) c A := rfl
  rw [e, ← T.aeval_toPoly (T.MP m h) (T.sem_MP m h), ← T.aeval_toPoly (T.MP m h) (T.sem_MP m h),
    GPoly.toPoly_smul, map_mul, aeval_C, IntermediateField.algebraMap_apply, T.sem_MP m h]

/-- **The logarithmic column times `θ` is elementary** (over `L(√κ)`, then over `L`). -/
theorem hcolIn (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m)) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hA0 : T.evP m A ≠ 0) (zc : LC m) (hz0 : T.ev m zc ≠ 0) (κ : ℚ) (hκ : κ ≠ 0)
    (W0 W1 : GPoly (LC m)) (q : ℚ) :
    HasElementaryIntegralIn ((q : L) * (T.ev (m + 1) (logCol Fc ks m (A.map ((MO Fc ks m).mul
      ((MO Fc ks m).mul ((MO Fc ks m).mul zc zc) (mcst Fc ks m κ⁻¹)))) W0 W1 zc) * θ)) := by
  rw [T.ev_logCol m h]
  set Pv := T.evP m (A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul zc zc)
    (mcst Fc ks m κ⁻¹)))) with hPv
  have hPvA : Pv = T.ev m zc ^ 2 / κ * T.evP m A := by
    rw [hPv, T.evP_mapMul m h.of_succ]
    congr 1
    rw [← T.sem_MP m h.of_succ, (T.MP m h.of_succ).sem_mul, (T.MP m h.of_succ).sem_mul,
      T.sem_mcst, IntermediateField.coe_mul, IntermediateField.coe_mul, T.sem_MP m h.of_succ]
    push_cast; ring
  set W0v := T.evP m W0 with hW0v
  set W1v := T.evP m W1 with hW1v
  set zv := T.ev m zc with hzv
  set rv := (1 / 2 : L) * (Pv′ * Pv⁻¹) with hrvdef
  by_cases hN : W0v * W0v - W1v * W1v * Pv = 0
  · rw [hN, inv_zero, mul_zero, zero_mul, zero_mul, mul_zero]
    have : (0 : L) = (0 : L)′ := by simp
    rw [this]; exact hasElementaryIntegralIn_deriv 0
  obtain ⟨E₂, _, _, _, _, -, halg, s, hs2, hs'⟩ := sqrt_ext L κ hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap L E₂).injective
  refine HasElementaryIntegralIn.of_isAlgebraic halg ?_
  set ψ := algebraMap L E₂
  have hs0 : s ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow two_ne_zero] at hs2; exact hκ (by exact_mod_cast hs2.symm)
  have hψd : ∀ w : L, (ψ w)′ = ψ w′ := fun w ↦ deriv_algebraMap w
  set Y := ψ (zv * θ) / s with hY
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
  have hPv0 : Pv ≠ 0 := by
    rw [hPvA]; exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 hz0) (by exact_mod_cast hκ)) hA0
  have hY2 : Y ^ 2 = ψ Pv := by
    rw [hY, div_pow, hs2, ← map_pow, hPvA, mul_pow, hθ]
    simp only [map_mul, map_div₀, map_pow, map_ratCast]
    field_simp
  have hθd : θ′ = (1 / 2 : L) * logDeriv (T.evP m A) * θ := by
    have := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 1 1
    simp only [one_mul, pow_one, Derivation.map_one_eq_zero, zero_add] at this
    rw [this]; push_cast; ring
  have hY0 : Y ≠ 0 := by
    rw [hY]
    exact div_ne_zero ((map_ne_zero ψ).mpr (mul_ne_zero hz0 hθ0)) hs0
  have hYd : Y′ = ψ rv * Y := by
    have hd := congrArg (fun w ↦ w′) hY2
    simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, hψd] at hd
    have hPψ : ψ Pv ≠ 0 := (map_ne_zero ψ).mpr hPv0
    have hrv : ψ rv = (1 / 2 : E₂) * (ψ Pv′ * (ψ Pv)⁻¹) := by
      simp only [rv, map_mul, map_div₀, map_one, map_ofNat, map_inv₀]
    rw [hrv, ← hY2, ← hd]
    field_simp
    ring
  have hNm : ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv ≠ 0 := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub]
    exact (map_ne_zero ψ).mpr (by rw [pow_two, pow_two]; exact hN)
  have hcs : (ψ (q : L) * s)′ = 0 := by
    rw [Derivation.leibniz, hs', map_ratCast, Tower.NestP.deriv_ratCastK (K := E₂) q]; simp
  have := hei_colIn Y (ψ W0v) (ψ W1v) (ψ Pv) (ψ rv) hY2 hYd hNm (ψ (q : L) * s) hcs
  convert this using 1
  have hN' : ψ W0v * ψ W0v - ψ W1v * ψ W1v * ψ Pv ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero ψ).mpr hN
  rw [hY]
  simp only [map_mul, map_sub, map_add, map_inv₀, hψd]
  rw [div_eq_mul_inv (ψ W0v * _ - _), show ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv =
    ψ W0v * ψ W0v - ψ W1v * ψ W1v * ψ Pv by ring]
  field_simp

/-- **A solution of the parametric equation gives an antiderivative.** -/
theorem ke_backward_param [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hTr : T.Tr (m + 1))
    (A B : GPoly (LC m)) (k l : ℕ) (θ : L) (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0)
    (zc : LC m) (hz0 : T.ev m zc ≠ 0) (κ : ℚ) (hκ : κ ≠ 0) (W0 W1 : GPoly (LC m))
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (h : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) [((B, denC Fc ks m k l A) : LC (m + 1)),
      normC Fc (m + 1) (logCol Fc ks m (A.map ((MO Fc ks m).mul ((MO Fc ks m).mul
        ((MO Fc ks m).mul zc zc) (mcst Fc ks m κ⁻¹)))) W0 W1 zc)]).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true) :
    HasElementaryIntegralIn (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) := by
  obtain ⟨r, hr, hr0⟩ := List.any_eq_true.mp h
  have hq0 : r.1.getD 0 0 ≠ 0 := of_decide_eq_true hr0
  set col := normC Fc (m + 1) (logCol Fc ks m (A.map ((MO Fc ks m).mul ((MO Fc ks m).mul
        ((MO Fc ks m).mul zc zc) (mcst Fc ks m κ⁻¹)))) W0 W1 zc) with hcol
  set rhs : LC (m + 1) := (B, denC Fc ks m k l A) with hrhs
  have hs := hspec.sound [rhs, col] r hr
  have hsQ : sQ (T.MP (m + 1) hTr) r.1 [rhs, col] =
      ((r.1.getD 0 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem rhs +
        ((r.1.getD 1 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem col := by
    simp [sQ, Finset.sum_range_succ]
  rw [hsQ] at hs
  have hsL := congrArg Subtype.val hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv] at hsL
  rw [T.sem_kpFr m hTr, hrhs, T.sem_frac_code m hTr, T.evP_denC m hTr.of_succ] at hsL
  simp only [T.sem_MP (m + 1) hTr] at hsL
  rw [hcol, T.ev_normC (m + 1) hTr] at hsL
  set a : L := T.ev (m + 1) r.2
  set q0 : ℚ := r.1.getD 0 0
  set q1 : ℚ := r.1.getD 1 0
  set colv := T.ev (m + 1) (logCol Fc ks m (A.map ((MO Fc ks m).mul ((MO Fc ks m).mul
        ((MO Fc ks m).mul zc zc) (mcst Fc ks m κ⁻¹)))) W0 W1 zc)
  have hq0L : (q0 : L) ≠ 0 := by exact_mod_cast hq0
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (a / q0) 1
  simp only [pow_one] at h1
  have hf : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = ((a / q0) * θ)′ + ((-q1 / q0 : ℚ) : L) * (colv * θ) := by
    rw [h1]
    have hq0d : ((q0 : L))′ = 0 := Tower.NestP.deriv_ratCastK (K := L) q0
    have hd : (a / (q0 : L))′ = a′ / q0 := by
      rw [div_eq_mul_inv a, Derivation.leibniz, Derivation.leibniz_inv, hq0d, div_eq_mul_inv]
      simp only [smul_zero, smul_eq_mul, mul_zero, zero_add, neg_zero]
      ring
    rw [hd]
    generalize T.evP m B / (T.ts m ^ k * T.evP m A ^ l) = R at hsL ⊢
    push_cast at hsL ⊢
    field_simp
    linear_combination (-2 * θ : L) * hsL
  rw [hf]
  exact (hasElementaryIntegralIn_deriv _).add
    (T.hcolIn m hTr A θ hθ hA0 zc hz0 κ hκ W0 W1 (-q1 / q0))

/-- **Lifting an elementary integral**: the Liouville data in an elementary extension containing
`√κ`, for the lifted realization. -/
theorem ke_lift (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (k l : ℕ) (hf : HasElementaryIntegral (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ))
    (κ : ℚ) (hκ : κ ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Differential E) (_ : CharZero E)
      (TE : MTower Fc ks (constants E) E) (θE s : E) (ι : Type) (sI : Finset ι) (c u : ι → E)
      (v : E), TE.n = m + 1 ∧ θE ^ 2 = TE.evP m A ∧ s ^ 2 = κ ∧ s′ = 0 ∧
      (∀ i ∈ sI, (c i)′ = 0) ∧
      (∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE}) ∧
      v ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} ∧
      TE.evP m B / (TE.ts m ^ k * TE.evP m A ^ l) * θE = v′ + ∑ i ∈ sI, c i * logDeriv (u i) := by
  classical
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨E₂, _, _, _, _, hE₁₂, -, s, hs2, hs'⟩ := sqrt_ext E₁ κ hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap E₁ E₂).injective
  letI : Algebra L E₂ := ((algebraMap E₁ E₂).comp (algebraMap L E₁)).toAlgebra
  haveI : IsScalarTower L E₁ E₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI hDA₂ : DifferentialAlgebra L E₂ :=
    ⟨fun z ↦ by
      change (algebraMap E₁ E₂ (algebraMap L E₁ z))′ = algebraMap E₁ E₂ (algebraMap L E₁ z′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hE₂ : IsElementaryExtension L E₂ := hE₁.trans hE₁₂
  have hg₂ : (algebraMap E₁ E₂ g)′ = algebraMap L E₂ (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) := by
    rw [deriv_algebraMap, hg]; rfl
  obtain ⟨ι, sI, c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₂ _ _ hg₂
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₂
  set ψ := algebraMap L E₂ with hψ
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    induction P with
    | nil => simp [evP, evPL]
    | cons a P ih =>
      simp only [evP, evPL, List.foldr_cons] at ih ⊢
      rw [ih, map_add, map_mul, hTEts m, ← hTEev m a]
  set θE := ψ θ
  have hT1 : ∀ w ∈ TE.F (m + 1), w ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} :=
    fun w hw ↦ IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : TE.F (m + 1))
  have hLT : ∀ z : L, ψ z ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hT1 _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₂, w ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := TE.hconst w hw
      rw [← hc0]
      exact hT1 _ (TE.const_mem (m + 1) c0)
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  refine ⟨E₂, inferInstance, inferInstance, inferInstance, TE, θE, s, ι, sI, c, u, v,
    by rw [hTEn, hn], by rw [hPE, ← map_pow, hθ], hs2, hs', fun i hi ↦ (hdata i hi).1,
    fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩, hCT _ hv, ?_⟩
  rw [hPE, hPE, hTEts m, add_comm, ← heqL]
  simp only [map_mul, map_div₀, map_pow]
  rfl

lemma toPoly_eval_zero (m : ℕ) (h : T.Tr m) (A : GPoly (LC m)) :
    (GPoly.toPoly (T.MP m h) A).eval 0 = (T.MP m h).sem (A.getD 0 (MO Fc ks m).zero) := by
  cases A with
  | nil => simp [(T.MP m h).sem_zero]
  | cons a A => simp

open Classical in
/-- **Forward, `A(0)` not a constant times a square**: the Risch equation has a solution. -/
theorem ke_forward_N (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = none)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (B : GPoly (LC m)) (k l : ℕ) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) ((B, denC Fc ks m k l A) : LC (m + 1)) = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  set a0 := A.getD 0 (MO Fc ks m).zero with ha0def
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hp0v : S.p.eval 0 = (T.MP m hTm).sem a0 := by
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have ha0v : (T.MP m hTm).sem a0 ≠ 0 := fun h0 ↦ by
    rw [← (T.MP m hTm).isZero_iff] at h0; rw [h0] at ha0; exact Bool.noConfusion ha0
  obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (T.F m) (AlgebraicClosure (T.F m)) (S.p.eval 0)) two_pos
  have hβ0 : β₀ ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow two_ne_zero] at hβ₀
    have := (map_eq_zero_iff (algebraMap (T.F m) (AlgebraicClosure (T.F m)))
      (algebraMap (T.F m) (AlgebraicClosure (T.F m))).injective).mp hβ₀.symm
    rw [hp0v] at this
    exact ha0v this
  have hns : ∀ c : T.F m, algebraMap (T.F m) (AlgebraicClosure (T.F m)) c ≠ β₀ := by
    intro cc hcc
    have hc2 : cc ^ 2 = (T.MP m hTm).sem a0 := by
      apply (algebraMap (T.F m) (AlgebraicClosure (T.F m))).injective
      rw [map_pow, hcc, hβ₀, hp0v]
    have hcc0 : cc ≠ 0 := fun h0 ↦ ha0v (by rw [← hc2, h0, zero_pow two_ne_zero])
    obtain ⟨r, hr, hr0⟩ := T.halfKer_complete (lv := lv) m hTm (halfFr Fc ks m a0)
      (MSm.rde _ (T.halfFr_ok m hTm a0)) cc⁻¹ (inv_ne_zero hcc0) (by
        apply Subtype.ext
        have hsh := T.sem_halfFr m hTm a0
        rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, hsh,
          ← T.sem_MP m hTm a0, ← hc2]
        have hccL : ((cc : T.F m) : L) ≠ 0 := fun h0 ↦ hcc0 (Subtype.ext h0)
        rw [IntermediateField.coe_inv, IntermediateField.coe_pow, logDeriv, Derivation.leibniz_inv,
          Derivation.leibniz_pow]
        simp only [smul_eq_mul, nsmul_eq_mul, IntermediateField.coe_zero]
        field_simp
        ring)
    have := List.find?_eq_none.mp hfind r hr
    simp [hr0] at this
  have hnt := S.nontors_of_nonsquare (K := AlgebraicClosure (T.F m)) rfl β₀
    (by rw [hβ₀]) hβ0 hns
  obtain ⟨aa, haa, hae⟩ := T.ke_core_nontors m hTr A hsq hdegA θ hθ 1 one_ne_zero MS.hyp
    (by omega) hk hcopA β₀ (by rw [hβ₀]) hβ0 hnt B k l sI c u hcd hu v hv heq
  have hspec := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  refine (T.rdeOKFr_iff (m + 1) hTr _ hspec _).mp ⟨⟨aa, haa⟩, Subtype.ext ?_⟩
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
    T.sem_frac_code m hTr, T.evP_denC m hTm, ← hae]
  push_cast
  ring

section Helpers

variable [Fact (Irreducible (toPoly (fKc Fc)))]

/-- The evaluation `Kₘ → Fₘ`. -/
noncomputable def psiF (m : ℕ) (h : T.Tr m) : KF Fc m →+* T.F m where
  toFun z := ⟨T.psiC m h z, T.psiC_mem m h z⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

lemma psiF_trC (m : ℕ) (h : T.Tr m) (q : LC m) : T.psiF m h (trC Fc m q) = (T.MP m h).sem q :=
  Subtype.ext (by rw [T.sem_MP m h]; exact T.psiC_trC m h q)

lemma gtoPoly_eq {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α}
    (M : CField α K O) (p : GPoly α) : GPoly.toPoly M p = CPoly.toPoly (p.map M.sem) := by
  induction p with
  | nil => rfl
  | cons a p ih => rw [GPoly.toPoly_cons, List.map_cons, toPoly_cons, ih]

lemma toPoly_trC_map (m : ℕ) (h : T.Tr m) (P : GPoly (LC m)) :
    (CPoly.toPoly (P.map (trC Fc m))).map (T.psiF m h) = GPoly.toPoly (T.MP m h) P := by
  rw [← Sup.toPoly_mapHom, List.map_map, gtoPoly_eq]
  congr 1
  exact List.map_congr_left fun q _ ↦ T.psiF_trC m h q

omit [Fact (Irreducible (toPoly (fKc Fc)))] in
lemma squarefree_of_map {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (f : K[X])
    (h : Squarefree (f.map φ)) : Squarefree f := fun x hx ↦
  (Polynomial.isUnit_map φ).mp (h (x.map φ) (by rw [← Polynomial.map_mul]; exact Polynomial.map_dvd φ hx))

end Helpers

/-- **The kernel element**: `z ≠ 0` and `z² a₀ = κ` (rational, non-zero). -/
theorem ke_z_facts (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (A : GPoly (LC m))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (q : List ℚ) (z : LC m)
    (hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = some (q, z)) :
    T.ev m z ≠ 0 ∧
      T.ev m z ^ 2 * T.ev m (A.getD 0 (MO Fc ks m).zero) =
        ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0 : ℚ) ∧
      (ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0 ≠ 0 := by
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hTm : T.Tr m := MSm.hyp.tr
  set a0 := A.getD 0 (MO Fc ks m).zero
  have hmem := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hp
  have hz0 : (T.MP m hTm).sem z ≠ 0 := fun h0 ↦ by
    rw [← (T.MP m hTm).isZero_iff] at h0; rw [h0] at hp; exact Bool.noConfusion hp
  have ha0v : (T.MP m hTm).sem a0 ≠ 0 := fun h0 ↦ by
    rw [← (T.MP m hTm).isZero_iff] at h0; rw [h0] at ha0; exact Bool.noConfusion ha0
  have hsol := T.halfKer_sound (lv := lv) m hTm (halfFr Fc ks m a0)
    (MSm.rde _ (T.halfFr_ok m hTm a0)) _ hmem
  have hsolL := congrArg Subtype.val hsol
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_halfFr m hTm,
    T.sem_MP m hTm, IntermediateField.coe_zero] at hsolL
  have hzL : T.ev m z ≠ 0 := by rw [← T.sem_MP m hTm]; exact fun h0 ↦ hz0 (Subtype.ext h0)
  have haL : T.ev m a0 ≠ 0 := by rw [← T.sem_MP m hTm]; exact fun h0 ↦ ha0v (Subtype.ext h0)
  have hcst : ((T.MP m hTm).sem ((MO Fc ks m).mul ((MO Fc ks m).mul z z) a0))′ = 0 := by
    apply Subtype.ext
    rw [MTower.coe_deriv, (T.MP m hTm).sem_mul, (T.MP m hTm).sem_mul, IntermediateField.coe_mul,
      IntermediateField.coe_mul, T.sem_MP m hTm, T.sem_MP m hTm, IntermediateField.coe_zero]
    rw [Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have hz' : (T.ev m z)′ = -(1 / 2 : L) * logDeriv (T.ev m a0) * T.ev m z := by
      linear_combination hsolL
    rw [hz']
    unfold logDeriv
    field_simp
    ring
  have hκ := T.ratValC_of_const m hTm _ hcst
  have hκL := congrArg Subtype.val hκ
  rw [(T.MP m hTm).sem_mul, (T.MP m hTm).sem_mul, IntermediateField.coe_mul,
    IntermediateField.coe_mul, T.sem_MP m hTm, T.sem_MP m hTm] at hκL
  push_cast at hκL
  refine ⟨hzL, by rw [← hκL]; ring, fun h0 ↦ ?_⟩
  rw [h0, Rat.cast_zero] at hκL
  exact mul_ne_zero (mul_ne_zero hzL hzL) haL hκL

/-- **The normalized curve**: `μ = z/√κ`, `Â = μ² A` with `Â(0) = 1`, and its code over `Kₘ`. -/
theorem ke_S_setup [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (q : List ℚ) (z : LC m)
    (hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = some (q, z)) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (s : L) (hs2 : s ^ 2 = ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0 : ℚ)) (hs' : s′ = 0) :
    ∃ (μ : T.F m) (hμ : μ ≠ 0), ((μ : T.F m) : L) = T.ev m z / s ∧
      (T.keS m hTr A hsq hdegA θ hθ μ hμ).p.eval 0 = 1 ∧
      (T.keS m hTr A hsq hdegA θ hθ μ hμ).p =
        (CPoly.toPoly (CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m)))).map
          (T.psiF m hTr.of_succ) := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  obtain ⟨hz0, hκrel, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q z hfind
  set κ : ℚ := (ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
    (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκdef
  have hκL : (κ : L) ≠ 0 := by exact_mod_cast hκ0
  have hs0 : s ≠ 0 := fun h0 ↦ hκL (by rw [← hs2, h0, zero_pow two_ne_zero])
  obtain ⟨c0, hc0⟩ := T.hconst s hs'
  have hsF : s ∈ T.F m := hc0 ▸ T.const_mem m c0
  set sF : T.F m := ⟨s, hsF⟩
  set zF : T.F m := ⟨T.ev m z, T.ev_mem m z⟩
  have hsF0 : sF ≠ 0 := fun h0 ↦ hs0 (congrArg Subtype.val h0)
  have hzF0 : zF ≠ 0 := fun h0 ↦ hz0 (congrArg Subtype.val h0)
  refine ⟨zF / sF, div_ne_zero hzF0 hsF0, rfl, ?_, ?_⟩
  · change (Polynomial.C ((zF / sF) ^ 2) * GPoly.toPoly (T.MP m hTm) A).eval 0 = 1
    rw [eval_mul, eval_C, T.toPoly_eval_zero m hTm]
    apply Subtype.ext
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_div,
      T.sem_MP m hTm, IntermediateField.coe_one]
    change (T.ev m z / s) ^ 2 * T.ev m (A.getD 0 (MO Fc ks m).zero) = 1
    rw [div_pow, hs2, div_mul_eq_mul_div, hκrel, div_self hκL]
  · rw [CPoly.toPoly_trim, T.toPoly_trC_map m hTm]
    have e : A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m κ⁻¹))) = GPoly.smul (MO Fc ks m) ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m κ⁻¹)) A := rfl
    rw [e, GPoly.toPoly_smul]
    change Polynomial.C ((zF / sF) ^ 2) * _ = _
    congr 2
    apply Subtype.ext
    rw [(T.MP m hTm).sem_mul, (T.MP m hTm).sem_mul, T.sem_mcst, IntermediateField.coe_mul,
      IntermediateField.coe_mul, T.sem_MP m hTm, IntermediateField.coe_pow,
      IntermediateField.coe_div]
    change (T.ev m z / s) ^ 2 = T.ev m z * T.ev m z * (((κ⁻¹ : ℚ) : T.F m) : L)
    push_cast
    rw [div_pow, hs2]
    ring

omit [CharZero L] in
lemma fK_facts {K C' : Type*} [Field K] [DecidableEq K] [Field C'] (φ : K →+* C') (fK : CPoly K)
    (htrim : CPoly.trim fK = fK) (p : C'[X]) (hpf : p = (toPoly fK).map φ) (hp0 : p.eval 0 = 1)
    (hsq : Squarefree p) (hcop : Nat.Coprime 2 p.natDegree) :
    (toPoly fK).natDegree = fK.length - 1 ∧ (toPoly fK).eval 0 = 1 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime 2 (fK.length - 1) := by
  have hne : toPoly fK ≠ 0 := fun h0 ↦ by rw [hpf, h0, Polynomial.map_zero, eval_zero] at hp0; simp at hp0
  have htne : CPoly.trim fK ≠ [] := fun h0 ↦ hne ((CPoly.trim_eq_nil_iff fK).mp h0)
  have hlen := CPoly.length_trim htne
  rw [htrim] at hlen
  have hdeg : (toPoly fK).natDegree = fK.length - 1 := by omega
  have hpdeg : p.natDegree = (toPoly fK).natDegree := by
    rw [hpf, natDegree_map_eq_of_injective φ.injective]
  refine ⟨hdeg, ?_, squarefree_of_map φ _ (hpf ▸ hsq), by rw [← hdeg, ← hpdeg]; exact hcop⟩
  apply φ.injective
  rw [map_one, ← hp0, hpf, eval_map, ← map_zero φ, eval₂_at_apply]

open Classical in
/-- **Forward, normalized curve, no torsion**: the Risch equation has a solution. -/
theorem ke_forward_S_nontors [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (q : List ℚ) (z : LC m)
    (hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = some (q, z)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cp : CertProv (KF Fc m)) (htors : torsOracleC (redAtKF Fc m rs) cp ps bound
      (CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))) 2
      (gammaL ![(0 : KF Fc m)] ![1] ![1] 1) = some none)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (B : GPoly (LC m)) (k l : ℕ) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (s : L) (hs2 : s ^ 2 = ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0 : ℚ)) (hs' : s′ = 0) :
    rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) ((B, denC Fc ks m k l A) : LC (m + 1)) = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  obtain ⟨μ, hμ, -, hp0, hpf⟩ := T.ke_S_setup hmon hdeg m hn hc hTr A hsq hdegA hcopA ha0 q z
    hfind θ hθ s hs2 hs'
  set S := T.keS m hTr A hsq hdegA θ hθ μ hμ with hS
  set fK := CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m)) with hfK
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ μ hμ hcopA
  obtain ⟨hd, hf0, hsqK, hcop2⟩ := fK_facts (T.psiF m hTm) fK (CPoly.trim_trim _) S.p hpf hp0
    S.hsq hcopS
  have hspec := torsOracleC_spec (redAtKF Fc m rs) cp (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
    ps bound hsqK hcop2
  have hnot := (hspec 1 ![(0 : KF Fc m)] ![1] ![1] (fun q ↦ by fin_cases q; simp [hf0])
    (fun a b _ ↦ Subsingleton.elim a b)).2 htors
  have hnF : ((S.n : ℕ) : KF Fc m) ≠ 0 := by
    show ((2 : ℕ) : KF Fc m) ≠ 0; norm_num
  have hnt := S.not_isPrincipalS_of (K := AlgebraicClosure (T.F m)) (T.psiF m hTm) fK hpf hd hcopS
    hf0 hnF hnot
  obtain ⟨aa, haa, hae⟩ := T.ke_core_nontors m hTr A hsq hdegA θ hθ μ hμ MS.hyp (by omega) hk
    hcopA 1 (by rw [hp0, map_one, one_pow]) one_ne_zero hnt B k l sI c u hcd hu v hv heq
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  refine (T.rdeOKFr_iff (m + 1) hTr _ hspecA _).mp ⟨⟨aa, haa⟩, Subtype.ext ?_⟩
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
    T.sem_frac_code m hTr, T.evP_denC m hTm, ← hae]
  push_cast
  ring

lemma evP_unTr_map [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hTm : T.Tr m)
    (l : List (KF Fc m)) :
    T.evP m (l.map (unTr Fc m)) = aeval (T.ts m) ((toPoly l).map (T.psiF m hTm)) := by
  induction l with
  | nil => simp [evP, evPL]
  | cons a l ih =>
    simp only [evP, evPL, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, map_add, map_mul, aeval_C, aeval_X]
    congr 1
    exact T.ev_unTr m hTm a

lemma elemW_two (S : SuperData (T.F m) L) (hS2 : S.n = 2) (W : (T.F m)[X][X]) :
    ((S.elemW W : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = aeval S.x (W.coeff 0) + aeval S.x (W.coeff 1) * S.y := by
  rw [SuperData.elemW, hS2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one,
    IntermediateField.coe_add, IntermediateField.coe_mul, S.polyX_coe, AdjoinSimple.coe_gen]

open Classical in
/-- **Forward, normalized curve, torsion**: the parametric equation has a solution with the
coefficient of `B/tᵏ` non-zero. -/
theorem ke_forward_S_tors [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (q : List ℚ) (z : LC m)
    (hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = some (q, z)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cp : CertProv (KF Fc m)) (N : ℕ)
    (htors : torsOracleC (redAtKF Fc m rs) cp ps bound
      (CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))) 2
      (gammaL ![(0 : KF Fc m)] ![1] ![1] 1) = some (some N))
    (Wb : Sup.BPoly (KF Fc m))
    (hwit : witW (CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))) 2
      ((CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))).length - 1)
      ![(0 : KF Fc m)] ![1] ![1] N = some Wb)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (B : GPoly (LC m)) (k l : ℕ) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (s : L) (hs2 : s ^ 2 = ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0 : ℚ)) (hs' : s′ = 0) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) [((B, denC Fc ks m k l A) : LC (m + 1)),
      normC Fc (m + 1) (logCol Fc ks m (A.map ((MO Fc ks m).mul ((MO Fc ks m).mul
        ((MO Fc ks m).mul z z) (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul
          ((MO Fc ks m).mul z z) (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹))))
        ((Wb.getD 0 []).map (unTr Fc m)) ((Wb.getD 1 []).map (unTr Fc m)) z)]).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  obtain ⟨μ, hμ, hμv, hp0, hpf⟩ := T.ke_S_setup hmon hdeg m hn hc hTr A hsq hdegA hcopA ha0 q z
    hfind θ hθ s hs2 hs'
  set S := T.keS m hTr A hsq hdegA θ hθ μ hμ with hS
  set κ : ℚ := (ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
    (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκdef
  set Ahat := A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
    (mcst Fc ks m κ⁻¹))) with hAhat
  set fK := CPoly.trim (Ahat.map (trC Fc m)) with hfK
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ μ hμ hcopA
  obtain ⟨hd, hf0, hsqK, hcop2⟩ := fK_facts (T.psiF m hTm) fK (CPoly.trim_trim _) S.p hpf hp0
    S.hsq hcopS
  have hspec := torsOracleC_spec (redAtKF Fc m rs) cp (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
    ps bound hsqK hcop2
  have hN1 := ((hspec 1 ![(0 : KF Fc m)] ![1] ![1] (fun q ↦ by fin_cases q; simp [hf0])
    (fun a b _ ↦ Subsingleton.elim a b)).1 N htors).1
  have hnF : ((S.n : ℕ) : KF Fc m) ≠ 0 := by
    show ((2 : ℕ) : KF Fc m) ≠ 0; norm_num
  obtain ⟨hWne, hWord⟩ := S.ordAt_witW (K := AlgebraicClosure (T.F m)) (T.psiF m hTm) fK hpf hd
    hcopS hf0 hnF N hN1 Wb hwit
  set Wp := (toB Wb).map (mapRingHom (T.psiF m hTm)) with hWp
  set W0 := aeval (T.ts m) (Wp.coeff 0) with hW0
  set W1 := aeval (T.ts m) (Wp.coeff 1) with hW1
  have hW0c : T.evP m ((Wb.getD 0 []).map (unTr Fc m)) = W0 := by
    rw [T.evP_unTr_map m hTm, hW0, hWp, Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
  have hW1c : T.evP m ((Wb.getD 1 []).map (unTr Fc m)) = W1 := by
    rw [T.evP_unTr_map m hTm, hW1, hWp, Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
  have hWe : ((S.elemW Wp : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = W0 + W1 * S.y := T.elemW_two S rfl Wp
  have hmemx : ∀ P : (T.F m)[X], aeval (T.ts m) P ∈ (T.F m)⟮S.x⟯ := fun P ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) P = aeval S.x P from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x P]
    exact SetLike.coe_mem _
  have hP : aeval (T.ts m) S.p = T.evP m Ahat := by
    rw [hpf, CPoly.toPoly_trim, T.toPoly_trC_map m hTm, T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
  -- the norm is non-zero
  have hNm : W0 ^ 2 - W1 ^ 2 * aeval (T.ts m) S.p ≠ 0 := by
    intro h0
    have hy2 : S.y ^ 2 = aeval (T.ts m) S.p := S.hy
    have hodd : Odd S.p.natDegree := by
      rw [← Nat.coprime_two_left]; exact hcopS
    have hny := not_mem_of_sq_odd (C := T.F m) S.x S.y S.htr S.p hodd hy2
    have hfac : (W0 + W1 * S.y) * (W0 - W1 * S.y) = 0 := by rw [← h0, ← hy2]; ring
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hWne (Subtype.ext (by rw [hWe, h1]; rfl))
    · by_cases hw1 : W1 = 0
      · apply hWne; apply Subtype.ext
        rw [hWe, hw1, zero_mul, add_zero]
        rw [hw1, zero_mul, sub_zero] at h1
        rw [h1]; rfl
      · apply hny
        rw [show S.y = W0 / W1 by field_simp; linear_combination -h1]
        exact div_mem (hmemx _) (hmemx _)
  obtain ⟨aa, haa, e, he, hae⟩ := T.ke_core_tors m hTr A hsq hdegA θ hθ μ hμ MS.hyp (by omega) hk
    hcopA hp0 N hN1 (S.elemW Wp) hWne hWord W0 W1 (hmemx _) (hmemx _) hWe hNm B k l sI c u hcd hu
    v hv heq
  rw [← hS] at hae
  -- the value of the column
  set col := normC Fc (m + 1) (logCol Fc ks m Ahat ((Wb.getD 0 []).map (unTr Fc m))
    ((Wb.getD 1 []).map (unTr Fc m)) z) with hcol
  have hx := T.keS_hx m hTr A hsq hdegA θ hθ μ hμ (by omega) hk
  have hPd : (aeval (T.ts m) S.p)′ = aeval (T.ts m) (mapCoeffs S.p +
      Polynomial.C (T.val m g)′ * X * derivative S.p) := S.deriv_aeval_xW _ hx S.p
  have hP0 : aeval (T.ts m) S.p ≠ 0 := fun h0 ↦ S.htr ⟨S.p, S.hsq.ne_zero, h0⟩
  have hs0 : s ≠ 0 := fun h0 ↦ by
    have := T.ke_z_facts hmon hdeg m hn hc A ha0 q z hfind
    rw [h0, zero_pow two_ne_zero] at hs2
    exact this.2.2 (by exact_mod_cast hs2.symm)
  have hcolv : T.ev (m + 1) col = ((W0 * (W1′ + W1 *
      (aeval (T.ts m) (mapCoeffs S.p + Polynomial.C (T.val m g)′ * X * derivative S.p) /
        ((2 : L) * aeval (T.ts m) S.p))) - W0′ * W1) /
        (W0 ^ 2 - W1 ^ 2 * aeval (T.ts m) S.p)) * T.ev m z := by
    rw [hcol, T.ev_normC (m + 1) hTr, T.ev_logCol m hTr, hW0c, hW1c, ← hP, ← hPd]
    field_simp
  have hμL : ((μ : T.F m) : L) = T.ev m z / s := hμv
  rw [hμL] at hae
  -- the constant `e / s`
  have hes : (e / s)′ = 0 := by
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, he, hs']; simp
  obtain ⟨c0, hc0⟩ := T.hconst (e / s) hes
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  set rhs : LC (m + 1) := (B, denC Fc ks m k l A) with hrhs
  obtain ⟨β, hβ, -⟩ := hspecA.complete [rhs, col] [1, c0] (fun i hi ↦ by
      rcases i with _ | _ | i
      · simp at hi
      · simp at hi
      · rfl) ⟨aa, haa⟩ (by
    apply Subtype.ext
    simp only [sC, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, List.getD_cons_zero, List.getD_cons_succ, IntermediateField.coe_add,
      IntermediateField.coe_mul, MTower.coe_deriv, map_one, one_mul]
    rw [T.sem_kpFr m hTr, hrhs, T.sem_frac_code m hTr, T.evP_denC m hTm, T.sem_MP (m + 1) hTr,
      hcolv]
    change _ = _ + algebraMap Cc L c0 * _
    rw [hc0]
    change aa′ + _ * aa = _
    rw [show (((1 : ℕ) : ℚ) / (2 : ℕ) : L) = (1 / 2 : L) by push_cast; ring, hae]
    field_simp)
  have h0 := hβ 0
  simp only [List.getD_cons_zero] at h0
  by_contra hno
  simp only [List.any_eq_true, not_exists, not_and, decide_eq_true_eq, not_not] at hno
  apply one_ne_zero (α := Cc)
  rw [h0]
  refine Finset.sum_eq_zero fun kk hkk ↦ ?_
  have hmem : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) [rhs, col]).getD kk ([], (MO Fc ks (m + 1)).zero) ∈
      prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) [rhs, col] := by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hkk)]
    exact List.getElem_mem _
  rw [hno _ hmem, map_zero, mul_zero]

open Classical in
/-- **`keDecideC` is correct** (any certificate provider): whenever it answers `some b`, the integral
of `B(t) θ / tᵏ` (`θ² = A(t)`, `t` an exponential level) is elementary exactly when `b = true`. -/
theorem keDecideC_correct [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (b : Bool)
    (hdec : keDecideC Fc ks lv m A B k l ps bound rs cpf = some b) :
    HasElementaryIntegral (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) ↔ b = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  unfold keDecideC at hdec
  dsimp only at hdec
  rcases hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) with _ | ⟨q, z⟩
  · -- no square root of `A(0)`
    rw [hfind] at hdec
    obtain rfl := Option.some.inj hdec
    constructor
    · intro hf
      obtain ⟨E, _, _, _, TE, θE, -, ι, sI, c, u, v, hTEn, hθE, -, -, hcd, hu, hv, heq⟩ :=
        T.ke_lift hmon hdeg m hn hc A θ hθ hgen B k l hf 1 one_ne_zero
      exact TE.ke_forward_N hmon hdeg m hTEn hc hk A hsqc hdegpos hcop ha0 hfind θE hθE B k l sI c u
        hcd hu v hv heq
    · intro h
      exact (T.ke_backward_plain m hTr A B k l θ hθ hA0 hspecA h).hasElementaryIntegral
  · rw [hfind] at hdec
    dsimp only at hdec
    obtain ⟨hz0, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q z hfind
    rcases htors : torsOracleC (redAtKF Fc m rs) (cpf (CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m)))) ps bound
      (CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))) 2
      (gammaL ![(0 : KF Fc m)] ![1] ![1] 1) with _ | _ | N
    · rw [htors] at hdec; exact absurd hdec (by simp)
    · -- no torsion
      rw [htors] at hdec
      obtain rfl := Option.some.inj hdec
      constructor
      · intro hf
        obtain ⟨E, _, _, _, TE, θE, s, ι, sI, c, u, v, hTEn, hθE, hs2, hs', hcd, hu, hv, heq⟩ :=
          T.ke_lift hmon hdeg m hn hc A θ hθ hgen B k l hf _ hκ0
        exact TE.ke_forward_S_nontors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop ha0 q z hfind ps
          bound rs _ htors θE hθE B k l sI c u hcd hu v hv heq s hs2 hs'
      · intro h
        exact (T.ke_backward_plain m hTr A B k l θ hθ hA0 hspecA h).hasElementaryIntegral
    · -- torsion
      rw [htors] at hdec
      dsimp only at hdec
      rcases hwit : witW (CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul
          ((MO Fc ks m).mul z z) (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul
            ((MO Fc ks m).mul z z) (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))) 2
        ((CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
          (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
            (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))).length - 1)
        ![(0 : KF Fc m)] ![1] ![1] N with _ | Wb
      · rw [hwit] at hdec; exact absurd hdec (by simp)
      · rw [hwit] at hdec
        obtain rfl := Option.some.inj hdec
        constructor
        · intro hf
          obtain ⟨E, _, _, _, TE, θE, s, ι, sI, c, u, v, hTEn, hθE, hs2, hs', hcd, hu, hv, heq⟩ :=
            T.ke_lift hmon hdeg m hn hc A θ hθ hgen B k l hf _ hκ0
          exact TE.ke_forward_S_tors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop ha0 q z hfind ps
            bound rs _ N htors Wb hwit θE hθE B k l sI c u hcd hu v hv heq s hs2 hs'
        · intro h
          exact (T.ke_backward_param m hTr A B k l θ hθ hA0 z hz0 _ hκ0 _ _ hspecA h).hasElementaryIntegral

open Classical in
/-- **`keDecide` is correct**: whenever it answers `some b`, the integral of `B(t) θ / tᵏ`
(`θ² = A(t)`, `t` an exponential level) is elementary exactly when `b = true`. -/
theorem keDecide_correct [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hdec : keDecide Fc ks lv m A B k l ps bound rs = some b) :
    HasElementaryIntegral (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) ↔ b = true :=
  T.keDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop ha0 θ hθ hgen B k l ps bound rs _ b hdec

end MTower

end Curves.MT
