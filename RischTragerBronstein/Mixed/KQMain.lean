import RischTragerBronstein.Mixed.KQSem
import RischTragerBronstein.Mixed.KQBridge
import RischTragerBronstein.Mixed.KEMain

/-!
# Square roots over a logarithmic level with poles at ordinary places: the decision is correct

`kqDecide_correct`: whenever `kqDecide` answers `some b`, `∫ B(t) θ / (D(t) A(t)ˡ)`
(`θ² = A(t)`, `t` a logarithmic level of a certified tower, `D = ∏ (t − c_q)`) is elementary iff
`b = true`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Lifting an elementary integral** of `f θ` (`f` a code of level `m + 1`): the Liouville data in
an elementary extension containing `√κ`, for the lifted realization. -/
theorem kq_lift (m : ℕ) (hn : T.n = m + 1) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (f : LC (m + 1)) (hf : HasElementaryIntegral (T.ev (m + 1) f * θ)) (κ : ℚ) (hκ : κ ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Differential E) (_ : CharZero E)
      (TE : MTower Fc ks (constants E) E) (θE s : E) (ι : Type) (sI : Finset ι) (c u : ι → E)
      (v : E), TE.n = m + 1 ∧ θE ^ 2 = TE.evP m A ∧ s ^ 2 = κ ∧ s′ = 0 ∧
      (∀ i ∈ sI, (c i)′ = 0) ∧
      (∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE}) ∧
      v ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} ∧
      TE.ev (m + 1) f * θE = v′ + ∑ i ∈ sI, c i * logDeriv (u i) := by
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
  have hg₂ : (algebraMap E₁ E₂ g)′ = algebraMap L E₂ (T.ev (m + 1) f * θ) := by
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
  rw [hTEev (m + 1) f, show ψ (T.ev (m + 1) f) * θE = ψ (T.ev (m + 1) f * θ) from
    (map_mul ψ _ _).symm, heqL]
  ring

/-- **The logarithmic column times `θ` is elementary** for the twist `ỹ² = s A` (over `L(√s)`). -/
theorem kq_hcolIn (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m)) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hA0 : T.evP m A ≠ 0) (κ : ℚ) (hκ : κ ≠ 0) (W0 W1 : GPoly (LC m)) (q : ℚ) :
    HasElementaryIntegralIn ((q : L) * (T.ev (m + 1) (logCol Fc ks m (A.map ((MO Fc ks m).mul
      (mcst Fc ks m κ))) W0 W1 (MO Fc ks m).one) * θ)) := by
  rw [T.ev_logCol m h]
  set Pv := T.evP m (A.map ((MO Fc ks m).mul (mcst Fc ks m κ))) with hPv
  have hPvA : Pv = κ * T.evP m A := by
    rw [hPv, T.evP_mapMul m h.of_succ, ← T.sem_MP m h.of_succ, T.sem_mcst]
    push_cast; ring
  have hone : T.ev m (MO Fc ks m).one = 1 := T.ev_one_code m h.of_succ
  rw [hone, mul_one]
  set W0v := T.evP m W0 with hW0v
  set W1v := T.evP m W1 with hW1v
  set rv := (1 / 2 : L) * (Pv′ * Pv⁻¹) with hrvdef
  by_cases hN : W0v * W0v - W1v * W1v * Pv = 0
  · rw [hN, inv_zero, mul_zero, zero_mul, mul_zero]
    have : (0 : L) = (0 : L)′ := by simp
    rw [this]; exact hasElementaryIntegralIn_deriv 0
  obtain ⟨E₂, _, _, _, _, -, halg, s, hs2, hs'⟩ := sqrt_ext L κ hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap L E₂).injective
  refine HasElementaryIntegralIn.of_isAlgebraic halg ?_
  set ψ := algebraMap L E₂
  have hs0 : s ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow two_ne_zero] at hs2; exact hκ (by exact_mod_cast hs2.symm)
  have hψd : ∀ w : L, (ψ w)′ = ψ w′ := fun w ↦ deriv_algebraMap w
  set Y := s * ψ θ with hY
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
  have hPv0 : Pv ≠ 0 := by rw [hPvA]; exact mul_ne_zero (by exact_mod_cast hκ) hA0
  have hY2 : Y ^ 2 = ψ Pv := by
    rw [hY, mul_pow, hs2, ← map_pow, hθ, hPvA, map_mul, map_ratCast]
  have hY0 : Y ≠ 0 := mul_ne_zero hs0 ((map_ne_zero ψ).mpr hθ0)
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
  have hcs : (ψ (q : L) / s)′ = 0 := by
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hs', map_ratCast,
      Tower.NestP.deriv_ratCastK (K := E₂) q]; simp
  have := hei_colIn Y (ψ W0v) (ψ W1v) (ψ Pv) (ψ rv) hY2 hYd hNm (ψ (q : L) / s) hcs
  convert this using 1
  rw [hY]
  simp only [map_mul, map_sub, map_add, map_inv₀, hψd]
  rw [div_eq_mul_inv (ψ W0v * _ - _), show ψ W0v ^ 2 - ψ W1v ^ 2 * ψ Pv =
    ψ W0v * ψ W0v - ψ W1v * ψ W1v * ψ Pv by ring]
  field_simp

section Setup

variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ 2 = T.evP m A) (μ : T.F m) (hμ : μ ≠ 0)

/-- `x′ = η` for a logarithmic level. -/
lemma kqS_hx (hmn : m < T.n) {η : LC m} (hk : ks m = .prim η) :
    (T.keS m h A hsq hdeg θ hθ μ hμ).x′ =
      aeval (T.keS m h A hsq hdeg θ hθ μ hμ).x (Polynomial.C (T.val m η)) := by
  change (T.ts m)′ = aeval (T.ts m) (Polynomial.C (T.val m η))
  rw [T.ht m hmn, hk, aeval_C]
  rfl

/-- **The good places**: no algebraic `α` with `α′ = η`. -/
lemma kqS_good (hM : T.MixHyp (m + 1)) {η : LC m} (hk : ks m = .prim η) :
    ∀ α : AlgebraicClosure (T.F m), α′ ≠ algebraMap (T.F m) (AlgebraicClosure (T.F m)) (T.val m η) :=
  fun α ↦ not_deriv_of_integral (T.val m η) (fun z hz ↦ hM.nd m (Nat.lt_succ_self m) η hk z hz) α
    (Algebra.IsIntegral.isIntegral α)

lemma sem_normC [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hm : T.Tr m) (q : LC m) :
    (T.MP m hm).sem (normC Fc m q) = (T.MP m hm).sem q :=
  Subtype.ext (by rw [T.sem_MP m hm, T.sem_MP m hm, T.ev_normC m hm])

include h in
/-- The value of the integrand's rational part. -/
lemma ev_rhsQ (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) :
    T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) :
      LC (m + 1)) = T.evP m B / (T.evP m (prodLinG Fc ks m cs) * T.evP m A ^ l) := by
  rw [show T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) :
      LC (m + 1)) = T.evP m B / T.evP m (GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
        (powG (MO Fc ks m) A l)) from rfl,
    ← T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ) (GPoly.mul _ _ _),
    GPoly.toPoly_mul, map_mul, T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
    T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ), T.evP_powG m h.of_succ]

include h in
lemma evP_prodLin_ne (cs : List (LC m)) : T.evP m (prodLinG Fc ks m cs) ≠ 0 := by
  rw [← T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ), T.toPoly_prodLinG m h.of_succ]
  intro h0
  have htr : Transcendental (T.F m) (T.ts m) := h m (Nat.lt_succ_self m)
  have := transcendental_iff.mp htr _ h0
  exact (List.prod_ne_zero (fun hm ↦ by
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hm
    exact X_sub_C_ne_zero _ hc)) this

end Setup

section Codes

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))

lemma kqOK_spec (hok : kqOK Fc ks m A B l cs = true) (q : ℕ) (hq : q < cs.length) :
    (T.MP m hm).sem (kqR Fc ks m A l cs q) ≠ 0 ∧
      (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ≠ 0 ∧
      (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ≠ 0 := by
  have h := List.all_eq_true.mp hok q (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have ne : ∀ z : LC m, (MO Fc ks m).isZero z = false → (T.MP m hm).sem z ≠ 0 := fun z hz h0 ↦ by
    rw [← (T.MP m hm).isZero_iff] at h0; rw [h0] at hz; exact Bool.noConfusion hz
  refine ⟨ne _ h1, ?_, ?_⟩
  · rw [← T.sem_evalGC m hm]; exact ne _ h2
  · rw [← T.sem_evalGC m hm]; exact ne _ h3

lemma sem_kqR (q : ℕ) :
    (T.MP m hm).sem (kqR Fc ks m A l cs q) =
      (GPoly.toPoly (T.MP m hm) (prodLinG Fc ks m (cs.eraseIdx q))).eval
        ((T.MP m hm).sem (kqC Fc ks m cs q)) *
      (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ l := by
  rw [kqR, T.sem_normC m hm, (T.MP m hm).sem_mul, T.sem_evalGC m hm, sem_powC, T.sem_evalGC m hm]

lemma sem_kqD (q : ℕ) :
    (T.MP m hm).sem (kqD Fc ks m η cs q) =
      (T.MP m hm).sem η - ((T.MP m hm).sem (kqC Fc ks m cs q))′ := by
  rw [kqD, subC, (T.MP m hm).sem_add, (T.MP m hm).sem_neg, (T.MP m hm).sem_deriv, sub_eq_add_neg]

lemma sem_kqQ (q : ℕ) :
    (T.MP m hm).sem (kqQ Fc ks m η A B l cs q) =
      (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ 2 *
        (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) /
        ((T.MP m hm).sem (kqD Fc ks m η cs q) * (T.MP m hm).sem (kqR Fc ks m A l cs q)) ^ 2 := by
  simp only [kqQ]
  rw [T.sem_normC m hm, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul,
    (T.MP m hm).sem_inv, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul, T.sem_evalGC m hm,
    T.sem_evalGC m hm]
  ring

lemma sem_kqB (q : ℕ) :
    (T.MP m hm).sem (kqB Fc ks m η A B l cs q) =
      ((kqK Fc ks m η A B l cs 0 * kqM Fc ks m η A B l cs q : ℚ) : T.F m) *
        ((T.MP m hm).sem (kqD Fc ks m η cs q) * (T.MP m hm).sem (kqR Fc ks m A l cs q) /
          (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q))) := by
  simp only [kqB]
  rw [T.sem_normC m hm, (T.MP m hm).sem_mul, T.sem_mcst, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul,
    (T.MP m hm).sem_inv, T.sem_evalGC m hm]
  ring

lemma toPoly_kqAhat :
    GPoly.toPoly (T.MP m hm) (kqAhat Fc ks m η A B l cs) =
      Polynomial.C ((kqK Fc ks m η A B l cs 0 : ℚ) : T.F m) * GPoly.toPoly (T.MP m hm) A := by
  have e : kqAhat Fc ks m η A B l cs =
      GPoly.smul (MO Fc ks m) (mcst Fc ks m (kqK Fc ks m η A B l cs 0)) A := rfl
  rw [e, GPoly.toPoly_smul, T.sem_mcst]

/-- The constancy test: every `Q_q` is a constant, and then it is the rational `κ_q`. -/
lemma kqConst_spec (hc : kqConst Fc ks m η A B l cs = true) (q : ℕ) (hq : q < cs.length) :
    (T.MP m hm).sem (kqQ Fc ks m η A B l cs q) = ((kqK Fc ks m η A B l cs q : ℚ) : T.F m) := by
  have h := List.all_eq_true.mp hc q (List.mem_range.mpr hq)
  have hd : ((T.MP m hm).sem (kqQ Fc ks m η A B l cs q))′ = 0 := by
    rw [← (T.MP m hm).sem_deriv]; exact ((T.MP m hm).isZero_iff _).mp h
  exact T.ratValC_of_const m hm _ hd

lemma kqConst_of (hq : ∀ q < cs.length,
    ((T.MP m hm).sem (kqQ Fc ks m η A B l cs q))′ = 0) : kqConst Fc ks m η A B l cs = true := by
  refine List.all_eq_true.mpr fun q hqm ↦ ?_
  rw [(T.MP m hm).isZero_iff, (T.MP m hm).sem_deriv]
  exact hq q (List.mem_range.mp hqm)

lemma kqClass_spec (hc : kqClass Fc ks m η A B l cs = true) (q : ℕ) (hq : q < cs.length) :
    kqM Fc ks m η A B l cs q ^ 2 = kqK Fc ks m η A B l cs q / kqK Fc ks m η A B l cs 0 ∧
      0 ≤ kqM Fc ks m η A B l cs q := by
  have h := List.all_eq_true.mp hc q (List.mem_range.mpr hq)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  have := qsqrt_spec hy
  simp only [kqM, hy, Option.getD_some]
  exact this

lemma kqMN_eq (q : ℕ) (hq : q < cs.length) (h0 : 0 ≤ kqM Fc ks m η A B l cs q) :
    (kqMN Fc ks m η A B l cs q : ℚ) = kqDen Fc ks m η A B l cs * kqM Fc ks m η A B l cs q := by
  set x := kqM Fc ks m η A B l cs q with hx
  have hdvd : x.den ∣ kqDen Fc ks m η A B l cs := by
    apply List.dvd_prod
    exact List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
  obtain ⟨k, hk⟩ := hdvd
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_pos.ne'
  have hk' : kqDen Fc ks m η A B l cs / x.den = k := by
    rw [hk, Nat.mul_div_cancel_left _ x.den_pos]
  have hnn : 0 ≤ ((k : ℤ) * x.num) := mul_nonneg (by positivity) (Rat.num_nonneg.mpr h0)
  simp only [kqMN, ← hx, hk']
  rw [show (((k : ℤ) * x.num).toNat : ℚ) = (((k : ℤ) * x.num : ℤ) : ℚ) by
    rw [← Int.toNat_of_nonneg hnn]; rfl]
  rw [hk]
  push_cast
  rw [mul_comm (x.den : ℚ), mul_assoc, mul_comm (x.den : ℚ), Rat.mul_den_eq_num]

end Codes

section Data

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ 2 = T.evP m A) (μ : T.F m) (hμ : μ ≠ 0)

/-- **The data of the abstract theorems** for the curve `y = θ μ`, `y² = μ² A(x)` over `Fₘ`:
`b = f/μ`, `D = ∏ (x − c_q)`, `R_q = ∏_{q' ≠ q} (x − c_{q'})`, `P = μ^{2l−1} B`. -/
theorem kq_data (hmn : m < T.n) (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (hA0 : T.evP m A ≠ 0) :
    let S := T.keS m h A hsq hdeg θ hθ μ hμ
    let f : LC (m + 1) := (B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l))
    let b := T.ev (m + 1) f / ((μ : T.F m) : L)
    let c : Fin cs.length → T.F m := fun q ↦ (T.MP m h.of_succ).sem (kqC Fc ks m cs q)
    let D := GPoly.toPoly (T.MP m h.of_succ) (prodLinG Fc ks m cs)
    let R : Fin cs.length → (T.F m)[X] := fun q ↦
      GPoly.toPoly (T.MP m h.of_succ) (prodLinG Fc ks m (cs.eraseIdx q))
    let P := Polynomial.C (μ ^ (2 * l) / μ) * GPoly.toPoly (T.MP m h.of_succ) B
    b ∈ (T.F m)⟮S.x⟯ ∧ b * S.y = T.ev (m + 1) f * θ ∧ b * S.y ∈ (T.F m)⟮S.x⟯⟮S.y⟯ ∧
      (∀ q, D = (X - Polynomial.C (c q)) * R q) ∧
      (∀ α : AlgebraicClosure (T.F m), (∀ q, α ≠ algebraMap (T.F m) _ (c q)) →
        (D.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval α ≠ 0) ∧
      b * aeval S.x (D * S.p ^ l) = aeval S.x P := by
  intro S f b c D R P
  have hTm : T.Tr m := h.of_succ
  have hμL : ((μ : T.F m) : L) ≠ 0 := fun h0 ↦ hμ (Subtype.ext h0)
  have hDv : T.evP m (prodLinG Fc ks m cs) ≠ 0 := T.evP_prodLin_ne m h cs
  have hf : T.ev (m + 1) f = T.evP m B / (T.evP m (prodLinG Fc ks m cs) * T.evP m A ^ l) :=
    T.ev_rhsQ m h A B l cs
  have hxm : ∀ Q : (T.F m)[X], aeval (T.ts m) Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) Q = aeval S.x Q from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x Q]
    exact SetLike.coe_mem _
  have hev : ∀ Q : GPoly (LC m), T.evP m Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]; exact hxm _
  have hb : b ∈ (T.F m)⟮S.x⟯ := by
    show T.ev (m + 1) f / ((μ : T.F m) : L) ∈ _
    rw [hf]
    exact div_mem (div_mem (hev B) (mul_mem (hev _) (pow_mem (hev A) l)))
      (IntermediateField.algebraMap_mem _ μ)
  have hby : b * S.y = T.ev (m + 1) f * θ := by
    change T.ev (m + 1) f / ((μ : T.F m) : L) * (θ * μ) = _
    field_simp
  refine ⟨hb, hby, ?_, fun q ↦ T.prodLin_eraseIdx m hTm cs q q.2, fun α hα ↦ ?_, ?_⟩
  · rw [hby]
    refine T.keS_mem m h A hsq hdeg θ hθ μ hμ _ (mul_mem (IntermediateField.algebraMap_mem _
      (⟨T.ev (m + 1) f, T.ev_mem (m + 1) f⟩ : T.F (m + 1))) (mem_adjoin_simple_self _ _))
  · refine T.eval_prodLin_ne m hTm cs α fun c' hc' ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    have := hα ⟨i, hi⟩
    simpa [c, kqC, List.getD_eq_getElem _ _ hi] using this
  · have hp : S.p = Polynomial.C (μ ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hp]
    have hSx : S.x = T.ts m := rfl
    simp only [P, D, hSx, map_mul, map_pow, aeval_C, IntermediateField.algebraMap_apply]
    rw [T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm), T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm),
      T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    show T.ev (m + 1) f / ((μ : T.F m) : L) * _ = _
    rw [hf]
    push_cast
    field_simp
    ring

end Data

lemma sem_eq_val (m : ℕ) (hm : T.Tr m) (q : LC m) : (T.MP m hm).sem q = T.val m q :=
  Subtype.ext (T.sem_MP m hm q)

open Classical in
/-- **Forward, the squared residues are constant.** -/
theorem kq_forward_const [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    kqConst Fc ks m η A B l cs = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kq_data m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) B l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  refine T.kqConst_of m hTm η A B l cs fun q hq ↦ ?_
  have hok' := fun q' (hq' : q' < cs.length) ↦ T.kqOK_spec m hTm A B l cs hok q' hq'
  have hRne : ∀ q' : Fin cs.length, (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))).eval
      ((T.MP m hTm).sem (kqC Fc ks m cs q')) ≠ 0 := fun q' h0 ↦ by
    have := (hok' q' q'.2).1
    rw [T.sem_kqR m hTm, h0, zero_mul] at this
    exact this rfl
  have hp : S.p = Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
  have hpc : ∀ q' : Fin cs.length, S.p.eval ((T.MP m hTm).sem (kqC Fc ks m cs q')) ≠ 0 := fun q' ↦ by
    rw [hp, eval_mul, eval_C, one_pow, one_mul]; exact (hok' q' q'.2).2.1
  obtain ⟨ζ, hζ, hζe⟩ := S.kq_resid_const (K := AlgebraicClosure (T.F m)) (T.val m η)
    (T.kqS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
    (T.kqS_good m MS.hyp hk) (T.keS_constC m)
    (fun q' : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q'))
    (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m cs))
    (fun q' ↦ GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne hDoff hbP hpc
    rfl hbm sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq) ⟨q, hq⟩
  have hQ : (T.MP m hTm).sem (kqQ Fc ks m η A B l cs q) = ζ := by
    rw [T.sem_kqQ m hTm, T.sem_kqD m hTm, T.sem_kqR m hTm, T.sem_eq_val m hTm η]
    simp only [hp, eval_mul, eval_C, one_pow, div_one, one_mul, eval_pow] at hζe
    have hne : (T.val m η - ((T.MP m hTm).sem (kqC Fc ks m cs q))′) *
        ((GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q))).eval
          ((T.MP m hTm).sem (kqC Fc ks m cs q)) *
        (GPoly.toPoly (T.MP m hTm) A).eval ((T.MP m hTm).sem (kqC Fc ks m cs q)) ^ l) ≠ 0 := by
      have h1 := (hok' q hq).1
      rw [T.sem_kqR m hTm] at h1
      refine mul_ne_zero (fun h0 ↦ ?_) h1
      exact T.kqS_good m MS.hyp hk (algebraMap (T.F m) _ ((T.MP m hTm).sem (kqC Fc ks m cs q)))
        (by rw [deriv_algebraMap, ← sub_eq_zero.mp h0])
    rw [div_eq_iff (pow_ne_zero 2 hne)]
    simpa using hζe
  rw [hQ, hζ]


omit [CharZero L] in
lemma fK_facts' {K C' : Type*} [Field K] [DecidableEq K] [Field C'] (φ : K →+* C') (fK : CPoly K)
    (htrim : CPoly.trim fK = fK) (p : C'[X]) (hpf : p = (toPoly fK).map φ) (hp0 : p ≠ 0)
    (hsq : Squarefree p) (hcop : Nat.Coprime 2 p.natDegree) :
    (toPoly fK).natDegree = fK.length - 1 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime 2 (fK.length - 1) := by
  have hne : toPoly fK ≠ 0 := fun h0 ↦ hp0 (by rw [hpf, h0, Polynomial.map_zero])
  have htne : CPoly.trim fK ≠ [] := fun h0 ↦ hne ((CPoly.trim_eq_nil_iff fK).mp h0)
  have hlen := CPoly.length_trim htne
  rw [htrim] at hlen
  have hdeg : (toPoly fK).natDegree = fK.length - 1 := by omega
  have hpdeg : p.natDegree = (toPoly fK).natDegree := by
    rw [hpf, natDegree_map_eq_of_injective φ.injective]
  exact ⟨hdeg, squarefree_of_map φ _ (hpf ▸ hsq), by rw [← hdeg, ← hpdeg]; exact hcop⟩

open Classical in
/-- **The twisted curve**: with `μ = √κ₀`, the ordinates `β_q` of the poles on `y² = μ² A`, the
residue identity with `ρ = μ / M`, and the code of `μ² A` over `Kₘ`. -/
theorem kq_twist [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true)
    (hcst : kqConst Fc ks m η A B l cs = true) (hcl : kqClass Fc ks m η A B l cs = true)
    (hr : 0 < cs.length) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (s : L) (hs2 : s ^ 2 = (kqK Fc ks m η A B l cs 0 : ℚ)) (hs' : s′ = 0) :
    ∃ (μ : T.F m) (hμ : μ ≠ 0), ((μ : T.F m) : L) = s ∧ μ ^ 2 = (kqK Fc ks m η A B l cs 0 : T.F m) ∧
      (∀ q : Fin cs.length, (T.MP m hTr.of_succ).sem (kqB Fc ks m η A B l cs q) ≠ 0 ∧
        (T.MP m hTr.of_succ).sem (kqB Fc ks m η A B l cs q) ^ 2 =
          (T.keS m hTr A hsq hdegA θ hθ μ hμ).p.eval ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))) ∧
      (∀ q : Fin cs.length,
        (Polynomial.C (μ ^ (2 * l) / μ) * GPoly.toPoly (T.MP m hTr.of_succ) B).eval
          ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q)) *
          (T.MP m hTr.of_succ).sem (kqB Fc ks m η A B l cs q) =
        (kqMq Fc ks m η A B l cs q : T.F m) * (μ / (kqDen Fc ks m η A B l cs : T.F m)) *
          (T.val m η - ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))′) *
          (GPoly.toPoly (T.MP m hTr.of_succ) (prodLinG Fc ks m (cs.eraseIdx q)) *
            (T.keS m hTr A hsq hdegA θ hθ μ hμ).p ^ l).eval
            ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))) ∧
      (T.keS m hTr A hsq hdegA θ hθ μ hμ).p =
        (toPoly (kqFK Fc ks m η A B l cs)).map (T.psiF m hTr.of_succ) := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTm : T.Tr m := hTr.of_succ
  have hok' := fun q' (hq' : q' < cs.length) ↦ T.kqOK_spec m hTm A B l cs hok q' hq'
  set κ : ℕ → ℚ := kqK Fc ks m η A B l cs with hκ
  set c : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcdef
  set d : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqD Fc ks m η cs q) with hddef
  set Rt : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqR Fc ks m A l cs q) with hRt
  set Bc : ℕ → T.F m := fun q ↦ (GPoly.toPoly (T.MP m hTm) B).eval (c q) with hBc
  set Ac : ℕ → T.F m := fun q ↦ (GPoly.toPoly (T.MP m hTm) A).eval (c q) with hAc
  have hd0 : ∀ q, d q ≠ 0 := fun q h0 ↦ by
    simp only [hddef, T.sem_kqD m hTm, T.sem_eq_val m hTm η] at h0
    exact T.kqS_good m MS.hyp hk (algebraMap (T.F m) _ (c q))
      (by rw [deriv_algebraMap, ← sub_eq_zero.mp h0])
  have hQv : ∀ q < cs.length, (κ q : T.F m) = Bc q ^ 2 * Ac q / (d q * Rt q) ^ 2 := fun q hq ↦ by
    rw [← T.kqConst_spec m hTm η A B l cs hcst q hq, T.sem_kqQ m hTm]
  have hκ0 : ∀ q < cs.length, κ q ≠ 0 := fun q hq h0 ↦ by
    have := hQv q hq
    rw [h0, Rat.cast_zero, eq_comm, div_eq_zero_iff] at this
    rcases this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact (hok' q hq).2.2 (pow_eq_zero_iff two_ne_zero |>.mp h2)
      · exact (hok' q hq).2.1 h2
    · exact mul_ne_zero (hd0 q) (hok' q hq).1 (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have hsL : s ≠ 0 := fun h0 ↦ hκ0 0 hr (by
    rw [h0, zero_pow two_ne_zero] at hs2; exact_mod_cast hs2.symm)
  obtain ⟨c0, hc0⟩ := T.hconst s hs'
  have hsF : s ∈ T.F m := hc0 ▸ T.const_mem m c0
  set μ : T.F m := ⟨s, hsF⟩ with hμdef
  have hμ : μ ≠ 0 := fun h0 ↦ hsL (congrArg Subtype.val h0)
  have hμ2 : μ ^ 2 = (κ 0 : T.F m) := Subtype.ext (by
    rw [IntermediateField.coe_pow]; push_cast; exact hs2)
  have hp : (T.keS m hTr A hsq hdegA θ hθ μ hμ).p =
      Polynomial.C (μ ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
  have hMq : ∀ q (hq : q < cs.length), (kqMq Fc ks m η A B l cs ⟨q, hq⟩ : T.F m) =
      ((kqDen Fc ks m η A B l cs * kqM Fc ks m η A B l cs q : ℚ) : T.F m) := fun q hq ↦ by
    have := kqMN_eq m η A B l cs q hq (kqClass_spec m η A B l cs hcl q hq).2
    simp only [kqMq]
    rw [← this]; push_cast; rfl
  refine ⟨μ, hμ, rfl, hμ2, fun q ↦ ?_, fun q ↦ ?_, ?_⟩
  · have hq := q.2
    obtain ⟨hm2, -⟩ := kqClass_spec m η A B l cs hcl q hq
    rw [T.sem_kqB m hTm, hp, eval_mul, eval_C, hμ2]
    have hQ := hQv q hq
    have hB0 := (hok' q hq).2.2
    have hR0 := (hok' q hq).1
    have hk0 : (κ 0 : T.F m) ≠ 0 := by exact_mod_cast hκ0 0 hr
    have hmq : (kqM Fc ks m η A B l cs q : T.F m) ^ 2 = (κ q : T.F m) / (κ 0 : T.F m) := by
      rw [← Rat.cast_pow, hm2]; push_cast; rfl
    have hm0 : (kqM Fc ks m η A B l cs q : T.F m) ≠ 0 := by
      intro h0
      rw [h0, zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at hmq
      rcases hmq with h | h
      · exact hκ0 q hq (by exact_mod_cast h)
      · exact hk0 h
    refine ⟨?_, ?_⟩
    · push_cast
      exact mul_ne_zero (mul_ne_zero hk0 hm0) (div_ne_zero (mul_ne_zero (hd0 q) hR0) hB0)
    · push_cast
      rw [mul_pow, mul_pow, hmq, hQ]
      have hd0q := hd0 q
      simp only [hddef, hRt, hBc, hAc, hcdef, hκ] at hd0q hR0 hB0 ⊢
      field_simp
  · have hq := q.2
    rw [hMq q hq, T.sem_kqB m hTm, hp, eval_mul, eval_C, eval_mul, eval_pow, eval_mul, eval_C,
      T.sem_kqR m hTm, ← T.sem_eq_val m hTm η, ← T.sem_kqD m hTm]
    have hB0 := (hok' q hq).2.2
    have hDen : (kqDen Fc ks m η A B l cs : T.F m) ≠ 0 := by
      have : 0 < kqDen Fc ks m η A B l cs := by
        refine List.prod_pos fun x hx ↦ ?_
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact Rat.den_pos _
      exact_mod_cast this.ne'
    have hμ2' : ((kqK Fc ks m η A B l cs 0 : ℚ) : T.F m) = μ ^ 2 := hμ2.symm
    push_cast
    rw [hμ2']
    field_simp
    ring
  · rw [kqFK, CPoly.toPoly_trim, T.toPoly_trC_map m hTm, T.toPoly_kqAhat m hTm, hp, hμ2]


/-- **The data over the code field `Kₘ`**: the curve code `fK`, the points `(kqAl q, kqBe q)`. -/
theorem kq_KF_facts [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hTm : T.Tr m) (η : LC m)
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (p : (T.F m)[X])
    (hpf : p = (toPoly (kqFK Fc ks m η A B l cs)).map (T.psiF m hTm)) (hsqp : Squarefree p)
    (hcopp : Nat.Coprime 2 p.natDegree)
    (hβC : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqB Fc ks m η A B l cs q) ≠ 0 ∧
      (T.MP m hTm).sem (kqB Fc ks m η A B l cs q) ^ 2 = p.eval ((T.MP m hTm).sem (kqC Fc ks m cs q)))
    (hcinj : Function.Injective fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) :
    (toPoly (kqFK Fc ks m η A B l cs)).natDegree = (kqFK Fc ks m η A B l cs).length - 1 ∧
      Squarefree (toPoly (kqFK Fc ks m η A B l cs)) ∧
      Nat.Coprime 2 ((kqFK Fc ks m η A B l cs).length - 1) ∧
      (∀ q, kqBe Fc ks m η A B l cs q ≠ 0 ∧
        kqBe Fc ks m η A B l cs q ^ 2 = (toPoly (kqFK Fc ks m η A B l cs)).eval (kqAl Fc ks m cs q)) ∧
      Function.Injective (fun q ↦ (kqAl Fc ks m cs q, kqBe Fc ks m η A B l cs q)) ∧
      (fun q ↦ T.psiF m hTm (kqAl Fc ks m cs q)) =
        (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) ∧
      (fun q ↦ T.psiF m hTm (kqBe Fc ks m η A B l cs q)) =
        (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqB Fc ks m η A B l cs q)) := by
  have hp0 : p ≠ 0 := hsqp.ne_zero
  obtain ⟨hd, hsqK, hcop2⟩ := fK_facts' (T.psiF m hTm) (kqFK Fc ks m η A B l cs) (CPoly.trim_trim _)
    p hpf hp0 hsqp hcopp
  have hA : (fun q ↦ T.psiF m hTm (kqAl Fc ks m cs q)) =
      (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) :=
    funext fun q ↦ T.psiF_trC m hTm _
  have hB : (fun q ↦ T.psiF m hTm (kqBe Fc ks m η A B l cs q)) =
      (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqB Fc ks m η A B l cs q)) :=
    funext fun q ↦ T.psiF_trC m hTm _
  refine ⟨hd, hsqK, hcop2, fun q ↦ ⟨fun h0 ↦ ?_, ?_⟩, fun q q' hqq ↦ ?_, hA, hB⟩
  · apply (hβC q).1
    rw [← congrFun hB q, h0, map_zero]
  · apply (T.psiF m hTm).injective
    rw [map_pow, congrFun hB q, (hβC q).2, hpf, eval_map, ← congrFun hA q, eval₂_at_apply]
  · apply hcinj
    have h1 := congrArg (fun z ↦ T.psiF m hTm z.1) hqq
    simp only at h1
    rw [congrFun hA q, congrFun hA q'] at h1
    exact h1

lemma kq_cinj [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hTm : T.Tr m) (A B : GPoly (LC m))
    (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true) :
    Function.Injective fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) := by
  intro q q' hqq
  by_contra hne
  have h1 := (T.kqOK_spec m hTm A B l cs hok q q.2).1
  rw [T.sem_kqR m hTm] at h1
  have hR : (T.MP m hTm).sem (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q)) (kqC Fc ks m cs q))
      ≠ 0 := by
    rw [T.sem_evalGC m hTm]; exact left_ne_zero_of_mul h1
  have hz : (MO Fc ks m).isZero (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q))
      (kqC Fc ks m cs q)) = false := by
    cases h : (MO Fc ks m).isZero (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q))
      (kqC Fc ks m cs q))
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hR
  have := T.eval_prodLin_erase_ne m hTm cs q q.2 hz q' q'.2 (fun h ↦ hne (Fin.ext h).symm)
  apply this
  simp only [kqC, List.getD_eq_getElem _ _ q'.2] at hqq ⊢
  rw [← hqq]


lemma kqMq_zero_ne [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hTm : T.Tr m) (η : LC m)
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hcl : kqClass Fc ks m η A B l cs = true)
    (hr : 0 < cs.length) (hκ0 : kqK Fc ks m η A B l cs 0 ≠ 0) :
    kqMq Fc ks m η A B l cs ⟨0, hr⟩ ≠ 0 := by
  obtain ⟨h2, h0⟩ := kqClass_spec m η A B l cs hcl 0 hr
  have hm : (kqMq Fc ks m η A B l cs ⟨0, hr⟩ : ℚ) =
      kqDen Fc ks m η A B l cs * kqM Fc ks m η A B l cs 0 := kqMN_eq m η A B l cs 0 hr h0
  intro hz
  rw [hz, Nat.cast_zero, eq_comm, mul_eq_zero] at hm
  rcases hm with hm | hm
  · have : 0 < kqDen Fc ks m η A B l cs := by
      refine List.prod_pos fun x hx ↦ ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact Rat.den_pos _
    exact this.ne' (by exact_mod_cast hm)
  · rw [hm, div_self hκ0] at h2; norm_num at h2

open Classical in
/-- **Forward, no torsion**: a Liouville form is impossible. -/
theorem kq_forward_nontors [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true)
    (hcst : kqConst Fc ks m η A B l cs = true) (hcl : kqClass Fc ks m η A B l cs = true)
    (hr : 0 < cs.length) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cp : CertProv (KF Fc m)) (htors : torsOracleC (redAtKF Fc m rs) cp ps bound (kqFK Fc ks m η A B l cs) 2
      (gammaL (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) 1) = some none)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (s : L) (hs2 : s ^ 2 = (kqK Fc ks m η A B l cs 0 : ℚ)) (hs' : s′ = 0) : False := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨μ, hμ, hμs, hμ2, hβ, hres, hpf⟩ := T.kq_twist hmon hdeg m hn hc hk hTr A hsq hdegA B l cs
    hok hcst hcl hr θ hθ s hs2 hs'
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kq_data m hTr A hsq hdegA θ hθ μ hμ (by omega) B l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ μ hμ with hS
  have hok' := fun q' (hq' : q' < cs.length) ↦ T.kqOK_spec m hTm A B l cs hok q' hq'
  have hRne : ∀ q' : Fin cs.length, (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))).eval
      ((T.MP m hTm).sem (kqC Fc ks m cs q')) ≠ 0 := fun q' h0 ↦ by
    have := (hok' q' q'.2).1
    rw [T.sem_kqR m hTm, h0, zero_mul] at this
    exact this rfl
  have hcinj := T.kq_cinj m hTm A B l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ μ hμ hcopA
  obtain ⟨hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ := T.kq_KF_facts m hTm η A B l cs S.p hpf S.hsq hcopS
    hβ hcinj
  have hspec := torsOracleC_spec (redAtKF Fc m rs) cp (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
    ps bound hsqK hcop2
  have hnot := (hspec cs.length (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs)
    (kqMq Fc ks m η A B l cs) hvK hinjK).2 htors
  have hΓK : ∀ q, ((S.n : ℕ) : KF Fc m) * kqBe Fc ks m η A B l cs q ^ (S.n - 1) ≠ 0 ∧
      kqBe Fc ks m η A B l cs q ^ S.n =
        (toPoly (kqFK Fc ks m η A B l cs)).eval (kqAl Fc ks m cs q) := fun q ↦ by
    refine ⟨?_, (hvK q).2⟩
    show ((2 : ℕ) : KF Fc m) * kqBe Fc ks m η A B l cs q ^ (2 - 1) ≠ 0
    rw [pow_one]
    exact mul_ne_zero (by norm_num) (hvK q).1
  have hinj' : Function.Injective fun q ↦ (T.psiF m hTm (kqAl Fc ks m cs q),
      T.psiF m hTm (kqBe Fc ks m η A B l cs q)) := fun q q' h ↦ hinjK (by
    simp only [Prod.ext_iff] at h ⊢
    exact ⟨(T.psiF m hTm).injective h.1, (T.psiF m hTm).injective h.2⟩)
  have hnt := S.not_isPrincipalS_gen (K := AlgebraicClosure (T.F m)) (T.psiF m hTm) _ hpf hd hcopS
    _ _ (kqMq Fc ks m η A B l cs) hΓK hinj' (fun q ↦ (hvK q).1) hnot
  rw [hA, hB] at hnt
  have hκ0 : kqK Fc ks m η A B l cs 0 ≠ 0 := by
    intro h0
    have h1 := (hβ ⟨0, hr⟩).1
    have h2 := (hβ ⟨0, hr⟩).2
    have hp : S.p = Polynomial.C (μ ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hp, eval_mul, eval_C, hμ2, h0, Rat.cast_zero, zero_mul] at h2
    exact h1 (pow_eq_zero_iff two_ne_zero |>.mp h2)
  have hDen : (kqDen Fc ks m η A B l cs : T.F m) ≠ 0 := by
    have : 0 < kqDen Fc ks m η A B l cs := by
      refine List.prod_pos fun x hx ↦ ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact Rat.den_pos _
    exact_mod_cast this.ne'
  exact S.kq_liouville_nontors (K := AlgebraicClosure (T.F m)) (T.val m η)
    (T.kqS_hx m hTr A hsq hdegA θ hθ μ hμ (by omega) hk) (fun c ↦ deriv_algebraMap c)
    (T.kqS_good m MS.hyp hk) (T.keS_constC m)
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q))
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqB Fc ks m η A B l cs q)) hcinj hβ
    (kqMq Fc ks m η A B l cs) (μ / (kqDen Fc ks m η A B l cs : T.F m))
    (Polynomial.C (μ ^ (2 * l) / μ) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m cs))
    (fun q' ↦ GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne hDoff hbP
    hres rfl hnt ⟨⟨0, hr⟩, T.kqMq_zero_ne m hTm η A B l cs hcl hr hκ0⟩ (div_ne_zero hμ hDen) hbm
    sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ μ hμ _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ μ hμ _ hv) (by rw [hby]; exact heq)


open Classical in
/-- **Forward, torsion**: the parametric equation has a solution with the coefficient of the
integrand non-zero. -/
theorem kq_forward_tors [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true)
    (hcst : kqConst Fc ks m η A B l cs = true) (hcl : kqClass Fc ks m η A B l cs = true)
    (hr : 0 < cs.length) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cp : CertProv (KF Fc m)) (N : ℕ) (htors : torsOracleC (redAtKF Fc m rs) cp ps bound (kqFK Fc ks m η A B l cs) 2
      (gammaL (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) 1) =
        some (some N))
    (Wb : Sup.BPoly (KF Fc m))
    (hwit : witW (kqFK Fc ks m η A B l cs) 2 ((kqFK Fc ks m η A B l cs).length - 1)
      (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) N = some Wb)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (s : L) (hs2 : s ^ 2 = (kqK Fc ks m η A B l cs 0 : ℚ)) (hs' : s′ = 0) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      [((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) : LC (m + 1)),
        normC Fc (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs)
          ((Wb.getD 0 []).map (unTr Fc m)) ((Wb.getD 1 []).map (unTr Fc m)) (MO Fc ks m).one)]).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨μ, hμ, hμs, hμ2, hβ, hres, hpf⟩ := T.kq_twist hmon hdeg m hn hc hk hTr A hsq hdegA B l cs
    hok hcst hcl hr θ hθ s hs2 hs'
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kq_data m hTr A hsq hdegA θ hθ μ hμ (by omega) B l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ μ hμ with hS
  have hok' := fun q' (hq' : q' < cs.length) ↦ T.kqOK_spec m hTm A B l cs hok q' hq'
  have hRne : ∀ q' : Fin cs.length, (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))).eval
      ((T.MP m hTm).sem (kqC Fc ks m cs q')) ≠ 0 := fun q' h0 ↦ by
    have := (hok' q' q'.2).1
    rw [T.sem_kqR m hTm, h0, zero_mul] at this
    exact this rfl
  have hcinj := T.kq_cinj m hTm A B l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ μ hμ hcopA
  obtain ⟨hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ := T.kq_KF_facts m hTm η A B l cs S.p hpf S.hsq hcopS
    hβ hcinj
  have hspec := torsOracleC_spec (redAtKF Fc m rs) cp (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
    ps bound hsqK hcop2
  have hN1 := ((hspec cs.length (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs)
    (kqMq Fc ks m η A B l cs) hvK hinjK).1 N htors).1
  have hΓK : ∀ q, ((S.n : ℕ) : KF Fc m) * kqBe Fc ks m η A B l cs q ^ (S.n - 1) ≠ 0 ∧
      kqBe Fc ks m η A B l cs q ^ S.n =
        (toPoly (kqFK Fc ks m η A B l cs)).eval (kqAl Fc ks m cs q) := fun q ↦ by
    refine ⟨?_, (hvK q).2⟩
    show ((2 : ℕ) : KF Fc m) * kqBe Fc ks m η A B l cs q ^ (2 - 1) ≠ 0
    rw [pow_one]
    exact mul_ne_zero (by norm_num) (hvK q).1
  have hinj' : Function.Injective fun q ↦ (T.psiF m hTm (kqAl Fc ks m cs q),
      T.psiF m hTm (kqBe Fc ks m η A B l cs q)) := fun q q' h ↦ hinjK (by
    simp only [Prod.ext_iff] at h ⊢
    exact ⟨(T.psiF m hTm).injective h.1, (T.psiF m hTm).injective h.2⟩)
  obtain ⟨hWne, hWord⟩ := S.ordAt_witW_gen (K := AlgebraicClosure (T.F m)) (T.psiF m hTm) _ hpf hd
    hcopS _ _ (kqMq Fc ks m η A B l cs) hΓK hinj' (fun q ↦ (hvK q).1) N Wb hwit
  rw [hA, hB] at hWord
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
  have hP : aeval (T.ts m) S.p = T.evP m (kqAhat Fc ks m η A B l cs) := by
    rw [hpf, kqFK, CPoly.toPoly_trim, T.toPoly_trC_map m hTm,
      T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
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
  have hx := T.kqS_hx m hTr A hsq hdegA θ hθ μ hμ (by omega) hk
  obtain ⟨aa, haa, e, he, hae⟩ := S.kq_liouville_tors (K := AlgebraicClosure (T.F m)) (T.val m η)
    hx (fun c ↦ deriv_algebraMap c)
    (T.kqS_good m MS.hyp hk) (T.keS_constC m)
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q))
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqB Fc ks m η A B l cs q)) hcinj hβ
    (kqMq Fc ks m η A B l cs) (μ / (kqDen Fc ks m η A B l cs : T.F m))
    (Polynomial.C (μ ^ (2 * l) / μ) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m cs))
    (fun q' ↦ GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne hDoff hbP
    hres rfl hcopS N (by omega) (S.elemW Wp) hWne hWord W0 W1 (hmemx _) (hmemx _) hWe hNm hbm
    sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ μ hμ _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ μ hμ _ hv) (by rw [hby]; exact heq)
  rw [hby] at hae
  -- the value of the column
  set col := normC Fc (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs)
    ((Wb.getD 0 []).map (unTr Fc m)) ((Wb.getD 1 []).map (unTr Fc m)) (MO Fc ks m).one) with hcol
  have hPd : (aeval (T.ts m) S.p)′ = aeval (T.ts m) (mapCoeffs S.p +
      Polynomial.C (T.val m η) * derivative S.p) := S.deriv_aeval_xW _ hx S.p
  have hcolv : T.ev (m + 1) col = ((W0 * (W1′ + W1 *
      (aeval (T.ts m) (mapCoeffs S.p + Polynomial.C (T.val m η) * derivative S.p) /
        ((2 : L) * aeval (T.ts m) S.p))) - W0′ * W1) /
        (W0 ^ 2 - W1 ^ 2 * aeval (T.ts m) S.p)) := by
    rw [hcol, T.ev_normC (m + 1) hTr, T.ev_logCol m hTr, hW0c, hW1c, ← hP, ← hPd,
      T.ev_one_code m hTm, mul_one]
    field_simp
  -- the constant `e μ`
  have hμL : ((μ : T.F m) : L) = s := hμs
  have hes : (algebraMap (T.F m) L e * s)′ = 0 := by
    rw [Derivation.leibniz, he, hs']; simp
  obtain ⟨c0, hc0⟩ := T.hconst (-(algebraMap (T.F m) L e * s)) (by rw [map_neg, hes, neg_zero])
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  set rhs : LC (m + 1) := (B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
    (powG (MO Fc ks m) A l)) with hrhs
  have hA0' : T.evP m A ≠ 0 := hA0
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (aa * μ) 1
  simp only [pow_one] at h1
  have h2 : (aa * S.y)′ = (aa * μ * θ)′ := by
    change (aa * (θ * μ))′ = _; ring_nf
  rw [h2, h1] at hae
  have hSy : S.y = θ * μ := rfl
  rw [hSy] at hae
  have hn' : ((S.n : ℕ) : L) = 2 := by show ((2 : ℕ) : L) = 2; norm_num
  have hSx : S.x = T.ts m := rfl
  rw [hn', hSx] at hae
  have haaF : aa * (μ : L) ∈ T.F (m + 1) := mul_mem ((T.mem_F_succ).mpr haa) (T.le_succ m μ.2)
  obtain ⟨βv, hβv, -⟩ := hspecA.complete [rhs, col] [1, c0] (fun i hi ↦ by
      rcases i with _ | _ | i
      · simp at hi
      · simp at hi
      · rfl) ⟨aa * μ, haaF⟩ (by
    apply Subtype.ext
    simp only [sC, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, List.getD_cons_zero, List.getD_cons_succ, IntermediateField.coe_add,
      IntermediateField.coe_mul, MTower.coe_deriv, map_one, one_mul]
    rw [T.sem_kpFr m hTr, T.sem_MP (m + 1) hTr, T.sem_MP (m + 1) hTr, hcolv]
    change _ = _ + algebraMap Cc L c0 * _
    rw [hc0]
    change (aa * μ)′ + _ * (aa * μ) = _
    rw [show (((1 : ℕ) : ℚ) / (2 : ℕ) : L) = (1 / 2 : L) by push_cast; ring]
    apply mul_right_cancel₀ hθ0
    rw [hμL] at hae ⊢
    push_cast at hae ⊢
    linear_combination (-1 : L) * hae)
  have h0 := hβv 0
  simp only [List.getD_cons_zero] at h0
  by_contra hno
  simp only [List.any_eq_true, not_exists, not_and, decide_eq_true_eq, not_not] at hno
  apply one_ne_zero (α := Cc)
  rw [h0]
  refine Finset.sum_eq_zero fun kk hkk ↦ ?_
  have hmem : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) [rhs, col]).getD kk
      ([], (MO Fc ks (m + 1)).zero) ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) [rhs, col] := by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hkk)]
    exact List.getElem_mem _
  rw [hno _ hmem, map_zero, mul_zero]


lemma kqK_ne [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hM : T.MixHyp (m + 1)) {η : LC m}
    (hk : ks m = .prim η) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (hok : kqOK Fc ks m A B l cs = true) (hcst : kqConst Fc ks m η A B l cs = true) (q : ℕ)
    (hq : q < cs.length) : kqK Fc ks m η A B l cs q ≠ 0 := by
  have hTm : T.Tr m := hM.tr.of_succ
  have hok' := T.kqOK_spec m hTm A B l cs hok q hq
  have hQ := T.kqConst_spec m hTm η A B l cs hcst q hq
  rw [T.sem_kqQ m hTm] at hQ
  intro h0
  rw [h0, Rat.cast_zero, div_eq_zero_iff] at hQ
  have hd0 : (T.MP m hTm).sem (kqD Fc ks m η cs q) ≠ 0 := fun h0 ↦ by
    rw [T.sem_kqD m hTm, T.sem_eq_val m hTm η] at h0
    exact T.kqS_good m hM hk (algebraMap (T.F m) _ ((T.MP m hTm).sem (kqC Fc ks m cs q)))
      (by rw [deriv_algebraMap, ← sub_eq_zero.mp h0])
  rcases hQ with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hok'.2.2 (pow_eq_zero_iff two_ne_zero |>.mp h2)
    · exact hok'.2.1 h2
  · exact mul_ne_zero hd0 hok'.1 (pow_eq_zero_iff two_ne_zero |>.mp h1)

/-- **A solution of the parametric equation gives an antiderivative.** -/
theorem kq_backward_param [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hTr : T.Tr (m + 1))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (η : LC m) (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hA0 : T.evP m A ≠ 0) (hκ : kqK Fc ks m η A B l cs 0 ≠ 0) (W0 W1 : GPoly (LC m))
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (h : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      [((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) : LC (m + 1)),
        normC Fc (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 (MO Fc ks m).one)]).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true) :
    HasElementaryIntegralIn (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) := by
  obtain ⟨r, hr, hr0⟩ := List.any_eq_true.mp h
  have hq0 : r.1.getD 0 0 ≠ 0 := of_decide_eq_true hr0
  set col := normC Fc (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 (MO Fc ks m).one)
    with hcol
  set rhs : LC (m + 1) := (B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
    (powG (MO Fc ks m) A l)) with hrhs
  have hs := hspec.sound [rhs, col] r hr
  have hsQ : sQ (T.MP (m + 1) hTr) r.1 [rhs, col] =
      ((r.1.getD 0 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem rhs +
        ((r.1.getD 1 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem col := by
    simp [sQ, Finset.sum_range_succ]
  rw [hsQ] at hs
  have hsL := congrArg Subtype.val hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv] at hsL
  rw [T.sem_kpFr m hTr] at hsL
  simp only [T.sem_MP (m + 1) hTr] at hsL
  rw [hcol, T.ev_normC (m + 1) hTr] at hsL
  set a : L := T.ev (m + 1) r.2
  set q0 : ℚ := r.1.getD 0 0
  set q1 : ℚ := r.1.getD 1 0
  set colv := T.ev (m + 1) (logCol Fc ks m (kqAhat Fc ks m η A B l cs) W0 W1 (MO Fc ks m).one)
  have hq0L : (q0 : L) ≠ 0 := by exact_mod_cast hq0
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (a / q0) 1
  simp only [pow_one] at h1
  have hf : T.ev (m + 1) rhs * θ = ((a / q0) * θ)′ + ((-q1 / q0 : ℚ) : L) * (colv * θ) := by
    rw [h1]
    have hq0d : ((q0 : L))′ = 0 := Tower.NestP.deriv_ratCastK (K := L) q0
    have hd : (a / (q0 : L))′ = a′ / q0 := by
      rw [div_eq_mul_inv a, Derivation.leibniz, Derivation.leibniz_inv, hq0d, div_eq_mul_inv]
      simp only [smul_zero, smul_eq_mul, mul_zero, zero_add, neg_zero]
      ring
    rw [hd]
    generalize T.ev (m + 1) rhs = R at hsL ⊢
    push_cast at hsL ⊢
    field_simp
    linear_combination (-2 * θ : L) * hsL
  rw [hf]
  exact (hasElementaryIntegralIn_deriv _).add
    (T.kq_hcolIn m hTr A θ hθ hA0 _ hκ W0 W1 (-q1 / q0))


open Classical in
/-- **`kqDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θ / (∏_q (t − c_q) A(t)ˡ)` (`θ² = A(t)`, `t` a logarithmic level of a certified tower) is
elementary exactly when `b = true`. -/
theorem kqDecideC_correct [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (b : Bool) (hdec : kqDecideC Fc ks lv m η A B l cs ps bound rs cpf = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) ↔ b = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  unfold kqDecideC at hdec
  dsimp only at hdec
  by_cases hr0 : cs.length = 0
  · rw [if_pos hr0] at hdec; exact absurd hdec (by simp)
  rw [if_neg hr0] at hdec
  have hr : 0 < cs.length := Nat.pos_of_ne_zero hr0
  by_cases hok : kqOK Fc ks m A B l cs = true
  swap
  · rw [if_pos (by simpa using hok)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hok])] at hdec
  by_cases hcst : kqConst Fc ks m η A B l cs = true
  swap
  · -- a non-constant squared residue
    rw [if_pos (by simpa using hcst)] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨E, _, _, _, TE, θE, -, ι, sI, c, u, v, hTEn, hθE, -, -, hcd, hu, hv, heq⟩ :=
      T.kq_lift m hn A θ hθ hgen _ hf 1 one_ne_zero
    exact hcst (TE.kq_forward_const hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B l cs hok θE hθE
      sI c u hcd hu v hv heq)
  rw [if_neg (by simp [hcst])] at hdec
  by_cases hcl : kqClass Fc ks m η A B l cs = true
  swap
  · rw [if_pos (by simpa using hcl)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hcl])] at hdec
  have hκ0 := T.kqK_ne m MS.hyp hk A B l cs hok hcst 0 hr
  rcases htors : torsOracleC (redAtKF Fc m rs) (cpf (kqFK Fc ks m η A B l cs)) ps bound
      (kqFK Fc ks m η A B l cs) 2
      (gammaL (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) 1) with
      _ | _ | N
  · rw [htors] at hdec; exact absurd hdec (by simp)
  · -- no torsion
    rw [htors] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨E, _, _, _, TE, θE, s, ι, sI, c, u, v, hTEn, hθE, hs2, hs', hcd, hu, hv, heq⟩ :=
      T.kq_lift m hn A θ hθ hgen _ hf _ hκ0
    exact TE.kq_forward_nontors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B l cs hok hcst hcl hr
      ps bound rs _ htors θE hθE sI c u hcd hu v hv heq s hs2 hs'
  · rw [htors] at hdec
    dsimp only at hdec
    rcases hwit : witW (kqFK Fc ks m η A B l cs) 2 ((kqFK Fc ks m η A B l cs).length - 1)
      (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) N with _ | Wb
    · rw [hwit] at hdec; exact absurd hdec (by simp)
    · rw [hwit] at hdec
      obtain rfl := Option.some.inj hdec
      constructor
      · intro hf
        obtain ⟨E, _, _, _, TE, θE, s, ι, sI, c, u, v, hTEn, hθE, hs2, hs', hcd, hu, hv, heq⟩ :=
          T.kq_lift m hn A θ hθ hgen _ hf _ hκ0
        exact TE.kq_forward_tors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B l cs hok hcst hcl hr
          ps bound rs _ N htors Wb hwit θE hθE sI c u hcd hu v hv heq s hs2 hs'
      · intro h
        exact (T.kq_backward_param m hTr A B l cs η θ hθ hA0 hκ0 _ _ hspecA h).hasElementaryIntegral

open Classical in
/-- **`kqDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θ / (∏_q (t − c_q) A(t)ˡ)` (`θ² = A(t)`, `t` a logarithmic level of a certified tower) is
elementary exactly when `b = true`. -/
theorem kqDecide_correct [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (b : Bool) (hdec : kqDecide Fc ks lv m η A B l cs ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) ↔ b = true :=
  T.kqDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B l cs ps bound rs _ b hdec

end MTower

end Curves.MT
