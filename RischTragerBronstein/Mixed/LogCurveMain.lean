import RischTragerBronstein.Mixed.LogCurveLift
import RischTragerBronstein.Computable.PrimNElem

/-!
# One logarithm over a curve: the decision

**`integrateLogCurve_decides`**: let `S` be a curve `F(x, y) = 0` over `ℚ` in a differential field
`K` whose constants lie in an algebraically closed `Kc`, and `t = log u ∈ K` (`u` a curve code),
transcendental over the function field `F₀ = Kc(x, y)`, with `K = F₀(t)`. For every integrand
`A(t)/D(t)` with coefficients given by curve codes, `integrateLogCurve Fc u A D N` answers for all
large `N`, and the answer is `true` exactly when the integrand has an elementary integral.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup NFC

section Main

universe u

variable {Kc K : Type u} [Field Kc] [Field K] [Algebra Kc K] [Differential Kc] [Differential K]
variable [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K] [IsAlgClosed Kc]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc K) (hx : S.x′ = 1)
  (hconstK : ∀ z : K, z′ = 0 → z ∈ Set.range (algebraMap Kc K))
  (Fc : BPoly ℚ) (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))
  (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)

include hconstK in
/-- **No new constants in `F₀[t]`** for a primitive `t`. -/
lemma prim_no_new_constants (η : cF S) (t : K)
    (ht : letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
      t′ = algebraMap (cF S) K η)
    (htr0 : Transcendental (cF S) t) :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    letI := polynomialOfDeriv (C η)
    ∀ P : (cF S)[X], P′ = 0 → ∃ e : cF S, P = C e := by
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  haveI hDA : DifferentialAlgebra (cF S) K := differentialAlgebra_of_derivClosed _
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht]
  letI := algebraAdjoinSimple (F := cF S) t
  letI := polynomialOfDeriv (C η)
  letI : Differential (cF S)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (cF S)[X] (cF S)⟮t⟯ := isFractionRing_adjoin_simple t htr0
  haveI hDAL : DifferentialAlgebra (cF S)[X] (cF S)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  intro P hP
  set φ := algebraMap (cF S)[X] (cF S)⟮t⟯ with hφdef
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hq : (φ P)′ = 0 := by rw [hφdef, deriv_algebraMap, hP, map_zero]
  have hqK : (((φ P : (cF S)⟮t⟯) : K))′ = 0 := congrArg Subtype.val hq
  obtain ⟨c, hc⟩ := hconstK _ hqK
  refine ⟨algebraMap Kc (cF S) c, hinj (Subtype.ext ?_)⟩
  rw [← hc, algebraMap_adjoinSimple, aeval_C]
  rfl

set_option maxHeartbeats 4000000 in
include hconstK hmon hdeg in
/-- **One logarithm over a curve is decided.** -/
theorem integrateLogCurve_decides (hsh : curveShape Fc = true) (ucode : GPoly (GFrac ℚ)) (t : K)
    (hu0 : (cM hC S hx Fc hSF).sem ucode ≠ 0)
    (ht : t′ = logDeriv ((cM hC S hx Fc hSF).sem ucode))
    (htr0 : Transcendental (cF S) t)
    (hgen : adjoin (cF S) {t} = (⊤ : IntermediateField (cF S) K))
    (A D : GPoly (GPoly (GFrac ℚ)))
    (hD0 : letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
      GPoly.toPoly (cMF hC S hx Fc hSF) D ≠ 0) :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, integrateLogCurve Fc ucode A D N = some b ∧
      (HasElementaryIntegral (aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) /
        aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D)) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn (aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) /
        aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D))) := by
  classical
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  haveI hDA : DifferentialAlgebra (cF S) K := differentialAlgebra_of_derivClosed _
  haveI hcharF : CharZero (cF S) := ⟨fun m n h ↦ by
    have := congrArg (fun z : cF S ↦ (z : K)) h
    simpa using this⟩
  simp only [integrateLogCurve]
  set O := curveOps Fc with hO
  set ηc := etaCode Fc ucode with hηc
  set w : GPoly (GPoly (GFrac ℚ)) := [ηc] with hwdef
  set η : cF S := (cMF hC S hx Fc hSF).sem ηc with hηdef
  have hηK : (η : K) = (cM hC S hx Fc hSF).sem ηc := coe_sem_cMF hC S hx Fc hSF ηc
  have ht1 : t′ = (cM hC S hx Fc hSF).sem ηc := by rw [ht, hηc, sem_etaCode]
  have ht' : t′ = algebraMap (cF S) K η := ht1
  have hWp : GPoly.toPoly (cMF hC S hx Fc hSF) w = C η := by
    simp only [hwdef, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
    rfl
  have hw : t′ = aeval t (C η) := by rw [aeval_C, ht']
  -- the fraction field `F₀⟮t⟯`
  letI := algebraAdjoinSimple (F := cF S) t
  letI dP : Differential (cF S)[X] := polynomialOfDeriv (C η)
  letI : Differential (cF S)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (cF S)[X] (cF S)⟮t⟯ := isFractionRing_adjoin_simple t htr0
  haveI hDAL : DifferentialAlgebra (cF S)[X] (cF S)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hD : ∀ P : (cF S)[X], P′ = implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) P := fun P ↦ by
    rw [hWp]; rfl
  have hφ : ∀ P : (cF S)[X], (((algebraMap (cF S)[X] (cF S)⟮t⟯ P) : (cF S)⟮t⟯) : K) = aeval t P :=
    fun P ↦ algebraMap_adjoinSimple t P
  have hinjt : ∀ P : (cF S)[X], aeval t P = 0 → P = 0 := fun P h ↦
    transcendental_iff.mp htr0 P h
  have hconst := prim_no_new_constants hC S hx hconstK η t ht' htr0
  have hnormAll : ∀ p : (cF S)[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive η (fun P ↦ rfl) hconst hp
  have hnormal : ∀ p : (cF S)[X], Irreducible p → p ∣ GPoly.toPoly (cMF hC S hx Fc hSF) D →
      ¬p ∣ implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) p := fun p hp _ h ↦
    hnormAll p hp (by rwa [hD p])
  -- (1) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite (cMF hC S hx Fc hSF) w A D hnormal hD0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (cF S)⟮t⟯) (cMF hC S hx Fc hSF) w A D _ hD hchk
  set h := GPoly.hermite O w A D with hh
  set Sd := GPoly.toPoly (cMF hC S hx Fc hSF) h.s with hSd
  have hS0 : Sd ≠ 0 := hsq.ne_zero
  have hsep : Sd.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  -- (2) polynomial and proper parts
  have hdm := GPoly.divMod_spec (cMF hC S hx Fc hSF) h.b h.s
  have hdeglt := GPoly.divMod_degree_lt (cMF hC S hx Fc hSF) h.b h.s hS0
  set q := (GPoly.divMod O h.b h.s).1 with hq
  set rem := (GPoly.divMod O h.b h.s).2 with hrem
  -- (3) the residue polynomial
  have hcop0 : IsCoprime Sd′ Sd := isCoprime_deriv_of_squarefree hsq fun p hp _ ↦ hnormAll p hp
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) Sd) Sd := by
    rw [← hD Sd]; exact hcop0
  have hr := GPoly.residuePoly_spec (cMF hC S hx Fc hSF) w rem h.s hS0 hcop
  set r := GPoly.toPoly (cMF hC S hx Fc hSF) (GPoly.residuePoly O w rem h.s) with hrdef
  have hidd : implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) Sd = mapCoeffs Sd + C η * derivative Sd := by
    rw [hWp, implicitDeriv, Derivation.add_apply, Derivation.smul_apply]
    rfl
  have hr' : Sd ∣ r * (mapCoeffs Sd + C η * derivative Sd) - GPoly.toPoly (cMF hC S hx Fc hSF) rem := by
    rwa [hidd] at hr
  have hst : aeval t Sd ≠ 0 := fun h0 ↦ hS0 (hinjt _ h0)
  -- (4) the integrand
  set g : K := (((algebraMap (cF S)[X] (cF S)⟮t⟯ (GPoly.toPoly (cMF hC S hx Fc hSF) h.gn) /
    algebraMap (cF S)[X] (cF S)⟮t⟯ (GPoly.toPoly (cMF hC S hx Fc hSF) h.gd) : (cF S)⟮t⟯)) : K) with hg
  set Pq := GPoly.toPoly (cMF hC S hx Fc hSF) q with hPq
  set Pr := GPoly.toPoly (cMF hC S hx Fc hSF) rem with hPr
  have hform : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) / aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D) =
      g′ + (aeval t Pq + aeval t Pr / aeval t Sd) := by
    have hid' : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) /
        aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D) =
        g′ + aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) h.b) / aeval t Sd := by
      have := congrArg Subtype.val hid
      rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hφ, hφ,
        hφ, hφ] at this
      exact this
    rw [hid', hdm, map_add, map_mul, ← hSd]
    field_simp
  -- (5) the coefficients of the polynomial part
  have hcoef : ∀ j, ((Pq.coeff j : cF S) : K) = (cM hC S hx Fc hSF).sem (q.getD j O.zero) := fun j ↦ by
    rw [hPq, GPoly.coeff_toPoly]
    by_cases hj : j < q.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj]
      rfl
    · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by omega)]
      exact ((cM hC S hx Fc hSF).sem_zero).symm
  have hdq : Pq.natDegree ≤ q.length := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    apply Subtype.ext
    rw [hcoef N, List.getD_eq_default _ _ (by exact_mod_cast hN.le), (cM hC S hx Fc hSF).sem_zero]
    rfl
  have hlogIn : Sd ∣ residueTest r Sd → HasElementaryIntegralIn (aeval t Pr / aeval t Sd) :=
    fun hT ↦ hasElementaryIntegralIn_of_residueTest t η 0
      (by rw [ht', map_zero, zero_mul, add_zero]) 1 one_ne_zero
      (by rw [map_zero]; simp [logDeriv]) Sd Pr r hsep hst hdeglt
      (by rwa [C_0, zero_mul, add_zero]) hT
  have hE : IsElementaryExtension (cF S) K :=
    isElementaryExtension_log' t hgen ((cM hC S hx Fc hSF).sem ucode) ⟨⟨_, sem_mem_cF hC S hx Fc hSF ucode⟩, rfl⟩
      hu0 ht
  have hlift := curve_primLift hC S hx hconstK Fc hSF hmon hdeg ηc t ht1 htr0
  -- (6) necessity
  have hnec : HasElementaryIntegral (aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) / aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D)) →
      Sd ∣ residueTest r Sd ∧ ∃ R, primChain Fc ηc q q.length O.zero = some R ∧
        HasElementaryIntegral ((cM hC S hx Fc hSF).sem (logConst Fc ηc q R)) := by
    intro hf
    have h1 : HasElementaryIntegral (aeval t Pq + aeval t Pr / aeval t Sd) := by
      have := hf.sub_in (hasElementaryIntegralIn_deriv g)
      rwa [hform, add_sub_cancel_left] at this
    have hT : Sd ∣ residueTest r Sd := by
      obtain ⟨E, _, _, _, _, hE1, gE, hgE⟩ := h1
      obtain ⟨F₁, hcl, hF₀, htrE, -⟩ := hlift E
      exact residue_of_lift_prim (F₀ := cF S) t hgen η ht' Pq Pr Sd r hsq hr' E hE1 gE hgE hst
        F₁ hcl (fun f ↦ hF₀ _ f.2) htrE
    refine ⟨hT, ?_⟩
    have h2 : HasElementaryIntegral (aeval t Pq) := by
      have := h1.sub_in (hlogIn hT)
      rwa [add_sub_cancel_right] at this
    obtain ⟨E2, _, _, _, _, hE2, g2, hg2⟩ := h2
    haveI : CharZero E2 := charZero_of_injective_algebraMap (algebraMap K E2).injective
    obtain ⟨F₂, hcl2, hF₂, htr2, hchain⟩ := hlift E2
    obtain ⟨p, hpF, hrec, htop, hgsum⟩ := poly_of_lift_prim t hgen η ht' Pq q.length hdq E2 hE2
      g2 hg2 F₂ hcl2 (fun f ↦ hF₂ _ f.2) htr2
    obtain ⟨R, hR, κ, hκ0, hκ⟩ := hchain q q.length p hpF (fun i h1 _ ↦ by
      have := hrec i h1
      rw [show algebraMap (cF S) K (Pq.coeff i) = (cM hC S hx Fc hSF).sem (q.getD i O.zero) from hcoef i] at this
      exact this) htop
    refine ⟨R, hR, E2, inferInstance, inferInstance, inferInstance, inferInstance, hE2,
      g2 - ∑ j ∈ Finset.range (q.length + 1), p (j + 1) * algebraMap K E2 t ^ (j + 1) +
        κ * algebraMap K E2 t, ?_⟩
    rw [Derivation.map_add, hgsum, Derivation.leibniz, hκ0, deriv_algebraMap, ht1, hκ,
      sem_logConst, show algebraMap (cF S) K (Pq.coeff 0) = (cM hC S hx Fc hSF).sem (q.getD 0 O.zero) from hcoef 0]
    simp only [smul_eq_mul, mul_zero, add_zero, map_sub, map_mul]
    change _ - algebraMap K E2 ((cM hC S hx Fc hSF).sem ηc) * _ + _ = _
    ring
  -- (7) sufficiency, given the chain
  have hsuff : ∀ R, primChain Fc ηc q q.length O.zero = some R → Sd ∣ residueTest r Sd →
      HasElementaryIntegralIn ((cM hC S hx Fc hSF).sem (logConst Fc ηc q R)) →
      HasElementaryIntegralIn (aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) /
        aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D)) := by
    intro R hR hT hc
    obtain ⟨P, -, hPrec, ⟨q0, hq0⟩, hP1⟩ := primChain_sound hC S hx Fc hSF ηc q q.length O.zero
      R hR
    have htop : (P (q.length + 1))′ = 0 := by
      rw [hq0, Derivation.map_add, deriv_ratCast' hC, add_zero, (cM hC S hx Fc hSF).sem_zero, Derivation.map_zero]
    have hsum := prim_sum_deriv t ((cM hC S hx Fc hSF).sem ηc) ht1 (fun i ↦ (cM hC S hx Fc hSF).sem (q.getD i O.zero)) P q.length
      (fun i h1 h2 ↦ hPrec i h1 h2) htop
    have hA : aeval t Pq = ∑ i ∈ Finset.range (q.length + 1), (cM hC S hx Fc hSF).sem (q.getD i O.zero) * t ^ i := by
      rw [aeval_eq_sum_range' (n := q.length + 1) (by omega)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Algebra.smul_def, ← hcoef i]
      rfl
    have hL := ((hc.add (hasElementaryIntegralIn_deriv
      (∑ j ∈ Finset.range (q.length + 1), P (j + 1) * t ^ (j + 1)))).add (hlogIn hT)).add
      (hasElementaryIntegralIn_deriv g)
    rw [hform]
    convert hL using 1
    rw [hsum, sem_logConst, hP1, hA]
    ring
  -- (8) the algorithm
  cases hres : GPoly.residueCheck O w rem h.s with
  | false =>
    refine ⟨0, fun N _ ↦ ⟨false, by simp, ?_, by simp⟩⟩
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    have := (GPoly.residueCheck_iff (cMF hC S hx Fc hSF) w rem h.s hS0).mpr (hnec hf).1
    rw [hres] at this
    exact Bool.noConfusion this
  | true =>
    have hT : Sd ∣ residueTest r Sd := (GPoly.residueCheck_iff (cMF hC S hx Fc hSF) w rem h.s hS0).mp hres
    cases hch : primChain Fc ηc q q.length O.zero with
    | none =>
      refine ⟨0, fun N _ ↦ ⟨false, by simp, ?_, by simp⟩⟩
      simp only [Bool.false_eq_true, iff_false]
      intro hf
      obtain ⟨R, hR, -⟩ := (hnec hf).2
      rw [hch] at hR
      simp at hR
    | some R =>
      obtain ⟨N₀, hN₀⟩ := const_decides_of hC S hx Fc hSF hsh hE (logConst Fc ηc q R)
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨b, hb, hiff, hIn⟩ := hN₀ N hN
      refine ⟨b, by simpa using hb, ⟨fun hf ↦ ?_, fun hb1 ↦ (hsuff R hch hT (hIn hb1)).hasElementaryIntegral⟩,
        fun hb1 ↦ hsuff R hch hT (hIn hb1)⟩
      obtain ⟨-, R', hR', hc⟩ := hnec hf
      rw [hch, Option.some.injEq] at hR'
      subst hR'
      exact hiff.mp hc

end Main

end Curves
