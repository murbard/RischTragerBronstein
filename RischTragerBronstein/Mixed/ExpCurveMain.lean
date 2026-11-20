import RischTragerBronstein.Mixed.ExpCurveDecide

/-!
# One exponential over a curve: the decision

**`integrateExpCurve_decides`**: let `S` be a curve `F(x, y) = 0` over `ℚ` in a differential field
`K` whose constants lie in an algebraically closed `Kc`, and `t = exp a ∈ K` (`a` a curve code),
transcendental over the function field `F₀ = Kc(x, y)`, with `K = F₀(t)`. For every integrand
`A(t)/D(t)` with coefficients given by curve codes, `integrateExpCurve Fc a A D N` answers for all
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

/-- The model of the function field inside itself. -/
noncomputable abbrev cMF :
    @CField (GPoly (GFrac ℚ)) (cF S) _ (differentialOfDerivClosed (cF_derivClosed hC S hx))
      (curveOps Fc) :=
  (cM hC S hx Fc hSF).restrictTo (cF S) (cF_derivClosed hC S hx) (sem_mem_cF hC S hx Fc hSF)

lemma coe_sem_cMF (a : GPoly (GFrac ℚ)) :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    (((cMF hC S hx Fc hSF).sem a : cF S) : K) = (cM hC S hx Fc hSF).sem a := rfl

include hconstK in
/-- **No new constants in `F₀[t]`**: `P′ tⁿ = P (tⁿ)′` forces `P = e Xⁿ`. -/
lemma exp_no_new_constants (acode : GPoly (GFrac ℚ)) (t : K)
    (ht : t′ = ((cM hC S hx Fc hSF).sem acode)′ * t) (htr0 : Transcendental (cF S) t) :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    letI := polynomialOfDeriv (C (etaF hC S hx Fc hSF acode) * X)
    ∀ (P : (cF S)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : cF S, P = C e * X ^ n := by
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  haveI hDA : DifferentialAlgebra (cF S) K := differentialAlgebra_of_derivClosed _
  set η := etaF hC S hx Fc hSF acode
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht]; rfl
  letI := algebraAdjoinSimple (F := cF S) t
  letI := polynomialOfDeriv (C η * X)
  letI : Differential (cF S)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (cF S)[X] (cF S)⟮t⟯ := isFractionRing_adjoin_simple t htr0
  haveI hDAL : DifferentialAlgebra (cF S)[X] (cF S)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  intro P n hP
  set φ := algebraMap (cF S)[X] (cF S)⟮t⟯ with hφdef
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hXn : φ (X ^ n) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hq : (φ P / φ (X ^ n))′ = 0 := by
    rw [Derivation.leibniz_div, hφdef, deriv_algebraMap, deriv_algebraMap]
    simp only [smul_eq_mul]
    rw [mul_comm (algebraMap (cF S)[X] (cF S)⟮t⟯ (X ^ n)), ← map_mul, ← map_mul, hP, sub_self,
      mul_zero]
  have hqK : (((φ P / φ (X ^ n) : (cF S)⟮t⟯) : K))′ = 0 := congrArg Subtype.val hq
  obtain ⟨c, hc⟩ := hconstK _ hqK
  refine ⟨algebraMap Kc (cF S) c, hinj (Subtype.ext ?_)⟩
  have h1 : ((φ P : (cF S)⟮t⟯) : K) = algebraMap Kc K c * ((φ (X ^ n) : (cF S)⟮t⟯) : K) := by
    have hXn' : ((φ (X ^ n) : (cF S)⟮t⟯) : K) ≠ 0 := fun h ↦ hXn (Subtype.ext h)
    rw [hc, IntermediateField.coe_div]
    field_simp
  rw [h1, algebraMap_adjoinSimple, algebraMap_adjoinSimple, map_mul, aeval_C]
  rfl

set_option maxHeartbeats 4000000 in
include hconstK hmon hdeg in
/-- **One exponential over a curve is decided.** -/
theorem integrateExpCurve_decides (hsh : curveShape Fc = true) (acode : GPoly (GFrac ℚ)) (t : K)
    (ht0 : t ≠ 0) (ht : t′ = ((cM hC S hx Fc hSF).sem acode)′ * t)
    (htr0 : Transcendental (cF S) t)
    (hgen : adjoin (cF S) {t} = (⊤ : IntermediateField (cF S) K))
    (A D : GPoly (GPoly (GFrac ℚ)))
    (hD0 : letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
      GPoly.toPoly (cMF hC S hx Fc hSF) D ≠ 0) :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, integrateExpCurve Fc acode A D N = some b ∧
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
  simp only [integrateExpCurve]
  set O := curveOps Fc with hO
  set w := expCurveW Fc acode with hwdef
  set η := etaF hC S hx Fc hSF acode with hηdef
  have hWp : GPoly.toPoly (cMF hC S hx Fc hSF) w = C η * X := by
    have h0 : (cMF hC S hx Fc hSF).sem O.zero = 0 := (cMF hC S hx Fc hSF).sem_zero
    have h1 : (cMF hC S hx Fc hSF).sem (O.deriv acode) = η := Subtype.ext ((cM hC S hx Fc hSF).sem_deriv acode)
    simp only [hwdef, expCurveW, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
    rw [h0, h1, C_0, zero_add, mul_comm]
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht]; rfl
  have ht' : t′ = algebraMap (cF S) K η * t := by rw [ht]; rfl
  -- the fraction field `F₀⟮t⟯`
  letI := algebraAdjoinSimple (F := cF S) t
  letI dP : Differential (cF S)[X] := polynomialOfDeriv (C η * X)
  letI : Differential (cF S)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (cF S)[X] (cF S)⟮t⟯ := isFractionRing_adjoin_simple t htr0
  haveI hDAL : DifferentialAlgebra (cF S)[X] (cF S)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hD : ∀ P : (cF S)[X], P′ = implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) P := fun P ↦ by rw [hWp]; rfl
  have hφ : ∀ P : (cF S)[X], (((algebraMap (cF S)[X] (cF S)⟮t⟯ P) : (cF S)⟮t⟯) : K) = aeval t P :=
    fun P ↦ algebraMap_adjoinSimple t P
  have hinjt : ∀ P : (cF S)[X], aeval t P = 0 → P = 0 := fun P h ↦
    transcendental_iff.mp htr0 P h
  have hconst := exp_no_new_constants hC S hx hconstK Fc hSF acode t ht htr0
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec (cMF hC S hx Fc hSF) A D hD0
  set sp := GPoly.expSplit O A D with hsp
  set k := sp.2.2.1 with hk
  have hd₁0 : GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.2.2 ≠ 0 := fun h ↦ hD0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (cF S)[X], Irreducible p → p ∣ GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special η (fun P ↦ rfl) hconst hp
      (by rwa [← hD] at hsp')).trans hpd)
  -- (2) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite (cMF hC S hx Fc hSF) w sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (cF S)⟮t⟯) (cMF hC S hx Fc hSF) w sp.1 sp.2.2.2 _ hD hchk
  have hsdvd := GPoly.hermite_s_dvd (cMF hC S hx Fc hSF) w sp.1 sp.2.2.2 hd₁0
  set h := GPoly.hermite O w sp.1 sp.2.2.2 with hh
  set Sd := GPoly.toPoly (cMF hC S hx Fc hSF) h.s with hSd
  have hS0 : Sd ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ Sd := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) polynomial and proper parts
  have hdm := GPoly.divMod_spec (cMF hC S hx Fc hSF) h.b h.s
  have hdeglt := GPoly.divMod_degree_lt (cMF hC S hx Fc hSF) h.b h.s hS0
  set q := (GPoly.divMod O h.b h.s).1 with hq
  set rem := (GPoly.divMod O h.b h.s).2 with hrem
  set Λc := GPoly.add O (GPoly.mul O q (GPoly.monomial O k O.one)) sp.2.1 with hΛc
  have hΛpoly : GPoly.toPoly (cMF hC S hx Fc hSF) Λc = GPoly.toPoly (cMF hC S hx Fc hSF) q * X ^ k + GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.1 := by
    rw [hΛc, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, (cMF hC S hx Fc hSF).sem_one, C_1, one_mul]
  -- (4) the residue polynomial
  have hcop0 : IsCoprime Sd′ Sd :=
    isCoprime_deriv_of_squarefree hsq fun p hp hpS ↦ by
      rw [hD p]; exact hnormal p hp (hpS.trans hsdvd)
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) Sd) Sd := by
    rw [← hD Sd]; exact hcop0
  have hr := GPoly.residuePoly_spec (cMF hC S hx Fc hSF) w rem h.s hS0 hcop
  have hr' : Sd ∣ GPoly.toPoly (cMF hC S hx Fc hSF) (GPoly.residuePoly O w rem h.s) *
      (mapCoeffs Sd + C η * X * derivative Sd) - GPoly.toPoly (cMF hC S hx Fc hSF) rem := by
    have hidd : implicitDeriv (GPoly.toPoly (cMF hC S hx Fc hSF) w) Sd =
        mapCoeffs Sd + C η * X * derivative Sd := by
      rw [hWp, implicitDeriv, Derivation.add_apply, Derivation.smul_apply]
      rfl
    rwa [hidd] at hr
  have hst : aeval t Sd ≠ 0 := fun h0 ↦ hS0 (hinjt _ h0)
  -- (5) the integrand
  set Λ := GPoly.toPoly (cMF hC S hx Fc hSF) Λc with hΛ
  set g : K := (((algebraMap (cF S)[X] (cF S)⟮t⟯ (GPoly.toPoly (cMF hC S hx Fc hSF) h.gn) /
    algebraMap (cF S)[X] (cF S)⟮t⟯ (GPoly.toPoly (cMF hC S hx Fc hSF) h.gd) : (cF S)⟮t⟯)) : K)
    with hg
  have hid' : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.1) /
      aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.2.2) =
      g′ + aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) h.b) / aeval t Sd := by
    have := congrArg Subtype.val hid
    rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hφ, hφ,
      hφ, hφ] at this
    exact this
  have htk : t ^ k ≠ 0 := pow_ne_zero _ ht0
  have hd₁' : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.2.2) ≠ 0 := fun h0 ↦
    hd₁0 (hinjt _ h0)
  have hform : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) /
      aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D) =
      g′ + aeval t Λ / t ^ k + aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) rem) / aeval t Sd := by
    have hA : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) =
        aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.1) * t ^ k +
          aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.1) *
            aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.2.2) := by
      rw [← hsp1]; simp only [map_add, map_mul, map_pow, aeval_X]
    have hDd : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D) =
        t ^ k * aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.2.2) := by
      rw [hsp2]; simp only [map_mul, map_pow, aeval_X]
    have hb : aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) h.b) =
        aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) q) * aeval t Sd +
          aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) rem) := by
      rw [hdm, map_add, map_mul]
    have hΛe : aeval t Λ = aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) q) * t ^ k +
        aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.1) := by
      rw [hΛpoly]; simp only [map_add, map_mul, map_pow, aeval_X]
    calc aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) A) / aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) D)
        = aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.1) /
            aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.2.2) +
          aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.1) / t ^ k := by
          rw [hA, hDd]; field_simp
      _ = g′ + aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) h.b) / aeval t Sd +
          aeval t (GPoly.toPoly (cMF hC S hx Fc hSF) sp.2.1) / t ^ k := by rw [hid']
      _ = _ := by rw [hb, hΛe]; field_simp; ring
  -- (6) the coefficients of `Λ`
  have hcoef : ∀ j, ((Λ.coeff j : cF S) : K) =
      (cM hC S hx Fc hSF).sem (Λc.getD j O.zero) := fun j ↦ by
    rw [hΛ, GPoly.coeff_toPoly]
    by_cases hj : j < Λc.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj]
      rfl
    · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by omega)]
      exact ((cM hC S hx Fc hSF).sem_zero).symm
  have hΛP : ∀ j, j ≠ k → CodeP hC S hx Fc hSF (Λ.coeff j) := fun j _ ↦ ⟨_, hcoef j⟩
  set c0 := Λc.getD k O.zero with hc0
  have hasc : HasElementaryIntegral (algebraMap (cF S) K (Λ.coeff k)) →
      HasElementaryIntegralIn (algebraMap (cF S) K (Λ.coeff k)) := fun hel ↦
    ascend_const hC S hx Fc hSF acode t ht0 ht hgen (constProb Fc c0)
      (shapeOK_constProb Fc hsh _ _ (codeQ_ne_zero _)) rfl _
      ((hcoef k).trans (sem_eq_constProb hC S hx Fc hSF c0)) hel
  have key := expGen_decides (F₀ := cF S) t hgen η ht0 ht' (CodeP hC S hx Fc hSF)
    (curve_expLift hC S hx hconstK Fc hSF hmon hdeg acode t ht0 ht htr0) g Λ k hΛP
    (GPoly.toPoly (cMF hC S hx Fc hSF) rem) Sd
    (GPoly.toPoly (cMF hC S hx Fc hSF) (GPoly.residuePoly O w rem h.s)) hsq hXS hdeglt hst hr' hasc
  rw [← hform] at key
  -- (7) the Risch equations and the algorithm
  have hrde : ∀ j, j ≠ k →
      ((∃ y : cF S, y′ + ((j : cF S) - k) * η * y = Λ.coeff j) ↔
        rdeOK Fc (mulCode Fc ((j : ℤ) - k) acode) (Λc.getD j O.zero) = true) := fun j hj ↦ by
    rw [← rdeOK_iff hC S hx Fc hSF hmon hdeg, sem_mulCode]
    have hder : (((((j : ℤ) - k : ℤ) : K) * (cM hC S hx Fc hSF).sem acode))′ =
        (((j : ℤ) - k : ℤ) : K) * ((cM hC S hx Fc hSF).sem acode)′ := by
      rw [Derivation.leibniz, Derivation.map_intCast]; simp
    rw [hder]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, y.2, ?_⟩
      have := congrArg Subtype.val hy
      rw [hcoef j] at this
      rw [← this]
      push_cast
      rfl
    · rintro ⟨y, hyK, hy⟩
      refine ⟨⟨y, hyK⟩, Subtype.ext ?_⟩
      rw [hcoef j, ← hy]
      push_cast
      rfl
  have hEl := isElementaryExtension_exp (F₀ := cF S) t hgen ht0 ((cM hC S hx Fc hSF).sem acode)
    ⟨⟨_, sem_mem_cF hC S hx Fc hSF acode⟩, rfl⟩ (by rw [logDeriv, ht, mul_div_assoc,
      div_self ht0, mul_one])
  obtain ⟨N₀, hN₀⟩ := const_decides_of hC S hx Fc hSF hsh hEl c0
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b0, hb0, hbiff, hbIn⟩ := hN₀ N hN
  have hrc := GPoly.residueCheck_iff (cMF hC S hx Fc hSF) w rem h.s hS0
  split_ifs with h1 h2
  · refine ⟨false, rfl, ?_, by simp⟩
    simp only [Bool.not_eq_true'] at h1
    simp only [Bool.false_eq_true, iff_false]
    intro hel
    have := hrc.mpr (key.mp hel).1
    rw [this] at h1
    exact Bool.noConfusion h1
  · refine ⟨false, rfl, ?_, by simp⟩
    simp only [Bool.false_eq_true, iff_false]
    intro hel
    have hR := (key.mp hel).2.1
    simp only [Bool.not_eq_true', List.all_eq_false, List.mem_range] at h2
    obtain ⟨j, -, hjf⟩ := h2
    have hjk : j ≠ k := fun h ↦ hjf (by simp [h])
    exact hjf (by rw [(hrde j hjk).mp (hR j hjk)]; simp)
  · refine ⟨b0, hb0, ?_, fun hb1 ↦ ?_⟩
    swap
    · simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2
      have hres := hrc.mp h1
      have hR : ∀ j, j ≠ k → ∃ y : cF S, y′ + ((j : cF S) - k) * η * y = Λ.coeff j := by
        intro j hj
        by_cases hjb : j < Λc.length + k + 1
        · have := List.all_eq_true.mp h2 j (List.mem_range.mpr hjb)
          simp only [Bool.or_eq_true, decide_eq_true_eq] at this
          exact (hrde j hj).mpr (this.resolve_left hj)
        · refine ⟨0, ?_⟩
          have h0 : Λ.coeff j = 0 := by
            apply Subtype.ext
            rw [hcoef j, List.getD_eq_default _ _ (by omega)]
            exact (cM hC S hx Fc hSF).sem_zero
          rw [h0]; simp
      have hc := hbIn hb1
      rw [← hcoef k] at hc
      rw [hform]
      exact expGen_suff_in (F₀ := cF S) t η ht0 ht' g Λ k _ Sd _ hsq hdeglt hst hr' hres hR hc
    rw [key, ← hbiff, ← hcoef k]
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2
    have hres := hrc.mp h1
    have hR : ∀ j, j ≠ k → ∃ y : cF S, y′ + ((j : cF S) - k) * η * y = Λ.coeff j := by
      intro j hj
      by_cases hjb : j < Λc.length + k + 1
      · have := List.all_eq_true.mp h2 j (List.mem_range.mpr hjb)
        simp only [Bool.or_eq_true, decide_eq_true_eq] at this
        exact (hrde j hj).mpr (this.resolve_left hj)
      · refine ⟨0, ?_⟩
        have h0 : Λ.coeff j = 0 := by
          apply Subtype.ext
          rw [hcoef j, List.getD_eq_default _ _ (by omega)]
          exact (cM hC S hx Fc hSF).sem_zero
        rw [h0]; simp
    exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hres, hR, h⟩⟩

end Main

end Curves
