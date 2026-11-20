import RischTragerBronstein.Computable.MixNComplete2
import RischTragerBronstein.Computable.PrimNElem
import RischTragerBronstein.Liouville.ExponentialLaurentPart
import RischTragerBronstein.Liouville.StepResidueTestExp

/-!
# Mixed towers: the decision `elemM`

`elemM_sound`: a positive answer gives an elementary integral over every elementary extension of
`E`. `elemM_complete`: a Liouville form of `A - K₀` over `F m` (`K₀ ∈ Kc(x)`) forces a positive
answer. Primitive levels as in `PrimNElem`; at an exponential level `t′ = b t` the logarithmic part
is decided by the residue test with `θ = t` (`residueTest_step_exponential`), the non-zero Laurent
coefficients by the Risch equations `Yₑ′ + e b Yₑ = Λₑ` (`rdeM`, complete), and the coefficient of
`t⁰` one level down (`laurent_part_liouville`: the slack `∑ cᵢ nᵢ b` lies in `Kc(x)`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.MixN.MixTower

open Tower.PrimN

variable {Kc : Type*} {E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
variable [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc] {ks : List Kind}
variable (T : MixTower Kc E ks)

lemma const_mem (m : ℕ) (z : E) (hz : z′ = 0) : z ∈ T.F m := by
  obtain ⟨κ, rfl⟩ := T.hCall z hz
  exact (T.F m).algebraMap_mem κ

/-! ### The rational base -/

/-- Every element of `Kc(x)` has an elementary integral over every elementary extension. -/
theorem rational_in (q : GFrac ℚ) : HasElementaryIntegralIn (evx Kc T.x q) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  by_cases hq : (CPoly.toPoly q.2).map (algebraMap ℚ Kc) = 0
  · have : evx Kc T.x q = (0 : E)′ := by simp [evx, hq]
    rw [this]
    exact hasElementaryIntegralIn_deriv 0
  intro E' _ _ _ _ _
  let _ : Algebra Kc E' := ((algebraMap E E').comp (algebraMap Kc E)).toAlgebra
  have hDA : DifferentialAlgebra Kc E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap Kc E a))′ = algebraMap E E' (algebraMap Kc E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hx : (algebraMap E E' T.x)′ = 1 := by rw [deriv_algebraMap, T.hx, map_one]
  have haev : ∀ P : Kc[X], algebraMap E E' (aeval T.x P) = aeval (algebraMap E E' T.x) P :=
    fun P ↦ by
      rw [aeval_def, aeval_def, hom_eval₂]
      rfl
  have := hasElementaryIntegral_rational_in T.hC (algebraMap E E' T.x) hx
    ((CPoly.toPoly q.1).map (algebraMap ℚ Kc)) _ hq 0
  rw [map_zero, zero_add] at this
  rw [evx, map_div₀, haev, haev]
  exact this

/-! ### Soundness -/

lemma implicitDeriv_C_eq {F' : Type*} [Field F'] [Differential F'] (η : F') (S : F'[X]) :
    implicitDeriv (C η) S = mapCoeffs S + (C η + C 0 * X) * derivative S := by
  simp [implicitDeriv]

/-- **Soundness of `elemM`, primitive step.** -/
theorem elemM_sound_prim (m : ℕ) (h : T.Tr (m + 1)) {η : Code 1} (hk : kind ks m = .prim η)
    (ih : ∀ A, elemM ks m A = true →
      HasElementaryIntegralIn ((((T.MP m (fun i hi ↦ h i (by omega))).sem A : T.F m)) : E))
    (A : Code (m + 2)) (hel : elemM ks (m + 1) A = true) :
    HasElementaryIntegralIn ((((T.MP (m + 1) h).sem A : T.F (m + 1))) : E) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (Nat.lt_succ_self m)
  have hwP : T.wPoly m = C (T.ratF m η) := by simp only [wPoly, hk]
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  simp only [elemM, hk, Bool.or_eq_true, Bool.and_eq_true] at hel
  by_cases hz : GPoly.isZero (opsM ks m) A.2 = true
  · have hA2 := (GPoly.isZero_iff M _).mp hz
    have h0 : ((M'.sem A : T.F (m + 1)) : E) = (0 : E)′ := by
      rw [hsem A, hA2, map_zero, div_zero]
      simp
    rw [h0]
    exact hasElementaryIntegralIn_deriv 0
  obtain ⟨hres, hmatch⟩ := hel.resolve_left hz
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr A.1 A.2 hA2 (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  generalize GPoly.hermite (opsM ks m) (wK ks m) A.1 A.2 = hr at hval hsq hres hmatch
  have hdm := GPoly.divMod_spec M hr.b hr.s
  have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hdm hdeg hres hmatch
  generalize hpd : polyDown (opsM ks m) (lift m η) η (limIntM ks m)
    (constC (m + 1)) qr.1 (qr.1.length - 1) (opsM ks m).zero [] = pd at hmatch
  rcases pd with _ | ⟨Q, Ys⟩
  · simp at hmatch
  simp only at hmatch
  have hG := ih _ hmatch
  set ηv := T.ratF m η with hηdef
  set t := T.ts m with ht
  have hw : t′ = aeval t (C ηv) := by rw [← hwP]; exact T.deriv_ts_aeval m
  have hS : GPoly.toPoly M hr.s ≠ 0 := hsq.ne_zero
  have hinjt : Function.Injective (aeval (R := T.F m) t) :=
    transcendental_iff_injective.mp htr
  have hst : aeval t (GPoly.toPoly M hr.s) ≠ 0 := fun h0 ↦
    hS (hinjt (h0.trans (map_zero _).symm))
  -- the logarithmic part
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M (wK ks m)) (GPoly.toPoly M hr.s))
      (GPoly.toPoly M hr.s) := by
    rw [T.toPoly_wK]
    letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hsq (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  have hrs := GPoly.residuePoly_spec M (wK ks m) qr.2 hr.s hS hcop
  rw [T.toPoly_wK, hwP, implicitDeriv_C_eq] at hrs
  have hT := (GPoly.residueCheck_iff M (wK ks m) qr.2 hr.s hS).mp hres
  have hlog : HasElementaryIntegralIn
      (aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s)) :=
    hasElementaryIntegralIn_of_residueTest (F := T.F m) t ηv 0
      (by rw [map_zero, zero_mul, add_zero, hw, aeval_C]; try rfl) 1 one_ne_zero
      (by rw [logDeriv_one, map_zero]) _ _ _ (PerfectField.separable_iff_squarefree.mpr hsq)
      hst hdeg hrs hT
  -- the polynomial part
  have hsolve : ∀ G W r, limIntM ks m G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
        M.sem G := by
    intro G W r hr
    obtain ⟨h1, h2⟩ := T.limIntM_sound m hm G W r.1 r.2 hr
    refine ⟨h1, Subtype.ext ?_⟩
    rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
    exact h2
  have hinit : implicitDeriv (C (M.sem (lift m η)))
      (X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M ((opsM ks m).zero :: [])) =
      X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M (qr.1.drop (qr.1.length - 1 + 1)) +
        C (((qr.1.length - 1 : ℕ) + 1 : T.F m) * M.sem (opsM ks m).zero *
          M.sem (lift m η)) * X ^ (qr.1.length - 1) := by
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [M.sem_zero]
  have hpoly := polyDown_sound M (lift m η) η (fun w ↦ M.sem (lift m w))
    (limIntM ks m) (constC (m + 1)) hsolve rfl (T.sem_constC m hm) T.deriv_ratCast qr.1
    (qr.1.length - 1) (opsM ks m).zero [] Q Ys hinit hpd
  rw [show M.sem (lift m η) = ηv from T.sem_lift_F m hm η] at hpoly
  have hqP : GPoly.toPoly M qr.1 = implicitDeriv (C ηv) (X * GPoly.toPoly M (Q :: Ys)) +
      C (M.sem ((opsM ks m).add (qr.1.getD 0 (opsM ks m).zero)
        ((opsM ks m).neg ((opsM ks m).mul Q (lift m η))))) := by
    have h0 := toPoly_drop M qr.1 0
    rw [List.drop_zero] at h0
    rw [hpoly, M.sem_add, M.sem_neg, M.sem_mul, show M.sem (lift m η) = ηv from T.sem_lift_F m hm η]
    conv_lhs => rw [h0]
    simp only [C_add, C_neg, C_mul, zero_add]
    ring
  have hq : HasElementaryIntegralIn (aeval t (GPoly.toPoly M qr.1)) := by
    rw [hqP, map_add, ← deriv_aeval_eq_implicitDeriv t (C ηv) hw, aeval_C]
    exact (hasElementaryIntegralIn_deriv _).add hG
  -- the whole integrand
  have hA : ((M'.sem A : T.F (m + 1)) : E) =
      ((T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) : T.F (m + 1)) : E)′ +
        (aeval t (GPoly.toPoly M qr.1) +
          aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s)) := by
    rw [hsem A, hval, hdm]
    simp only [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_mul,
      coe_deriv, coe_phi, map_add, map_mul]
    simp only [← hM, ← ht]
    field_simp
  rw [hA]
  exact (hasElementaryIntegralIn_deriv _).add (hq.add hlog)


lemma implicitDeriv_CX_eq {F' : Type*} [Field F'] [Differential F'] (b : F') (S : F'[X]) :
    implicitDeriv (C b * X) S = mapCoeffs S + (C 0 + C b * X) * derivative S := by
  simp [implicitDeriv]

/-- **Soundness of `elemM`, exponential step.** -/
theorem elemM_sound_exp (m : ℕ) (h : T.Tr (m + 1)) {b : Code 1} (hk : kind ks m = .exp b)
    (ih : ∀ A, elemM ks m A = true →
      HasElementaryIntegralIn ((((T.MP m (fun i hi ↦ h i (by omega))).sem A : T.F m)) : E))
    (A : Code (m + 2)) (hel : elemM ks (m + 1) A = true) :
    HasElementaryIntegralIn ((((T.MP (m + 1) h).sem A : T.F (m + 1))) : E) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (Nat.lt_succ_self m)
  set bv := T.ratF m b with hbv
  have hwP : T.wPoly m = C bv * X := by simp only [wPoly, hk]; rfl
  set t := T.ts m with ht
  have hw : t′ = aeval t (C bv * X) := by rw [← hwP]; exact T.deriv_ts_aeval m
  have hts0 : t ≠ 0 := T.hts0 m b hk
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  simp only [elemM, hk, Bool.or_eq_true, Bool.and_eq_true] at hel
  by_cases hz : GPoly.isZero (opsM ks m) A.2 = true
  · have hA2 := (GPoly.isZero_iff M _).mp hz
    have h0 : ((M'.sem A : T.F (m + 1)) : E) = (0 : E)′ := by
      rw [hsem A, hA2, map_zero, div_zero]
      simp
    rw [h0]
    exact hasElementaryIntegralIn_deriv 0
  obtain ⟨⟨hres, hls⟩, hel0⟩ := hel.resolve_left hz
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M A.1 A.2 hA2
  generalize GPoly.expSplit (opsM ks m) A.1 A.2 = sp at hsp1 hsp2 hsp3 hres hls hel0
  obtain ⟨u, v, k, d₁⟩ := sp
  simp only at hsp1 hsp2 hsp3 hres hls hel0
  have hd₁ : GPoly.toPoly M d₁ ≠ 0 := fun h0 ↦ hA2 (by rw [hsp2, h0, mul_zero])
  have hsdvd := GPoly.hermite_s_dvd M (wK ks m) u d₁ hd₁
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr u d₁ hd₁ (fun p hp hpd hdvd ↦
    T.normal_exp m htr hk p hp (fun hXp ↦ hsp3 (hXp.trans hpd)) hdvd)
  generalize GPoly.hermite (opsM ks m) (wK ks m) u d₁ = hr at hval hsq hsdvd hres hls hel0
  rw [← hM] at hval hsq
  have hsX : ¬X ∣ GPoly.toPoly M hr.s := fun h ↦ hsp3 (h.trans hsdvd)
  have hdm := GPoly.divMod_spec M hr.b hr.s
  have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hdm hdeg hres hls hel0
  set Λ := GPoly.add (opsM ks m) (GPoly.mul (opsM ks m) qr.1 (GPoly.monomial (opsM ks m) k
    (opsM ks m).one)) v with hΛ
  have hΛp : GPoly.toPoly M Λ = GPoly.toPoly M qr.1 * X ^ k + GPoly.toPoly M v := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  have hinjt : Function.Injective (aeval (R := T.F m) t) := transcendental_iff_injective.mp htr
  have hst : aeval t (GPoly.toPoly M hr.s) ≠ 0 := fun h0 ↦
    hsq.ne_zero (hinjt (h0.trans (map_zero _).symm))
  have hd₁t : aeval t (GPoly.toPoly M d₁) ≠ 0 := fun h0 ↦
    hd₁ (hinjt (h0.trans (map_zero _).symm))
  -- the logarithmic part
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M (wK ks m)) (GPoly.toPoly M hr.s))
      (GPoly.toPoly M hr.s) := by
    rw [T.toPoly_wK]
    letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hsq (fun p hp hps ↦
      T.normal_exp m htr hk p hp (fun hXp ↦ hsX (hXp.trans hps)))
  have hrs := GPoly.residuePoly_spec M (wK ks m) qr.2 hr.s hsq.ne_zero hcop
  rw [T.toPoly_wK, hwP, implicitDeriv_CX_eq] at hrs
  have hT := (GPoly.residueCheck_iff M (wK ks m) qr.2 hr.s hsq.ne_zero).mp hres
  have hlog : HasElementaryIntegralIn
      (aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s)) :=
    hasElementaryIntegralIn_of_residueTest (F := T.F m) t 0 bv
      (by rw [map_zero, zero_add, hw, map_mul, aeval_C, aeval_X]; try rfl) t hts0
      (by unfold logDeriv; rw [hw, map_mul, aeval_C, aeval_X]; field_simp; try rfl) _ _ _
      (PerfectField.separable_iff_squarefree.mpr hsq) hst hdeg hrs hT
  -- the Laurent part
  obtain ⟨Ys, hYs⟩ := Option.isSome_iff_exists.mp hls
  obtain ⟨hYl, hYspec⟩ := laurentSolve_spec (O := opsM ks m) b (rdeM ks m) Λ k _ Ys hYs
  set N := max Λ.length (k + 1) with hN
  set P := GPoly.toPoly M Ys with hP
  have hPid : implicitDeriv (C bv * X) P - C ((k : T.F m) * bv) * P =
      GPoly.toPoly M Λ - C (M.sem (Λ.getD k (opsM ks m).zero)) * X ^ k := by
    refine Polynomial.ext fun j ↦ ?_
    rw [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_sub, coeff_C_mul_X_pow, hP,
      coeff_toPoly_getD, coeff_toPoly_getD]
    by_cases hjN : j < N
    · by_cases hjk : j = k
      · subst hjk
        rw [(hYspec j hjN).1 rfl, M.sem_zero, if_pos rfl]
        simp
      · rw [if_neg hjk]
        have := T.rdeM_sound m hm _ _ _ ((hYspec j hjN).2 hjk)
        rw [T.ratF_smulQ] at this
        push_cast at this
        linear_combination this
    · have hj1 : Ys.getD j (opsM ks m).zero = (opsM ks m).zero :=
        List.getD_eq_default _ _ (by omega)
      have hj2 : Λ.getD j (opsM ks m).zero = (opsM ks m).zero :=
        List.getD_eq_default _ _ (by omega)
      rw [hj1, hj2, M.sem_zero, if_neg (by omega)]
      simp
  have hder : ∀ Q : (T.F m)[X], (aeval t Q)′ = aeval t (implicitDeriv (C bv * X) Q) :=
    deriv_aeval_eq_implicitDeriv t (C bv * X) hw
  have hk0 : t ^ k ≠ 0 := pow_ne_zero k hts0
  have hlaur : aeval t (GPoly.toPoly M Λ) / t ^ k =
      (aeval t P / t ^ k)′ + ((M.sem (Λ.getD k (opsM ks m).zero) : T.F m) : E) := by
    have hP' := congrArg (aeval t) hPid
    simp only [map_sub, map_mul, aeval_C, map_pow, aeval_X] at hP'
    have htk : (t ^ k)′ = (k : E) * (bv : E) * t ^ k := by
      rw [show (t ^ k : E) = aeval t (X ^ k : (T.F m)[X]) by simp, hder, deriv_X_pow, map_mul,
        aeval_C, map_pow, aeval_X]
      simp [map_mul]
    rw [Derivation.leibniz_div, hder, htk]
    simp only [smul_eq_mul]
    simp only [map_natCast, IntermediateField.algebraMap_apply] at hP'
    field_simp
    linear_combination -hP'
  set g : T.F (m + 1) := T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) with hg
  have hvalA : ((M'.sem A : T.F (m + 1)) : E) = (g : E)′ +
      aeval t (GPoly.toPoly M Λ) / t ^ k +
        aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s) := by
    have hv' : aeval t (GPoly.toPoly M u) / aeval t (GPoly.toPoly M d₁) =
        (g : E)′ + aeval t (GPoly.toPoly M qr.1) +
          aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s) := by
      have := congrArg (fun z : T.F (m + 1) ↦ (z : E)) hval
      simp only [IntermediateField.coe_add, IntermediateField.coe_div, coe_deriv, coe_phi] at this
      simp only [← ht] at this
      rw [this, hdm, map_add, map_mul]
      field_simp
      ring
    rw [hsem, IntermediateField.coe_div, coe_phi, coe_phi, ← hsp1, hsp2, hΛp]
    simp only [← ht]
    simp only [map_add, map_mul, map_pow, aeval_X] at hv' ⊢
    have hv'' : aeval t (GPoly.toPoly M u) = ((g : E)′ + aeval t
        (GPoly.toPoly M qr.1) + aeval t (GPoly.toPoly M qr.2) /
          aeval t (GPoly.toPoly M hr.s)) * aeval t (GPoly.toPoly M d₁) := by
      rw [← hv']; field_simp
    rw [hv'']
    field_simp
    ring
  rw [hvalA, hlaur]
  exact ((hasElementaryIntegralIn_deriv (g : E)).add
    ((hasElementaryIntegralIn_deriv (aeval t P / t ^ k)).add (ih _ hel0))).add hlog

/-- **Soundness of `elemM`**. -/
theorem elemM_sound : ∀ (m : ℕ) (h : T.Tr m) (A : Code (m + 1)), elemM ks m A = true →
    HasElementaryIntegralIn ((((T.MP m h).sem A : T.F m)) : E)
  | 0, h, A, _ => by
    rw [show (((T.MP 0 h).sem A : T.F 0) : E) = evx Kc T.x A from T.sem_model0 A]
    exact T.rational_in A
  | m + 1, h, A, hel => by
    have ih := elemM_sound m (fun i hi ↦ h i (by omega))
    cases hk : kind ks m with
    | prim η => exact T.elemM_sound_prim m h hk ih A hel
    | exp b => exact T.elemM_sound_exp m h hk ih A hel

/-! ### Completeness -/

lemma coe_logDeriv_F {m : ℕ} (y : T.F m) : ((logDeriv y : T.F m) : E) = logDeriv (y : E) := by
  unfold logDeriv
  rw [IntermediateField.coe_div, coe_deriv]

/-- A Liouville form at level `m`, up to an element of `Kc(x)`. -/
def LiouSol (m : ℕ) (h : T.Tr m) (A : Code (m + 1)) : Prop :=
  ∃ K0 ∈ T.F 0, LiouvilleIn (T.F m) ((((T.MP m h).sem A : T.F m) : E) - K0)

/-- **Completeness of `elemM`, primitive step.** -/
theorem elemM_complete_prim (m : ℕ) (hnd : T.ND (m + 1)) {η : Code 1} (hk : kind ks m = .prim η)
    (ih : ∀ A, T.LiouSol m (T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))).1 A → elemM ks m A = true)
    (A : Code (m + 2)) (hsol : T.LiouSol (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 A) :
    elemM ks (m + 1) A = true := by
  classical
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  set hm := (T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))).1 with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 with hM'
  have htr : Transcendental (T.F m) (T.ts m) := (T.tr_noHom_of_ND (m + 1) hnd).1 m (Nat.lt_succ_self m)
  have hη : ∀ y : T.F m, y′ ≠ T.ratF m η := by
    have := hnd.2 m (Nat.lt_succ_self m)
    simp only [hk] at this
    exact this
  have hwP : T.wPoly m = C (T.ratF m η) := by simp only [wPoly, hk]
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  obtain ⟨K0, hK0, ι, s, c, u, v, hdata, hv, heq⟩ := hsol
  simp only [elemM, hk, Bool.or_eq_true, Bool.and_eq_true]
  by_cases hz : GPoly.isZero (opsM ks m) A.2 = true
  · exact Or.inl hz
  right
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr A.1 A.2 hA2 (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  generalize GPoly.hermite (opsM ks m) (wK ks m) A.1 A.2 = hr at hval hsq ⊢
  have hdm := GPoly.divMod_spec M hr.b hr.s
  have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hdm hdeg ⊢
  set ηv := T.ratF m η with hηdef
  set t := T.ts m with ht
  have hw : t′ = aeval t (C ηv) := by rw [← hwP]; exact T.deriv_ts_aeval m
  have hS : GPoly.toPoly M hr.s ≠ 0 := hsq.ne_zero
  have hinjt : Function.Injective (aeval (R := T.F m) t) :=
    transcendental_iff_injective.mp htr
  have hst : aeval t (GPoly.toPoly M hr.s) ≠ 0 := fun h0 ↦
    hS (hinjt (h0.trans (map_zero _).symm))
  set g : T.F (m + 1) := T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) with hg
  have hA : ((M'.sem A : T.F (m + 1)) : E) = (g : E)′ +
        (aeval t (GPoly.toPoly M qr.1) +
          aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s)) := by
    rw [hsem A, hval, hdm]
    simp only [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_mul,
      coe_deriv, coe_phi, map_add, map_mul, hg]
    simp only [← hM, ← ht]
    field_simp
  set K0' : T.F m := ⟨K0, T.F_mono (Nat.zero_le m) hK0⟩ with hK0'
  -- the constants as elements of `F m`
  set c' : ι → T.F m := fun i ↦ if h : (c i)′ = 0 then ⟨c i, T.const_mem m _ h⟩ else 0 with hc'
  have hc'E : ∀ i ∈ s, ((c' i : T.F m) : E) = c i := fun i hi ↦ by
    simp only [hc']
    rw [dif_pos (hdata i hi).1]
  have hc'd : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦
    Subtype.ext (by rw [coe_deriv, hc'E i hi, (hdata i hi).1]; rfl)
  have hconst : ∀ z ∈ (T.F m)⟮t⟯, z′ = 0 → z ∈ Set.range (algebraMap (T.F m) E) :=
    fun z _ hz0 ↦ by
      obtain ⟨κ, rfl⟩ := T.hCall z hz0
      exact ⟨algebraMap Kc (T.F m) κ, rfl⟩
  have hvg : v - (g : E) ∈ (T.F m)⟮t⟯ :=
    (T.mem_F_succ).mp (sub_mem hv g.2)
  -- the residue test
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M (wK ks m)) (GPoly.toPoly M hr.s))
      (GPoly.toPoly M hr.s) := by
    rw [T.toPoly_wK]
    letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hsq (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  have hrs := GPoly.residuePoly_spec M (wK ks m) qr.2 hr.s hS hcop
  rw [T.toPoly_wK, hwP] at hrs
  have hsum : ∑ i ∈ s, c i * logDeriv (u i) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [← hc'E i hi]; rfl
  have hbv : aeval t ((GPoly.toPoly M qr.1 - C K0') * GPoly.toPoly M hr.s + GPoly.toPoly M qr.2) /
      aeval t (GPoly.toPoly M hr.s) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) + (v - (g : E))′ := by
    have hK : algebraMap (T.F m) E K0' = K0 := rfl
    rw [← hsum, map_sub, ← add_sub_assoc, ← heq, hA]
    simp only [map_add, map_mul, map_sub, aeval_C, hK]
    field_simp
    ring
  have hT : GPoly.toPoly M hr.s ∣ residueTest (GPoly.toPoly M
      (GPoly.residuePoly (opsM ks m) (wK ks m) qr.2 hr.s)) (GPoly.toPoly M hr.s) := by
    refine residueTest_step_primitive (F := T.F m) t htr ηv (by rw [hw, aeval_C]; try rfl) hconst s c' u
      (fun i hi ↦ ⟨(T.mem_F_succ).mp (hdata i hi).2.1, (hdata i hi).2.2⟩) hc'd (v - (g : E))
      hvg _ _ _ hsq ?_ hbv
    have : GPoly.toPoly M (GPoly.residuePoly (opsM ks m) (wK ks m) qr.2 hr.s) *
        (mapCoeffs (GPoly.toPoly M hr.s) + C ηv * derivative (GPoly.toPoly M hr.s)) -
        ((GPoly.toPoly M qr.1 - C K0') * GPoly.toPoly M hr.s + GPoly.toPoly M qr.2) =
        (GPoly.toPoly M (GPoly.residuePoly (opsM ks m) (wK ks m) qr.2 hr.s) *
          implicitDeriv (C ηv) (GPoly.toPoly M hr.s) - GPoly.toPoly M qr.2) -
        (GPoly.toPoly M qr.1 - C K0') * GPoly.toPoly M hr.s := by
      simp [implicitDeriv]
      ring
    rw [this]
    exact dvd_sub hrs (dvd_mul_left _ _)
  refine ⟨(GPoly.residueCheck_iff M (wK ks m) qr.2 hr.s hS).mpr hT, ?_⟩
  -- the fraction field `F m (tₘ)` and the polynomial part of the Liouville form
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (C ηv)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
    algebraMap_adjoinSimple _
  have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : E) = logDeriv (y : E) := by
    intro y
    unfold logDeriv
    rw [IntermediateField.coe_div]
    rfl
  set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if h : u i ∈ (T.F m)⟮t⟯ then ⟨u i, h⟩ else 1 with hu''d
  have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : E) = u i := fun i hi ↦ by
    simp only [hu''d]
    rw [dif_pos ((T.mem_F_succ).mp (hdata i hi).2.1)]
  obtain ⟨e, Pv, he, hPv⟩ := poly_part_liouville (K := (T.F m)⟮t⟯) (fun _ ↦ rfl) s c' u''
    (fun i hi h0 ↦ (hdata i hi).2.2 (by rw [← hu'' i hi, h0]; rfl)) ⟨v - (g : E), hvg⟩
    (GPoly.toPoly M qr.1 - C K0') _ ⟨_, _, hS, hdeg, rfl⟩ (Subtype.ext (by
      rw [IntermediateField.coe_add, IntermediateField.coe_div, hcoe, hcoe, hcoe,
        IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum]
      have h1 : aeval t (GPoly.toPoly M qr.1 - C K0') +
          aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s) =
          aeval t ((GPoly.toPoly M qr.1 - C K0') * GPoly.toPoly M hr.s +
            GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s) := by
        rw [map_add, map_mul]
        field_simp
      rw [h1, hbv]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcoe, aeval_C, hcoeLog, hu'' i hi]))
  set SL := ∑ i ∈ s, c' i * logDeriv (e i) with hSL
  -- the coefficients of the true polynomial part
  have hcoeffD : ∀ k, (Pv.coeff k)′ + ηv * (Pv.coeff (k + 1) * (k + 1)) =
      (GPoly.toPoly M qr.1 - C K0' - C SL).coeff k := fun k ↦ by
    rw [← coeff_implicitDeriv_C, hPv]
  have hP : ∀ k, 1 ≤ k → (Pv.coeff k)′ + ((k : T.F m) + 1) * Pv.coeff (k + 1) *
      M.sem (lift m η) = M.sem (qr.1.getD k (opsM ks m).zero) := by
    intro k hk
    have := hcoeffD k
    simp only [coeff_sub, coeff_C, if_neg (show k ≠ 0 by omega), sub_zero,
      coeff_toPoly_getD] at this
    rw [show M.sem (lift m η) = ηv from T.sem_lift_F m hm η]
    linear_combination this
  have hconstP : ∀ Q : (T.F m)[X], implicitDeriv (C ηv) Q = 0 → ∃ e : T.F m, Q = C e :=
    fun Q hQ ↦ const_of_implicitDeriv_eq_zero ηv hη hQ
  have hdegP : Pv.natDegree ≤ qr.1.length - 1 + 1 := by
    refine natDegree_le_succ_of_natDegree_deriv_le ηv hconstP ?_
    rw [hPv]
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
      (max_le (natDegree_toPoly_le M _) ?_)) ?_) <;>
      rw [natDegree_C] <;> exact Nat.zero_le _
  have htop : (Pv.coeff (qr.1.length - 1 + 1))′ = 0 := by
    have := hcoeffD (qr.1.length - 1 + 1)
    rw [coeff_eq_zero_of_natDegree_lt (by omega : Pv.natDegree < qr.1.length - 1 + 1 + 1),
      zero_mul, mul_zero, add_zero] at this
    simp only [coeff_sub, coeff_C, if_neg (show qr.1.length - 1 + 1 ≠ 0 by omega), sub_zero,
      coeff_toPoly_getD, List.getD_eq_default _ _ (show qr.1.length ≤ qr.1.length - 1 + 1 by omega),
      M.sem_zero] at this
    exact this
  obtain ⟨κ₀, hκ₀⟩ := T.const_F _ htop
  have hsolve : ∀ G W r, limIntM ks m G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
        M.sem G := by
    intro G W r hr
    obtain ⟨h1, h2⟩ := T.limIntM_sound m hm G W r.1 r.2 hr
    refine ⟨h1, Subtype.ext ?_⟩
    rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
    exact h2
  have hcomp : ∀ G W (y : T.F m) (c : List Kc), c.length = W.length →
      y′ + (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F m) c * M.sem (lift m w)) c
        W).sum = M.sem G → limIntM ks m G W ≠ none := by
    intro G W y c hl hy
    refine T.limIntM_complete m (hnd.mono (Nat.le_succ m)) G W ⟨y, y.2, c, hl, ?_⟩
    have := congrArg Subtype.val hy
    rw [IntermediateField.coe_add, T.coe_zipWithK_sum] at this
    exact this
  obtain ⟨Q', Ys', hpd, κ, hκ⟩ := polyDown_complete M (lift m η) η
    (fun w ↦ M.sem (lift m w)) (limIntM ks m) (constC (m + 1)) hsolve hcomp rfl
    (by rw [show M.sem (lift m η) = ηv from T.sem_lift_F m hm η]; exact hη) T.const_F T.deriv_algebraMap_Kc T.deriv_ratCast qr.1 Pv
    hP (qr.1.length - 1) (opsM ks m).zero [] ⟨-κ₀, by rw [M.sem_zero, hκ₀, map_neg]; ring⟩
  rw [hpd]
  simp only
  -- the `t⁰` coefficient has a Liouville form over `F m`, up to `Kc(x)`
  refine ih _ ⟨K0 - algebraMap Kc E κ * (ηv : E), ?_,
    ι, s, c, fun i ↦ (e i : E), (Pv.coeff 0 : E), fun i hi ↦ ⟨(hdata i hi).1, (e i).2,
      fun h0 ↦ he i hi (Subtype.ext h0)⟩, (Pv.coeff 0).2, ?_⟩
  · exact sub_mem hK0 (mul_mem ((T.F 0).algebraMap_mem κ) (T.evx_mem _))
  · have h0 := hcoeffD 0
    rw [coeff_sub, coeff_sub, coeff_C_zero, coeff_C_zero, coeff_toPoly_getD] at h0
    have hF : M.sem ((opsM ks m).add (qr.1.getD 0 (opsM ks m).zero)
        ((opsM ks m).neg ((opsM ks m).mul Q' (lift m η)))) -
        (K0' - algebraMap Kc (T.F m) κ * ηv) = SL + (Pv.coeff 0)′ := by
      rw [M.sem_add, M.sem_neg, M.sem_mul, hκ, show M.sem (lift m η) = ηv from T.sem_lift_F m hm η]
      push_cast at h0
      linear_combination -h0
    have hsumE : ((SL : T.F m) : E) = ∑ i ∈ s, c i * logDeriv ((e i : T.F m) : E) := by
      rw [hSL, AddSubmonoidClass.coe_finset_sum]
      exact Finset.sum_congr rfl fun i hi ↦ by
        rw [IntermediateField.coe_mul, hc'E i hi, T.coe_logDeriv_F]
    calc _ = (((M.sem ((opsM ks m).add (qr.1.getD 0 (opsM ks m).zero)
          ((opsM ks m).neg ((opsM ks m).mul Q' (lift m η)))) -
          (K0' - algebraMap Kc (T.F m) κ * ηv) : T.F m)) : E) := rfl
      _ = ((SL + (Pv.coeff 0)′ : T.F m) : E) := congrArg Subtype.val hF
      _ = _ := by rw [IntermediateField.coe_add, hsumE, coe_deriv]


/-- **Completeness of `elemM`, exponential step.** -/
theorem elemM_complete_exp (m : ℕ) (hnd : T.ND (m + 1)) {b : Code 1} (hk : kind ks m = .exp b)
    (ih : ∀ A, T.LiouSol m (T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))).1 A → elemM ks m A = true)
    (A : Code (m + 2)) (hsol : T.LiouSol (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 A) :
    elemM ks (m + 1) A = true := by
  classical
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  obtain ⟨hm, hnh⟩ := T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 with hM'
  have htr : Transcendental (T.F m) (T.ts m) := (T.tr_noHom_of_ND (m + 1) hnd).1 m (by omega)
  have hbD : T.Adm b := T.adm_of_kind hk
  have hbN : T.NotSpan (expsBelow ks m) b := by
    have := hnd.2 m (Nat.lt_succ_self m)
    rw [hk] at this
    exact this
  set bv := T.ratF m b with hbv
  have hwP : T.wPoly m = C bv * X := by simp only [wPoly, hk]; rfl
  set t := T.ts m with ht
  have hw : t′ = aeval t (C bv * X) := by rw [← hwP]; exact T.deriv_ts_aeval m
  have hts0 : t ≠ 0 := T.hts0 m b hk
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  obtain ⟨K0, hK0, ι, s, c, u, v, hdata, hv, heq⟩ := hsol
  simp only [elemM, hk, Bool.or_eq_true, Bool.and_eq_true]
  by_cases hz : GPoly.isZero (opsM ks m) A.2 = true
  · exact Or.inl hz
  right
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M A.1 A.2 hA2
  generalize GPoly.expSplit (opsM ks m) A.1 A.2 = sp at hsp1 hsp2 hsp3 ⊢
  obtain ⟨u₀, v₀, k, d₁⟩ := sp
  simp only at hsp1 hsp2 hsp3 ⊢
  have hd₁ : GPoly.toPoly M d₁ ≠ 0 := fun h0 ↦ hA2 (by rw [hsp2, h0, mul_zero])
  have hsdvd := GPoly.hermite_s_dvd M (wK ks m) u₀ d₁ hd₁
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr u₀ d₁ hd₁ (fun p hp hpd hdvd ↦
    T.normal_exp m htr hk p hp (fun hXp ↦ hsp3 (hXp.trans hpd)) hdvd)
  generalize GPoly.hermite (opsM ks m) (wK ks m) u₀ d₁ = hr at hval hsq hsdvd ⊢
  rw [← hM] at hval hsq
  have hsX : ¬X ∣ GPoly.toPoly M hr.s := fun h ↦ hsp3 (h.trans hsdvd)
  have hdm := GPoly.divMod_spec M hr.b hr.s
  have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hdm hdeg ⊢
  set Λ := GPoly.add (opsM ks m) (GPoly.mul (opsM ks m) qr.1 (GPoly.monomial (opsM ks m) k
    (opsM ks m).one)) v₀ with hΛ
  have hΛp : GPoly.toPoly M Λ = GPoly.toPoly M qr.1 * X ^ k + GPoly.toPoly M v₀ := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  have hinjt : Function.Injective (aeval (R := T.F m) t) := transcendental_iff_injective.mp htr
  have hst : aeval t (GPoly.toPoly M hr.s) ≠ 0 := fun h0 ↦
    hsq.ne_zero (hinjt (h0.trans (map_zero _).symm))
  have hd₁t : aeval t (GPoly.toPoly M d₁) ≠ 0 := fun h0 ↦
    hd₁ (hinjt (h0.trans (map_zero _).symm))
  have hk0 : t ^ k ≠ 0 := pow_ne_zero k hts0
  set g : T.F (m + 1) := T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) with hg
  have hvalA : ((M'.sem A : T.F (m + 1)) : E) = (g : E)′ +
      aeval t (GPoly.toPoly M Λ) / t ^ k +
        aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s) := by
    have hv' : aeval t (GPoly.toPoly M u₀) / aeval t (GPoly.toPoly M d₁) =
        (g : E)′ + aeval t (GPoly.toPoly M qr.1) +
          aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s) := by
      have := congrArg (fun z : T.F (m + 1) ↦ (z : E)) hval
      simp only [IntermediateField.coe_add, IntermediateField.coe_div, coe_deriv, coe_phi] at this
      simp only [← ht] at this
      rw [this, hdm, map_add, map_mul]
      field_simp
      ring
    rw [hsem, IntermediateField.coe_div, coe_phi, coe_phi, ← hsp1, hsp2, hΛp]
    simp only [← ht]
    simp only [map_add, map_mul, map_pow, aeval_X] at hv' ⊢
    have hv'' : aeval t (GPoly.toPoly M u₀) = ((g : E)′ + aeval t
        (GPoly.toPoly M qr.1) + aeval t (GPoly.toPoly M qr.2) /
          aeval t (GPoly.toPoly M hr.s)) * aeval t (GPoly.toPoly M d₁) := by
      rw [← hv']; field_simp
    rw [hv'']
    field_simp
    ring
  set K0' : T.F m := ⟨K0, T.F_mono (Nat.zero_le m) hK0⟩ with hK0'
  set c' : ι → T.F m := fun i ↦ if h : (c i)′ = 0 then ⟨c i, T.const_mem m _ h⟩ else 0 with hc'
  have hc'E : ∀ i ∈ s, ((c' i : T.F m) : E) = c i := fun i hi ↦ by
    simp only [hc']
    rw [dif_pos (hdata i hi).1]
  have hc'd : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦
    Subtype.ext (by rw [coe_deriv, hc'E i hi, (hdata i hi).1]; rfl)
  have hconst : ∀ z ∈ (T.F m)⟮t⟯, z′ = 0 → z ∈ Set.range (algebraMap (T.F m) E) :=
    fun z _ hz0 ↦ by
      obtain ⟨κ, rfl⟩ := T.hCall z hz0
      exact ⟨algebraMap Kc (T.F m) κ, rfl⟩
  have hvg : v - (g : E) ∈ (T.F m)⟮t⟯ := (T.mem_F_succ).mp (sub_mem hv g.2)
  have hsum : ∑ i ∈ s, c i * logDeriv (u i) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [← hc'E i hi]; rfl
  -- the residue test
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M (wK ks m)) (GPoly.toPoly M hr.s))
      (GPoly.toPoly M hr.s) := by
    rw [T.toPoly_wK]
    letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hsq (fun p hp hps ↦
      T.normal_exp m htr hk p hp (fun hXp ↦ hsX (hXp.trans hps)))
  have hrs := GPoly.residuePoly_spec M (wK ks m) qr.2 hr.s hsq.ne_zero hcop
  rw [T.toPoly_wK, hwP] at hrs
  have hB : aeval t ((GPoly.toPoly M Λ - C K0' * X ^ k) * GPoly.toPoly M hr.s +
      GPoly.toPoly M qr.2 * X ^ k) / (aeval t (GPoly.toPoly M hr.s) * t ^ k) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) + (v - (g : E))′ := by
    have hK : algebraMap (T.F m) E K0' = K0 := rfl
    rw [← hsum, map_sub, ← add_sub_assoc, ← heq, hvalA]
    simp only [map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, hK]
    field_simp
    ring
  have hT : GPoly.toPoly M hr.s ∣ residueTest (GPoly.toPoly M
      (GPoly.residuePoly (opsM ks m) (wK ks m) qr.2 hr.s)) (GPoly.toPoly M hr.s) := by
    refine residueTest_step_exponential (F := T.F m) t htr bv
      (by rw [hw, map_mul, aeval_C, aeval_X]; try rfl) hconst s c' u
      (fun i hi ↦ ⟨(T.mem_F_succ).mp (hdata i hi).2.1, (hdata i hi).2.2⟩) hc'd (v - (g : E))
      hvg ((GPoly.toPoly M Λ - C K0' * X ^ k) * GPoly.toPoly M hr.s + GPoly.toPoly M qr.2 * X ^ k)
      (GPoly.toPoly M qr.2) (GPoly.toPoly M hr.s)
      (GPoly.toPoly M (GPoly.residuePoly (opsM ks m) (wK ks m) qr.2 hr.s)) k hsq hsX
      ⟨GPoly.toPoly M Λ - C K0' * X ^ k, by ring⟩ ?_ hB
    have e : mapCoeffs (GPoly.toPoly M hr.s) + C bv * X * derivative (GPoly.toPoly M hr.s) =
        implicitDeriv (C bv * X) (GPoly.toPoly M hr.s) := by
      simp [implicitDeriv, mul_assoc]
    rw [e]
    exact hrs
  -- the Laurent part of the Liouville form
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (C bv * X)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
    algebraMap_adjoinSimple _
  have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : E) = logDeriv (y : E) := by
    intro y
    unfold logDeriv
    rw [IntermediateField.coe_div]
    rfl
  set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if h : u i ∈ (T.F m)⟮t⟯ then ⟨u i, h⟩ else 1 with hu''d
  have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : E) = u i := fun i hi ↦ by
    simp only [hu''d]
    rw [dif_pos ((T.mem_F_succ).mp (hdata i hi).2.1)]
  obtain ⟨e, n, V, kv, he, hid⟩ := laurent_part_liouville (K := (T.F m)⟮t⟯) (fun _ ↦ rfl) s c' u''
    (fun i hi h0 ↦ (hdata i hi).2.2 (by rw [← hu'' i hi, h0]; rfl)) ⟨v - (g : E), hvg⟩
    (GPoly.toPoly M Λ - C K0' * X ^ k) k
    (algebraMap (T.F m)[X] (T.F m)⟮t⟯ (GPoly.toPoly M qr.2) /
      algebraMap (T.F m)[X] (T.F m)⟮t⟯ (GPoly.toPoly M hr.s))
    ⟨_, _, hsq.ne_zero, hsX, hdeg, rfl⟩ (Subtype.ext (by
      rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hcoe,
        hcoe, hcoe, hcoe, IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum]
      have h1 : aeval t (GPoly.toPoly M Λ - C K0' * X ^ k) / aeval t (X ^ k : (T.F m)[X]) +
          aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s) =
          aeval t ((GPoly.toPoly M Λ - C K0' * X ^ k) * GPoly.toPoly M hr.s +
            GPoly.toPoly M qr.2 * X ^ k) / (aeval t (GPoly.toPoly M hr.s) * t ^ k) := by
        simp only [map_add, map_mul, map_pow, aeval_X]
        field_simp
      rw [h1, hB]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcoe, aeval_C, hcoeLog, hu'' i hi]))
  set S := ∑ i ∈ s, c' i * (logDeriv (e i) + (n i : T.F m) * bv) with hS
  have key : ∀ j, (GPoly.toPoly M Λ - C K0' * X ^ k).coeff j =
      if k ≤ j + kv then (C S * X ^ kv + (implicitDeriv (C bv * X) V - C ((kv : T.F m) * bv) * V)).coeff
        (j + kv - k) else 0 := fun j ↦ by
    have := congrArg (fun Q ↦ Q.coeff (j + kv)) hid
    simp only [coeff_mul_X_pow'] at this
    rw [if_pos (Nat.le_add_left kv j), Nat.add_sub_cancel] at this
    exact this
  have hWc : ∀ i, (implicitDeriv (C bv * X) V - C ((kv : T.F m) * bv) * V).coeff i =
      (V.coeff i)′ + ((i : T.F m) - kv) * bv * V.coeff i := fun i ↦ by
    rw [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul]
    ring
  have hΛc : ∀ j, (GPoly.toPoly M Λ - C K0' * X ^ k).coeff j =
      M.sem (Λ.getD j (opsM ks m).zero) - (if j = k then K0' else 0) := fun j ↦ by
    rw [coeff_sub, coeff_toPoly_getD, coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  refine ⟨⟨(GPoly.residueCheck_iff M (wK ks m) qr.2 hr.s hsq.ne_zero).mpr hT, ?_⟩, ?_⟩
  · -- the non-zero Laurent coefficients
    refine laurentSolve_isSome (opsM ks m) b (rdeM ks m) Λ k _ fun j _ hjk ↦ ?_
    rw [Option.isSome_iff_ne_none]
    have hz0 : ((((j : ℤ) - k : ℤ) : ℚ)) ≠ 0 := by
      have : ((j : ℤ) - k : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    have h1 := key j
    rw [hΛc, if_neg hjk, sub_zero] at h1
    by_cases hkj : k ≤ j + kv
    · rw [if_pos hkj, coeff_add, coeff_C_mul_X_pow, if_neg (by omega), zero_add, hWc] at h1
      refine T.rdeM_complete m (hnd.mono (Nat.le_succ m)) _ (hbD.smul _) (hbN.smul hz0) _
        (V.coeff (j + kv - k)) ?_
      rw [T.ratF_smulQ, h1]
      push_cast [Nat.cast_sub hkj]
      ring
    · rw [if_neg hkj] at h1
      refine T.rdeM_complete m (hnd.mono (Nat.le_succ m)) _ (hbD.smul _) (hbN.smul hz0) _ 0 ?_
      rw [h1]
      simp
  · -- the coefficient of `t⁰`, one level down
    have h1 := key k
    rw [hΛc, if_pos rfl, if_pos (by omega), coeff_add, coeff_C_mul_X_pow, Nat.add_sub_cancel_left,
      if_pos rfl, hWc, sub_self, zero_mul, zero_mul, add_zero] at h1
    refine ih _ ⟨K0 + (∑ i ∈ s, c i * (n i : E)) * (bv : E), ?_, ι, s, c, fun i ↦ (e i : E),
      (V.coeff kv : E), fun i hi ↦ ⟨(hdata i hi).1, (e i).2, fun h0 ↦ he i hi (Subtype.ext h0)⟩,
      (V.coeff kv).2, ?_⟩
    · refine add_mem hK0 (mul_mem (sum_mem fun i hi ↦ mul_mem (T.const_mem 0 _ (hdata i hi).1)
        (intCast_mem _ _)) ?_)
      exact T.evx_mem _
    · have h2 := congrArg Subtype.val h1
      rw [AddSubgroupClass.coe_sub, IntermediateField.coe_add, coe_deriv, hS,
        AddSubmonoidClass.coe_finset_sum] at h2
      rw [show ((K0' : T.F m) : E) = K0 from rfl] at h2
      have hS' : ∑ i ∈ s, (((c' i * (logDeriv (e i) + (n i : T.F m) * bv) : T.F m)) : E) =
          ∑ i ∈ s, c i * logDeriv ((e i : T.F m) : E) + (∑ i ∈ s, c i * (n i : E)) * (bv : E) := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [IntermediateField.coe_mul, hc'E i hi, IntermediateField.coe_add,
          IntermediateField.coe_mul, T.coe_logDeriv_F]
        push_cast
        ring
      rw [hS'] at h2
      linear_combination h2

/-- **Completeness of `elemM`**. -/
theorem elemM_complete : ∀ (m : ℕ) (hnd : T.ND m) (A : Code (m + 1)),
    T.LiouSol m (T.tr_noHom_of_ND m hnd).1 A → elemM ks m A = true
  | 0, _, _, _ => rfl
  | m + 1, hnd, A, h => by
    have ih := elemM_complete m (hnd.mono (Nat.le_succ m))
    cases hk : kind ks m with
    | prim η => exact T.elemM_complete_prim m hnd hk ih A h
    | exp b => exact T.elemM_complete_exp m hnd hk ih A h

end Tower.MixN.MixTower
