import RischTragerBronstein.Computable.PrimNComplete
import RischTragerBronstein.Liouville.PrimitivePolyPart
import RischTragerBronstein.Liouville.StepResidueTest
import RischTragerBronstein.Liouville.ResidueTestSufficient
import RischTragerBronstein.Rational.IntegrableIn
import RischTragerBronstein.Elementary.Sum

/-!
# Towers of `n` primitives: the decision `elemP`

`elemP_sound`: if `elemP ηs m A = true`, then `A` has an elementary integral over every elementary
extension of `E` (`HasElementaryIntegralIn`).

`elemP_complete`: if `A - K₀` (some `K₀ ∈ Kc(x)`) has a Liouville form over `F m` — constants
times logarithmic derivatives plus a derivative, all in `F m` — then `elemP ηs m A = true`.
The slack `K₀ ∈ Kc(x)` is what descending through a primitive `t` leaves behind (`c₀ η`), and is
harmless because every element of `Kc(x)` has an elementary integral.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

universe u

variable {F : Type u} [Field F] [Differential F]

/-- Sums of integrands that are integrable over every elementary extension. -/
theorem HasElementaryIntegralIn.add {f₁ f₂ : F} (h₁ : HasElementaryIntegralIn f₁)
    (h₂ : HasElementaryIntegralIn f₂) : HasElementaryIntegralIn (f₁ + f₂) := by
  intro E _ _ _ _ hE
  rw [map_add]
  refine (h₁ E hE).add_in ?_
  intro E' _ _ _ _ hE'
  let _ : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra F E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap F E a))′ = algebraMap E E' (algebraMap F E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  exact h₂ E' (hE.trans hE')

/-- Constant multiples of integrands that are integrable over every elementary extension. -/
theorem HasElementaryIntegralIn.const_mul {f : F} (h : HasElementaryIntegralIn f) (c : F)
    (hc : c′ = 0) : HasElementaryIntegralIn (c * f) := by
  intro E _ _ _ _ hE
  obtain ⟨K, _, _, _, _, hK, g, hg⟩ := h E hE
  let _ : Algebra F K := ((algebraMap E K).comp (algebraMap F E)).toAlgebra
  have hDA : DifferentialAlgebra F K :=
    ⟨fun a ↦ by
      change (algebraMap E K (algebraMap F E a))′ = algebraMap E K (algebraMap F E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, hK,
    algebraMap E K (algebraMap F E c) * g, ?_⟩
  rw [Derivation.leibniz, hg, deriv_algebraMap, deriv_algebraMap, hc, map_zero, map_zero,
    smul_zero, add_zero, smul_eq_mul, map_mul, map_mul]

theorem HasElementaryIntegralIn.congr {f g : F} (h : HasElementaryIntegralIn f) (hfg : f = g) :
    HasElementaryIntegralIn g := hfg ▸ h

end Differential

namespace Tower.PrimN.PrimTower

variable {Kc : Type*} {E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
variable [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : List (Code 1)}
variable (T : PrimTower Kc E ηs)

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

/-- **Soundness of `elemP`**: a positive answer yields an elementary integral, over every
elementary extension of `E`. -/
theorem elemP_sound : ∀ (m : ℕ) (hnd : T.ND m) (A : Code (m + 1)), elemP ηs m A = true →
    HasElementaryIntegralIn ((((T.MP m (T.tr_of_ND hnd)).sem A : T.F m)) : E)
  | 0, hnd, A, _ => by
    rw [show (((T.MP 0 (T.tr_of_ND hnd)).sem A : T.F 0) : E) = evx Kc T.x A from T.sem_model0 A]
    exact T.rational_in A
  | m + 1, hnd, A, hel => by
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
    set hm := T.tr_of_ND (hnd.mono (Nat.le_succ m)) with hhm
    set M := T.MP m hm with hM
    set M' := T.MP (m + 1) (T.tr_of_ND hnd) with hM'
    have htr : Transcendental (T.F m) (T.ts m) := T.tr_of_ND hnd m (Nat.lt_succ_self m)
    have hη : ∀ y : T.F m, y′ ≠ T.etaF m m := hnd m (Nat.lt_succ_self m)
    have hsem : ∀ q : Code (m + 2),
        M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
    simp only [elemP, Bool.or_eq_true, Bool.and_eq_true] at hel
    by_cases hz : GPoly.isZero (opsP ηs m) A.2 = true
    · have hA2 := (GPoly.isZero_iff M _).mp hz
      have h0 : ((M'.sem A : T.F (m + 1)) : E) = (0 : E)′ := by
        rw [hsem A, hA2, map_zero, div_zero]
        simp
      rw [h0]
      exact hasElementaryIntegralIn_deriv 0
    obtain ⟨hres, hmatch⟩ := hel.resolve_left hz
    have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr hη A.1 A.2 hA2
    generalize GPoly.hermite (opsP ηs m) (wP ηs m) A.1 A.2 = hr at hval hsq hres hmatch
    have hdm := GPoly.divMod_spec M hr.b hr.s
    have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
    generalize GPoly.divMod (opsP ηs m) hr.b hr.s = qr at hdm hdeg hres hmatch
    generalize hpd : polyDown (opsP ηs m) (lift m (eta ηs m)) (eta ηs m) (limIntP ηs m)
      (constC (m + 1)) qr.1 (qr.1.length - 1) (opsP ηs m).zero [] = pd at hmatch
    rcases pd with _ | ⟨Q, Ys⟩
    · simp at hmatch
    simp only at hmatch
    have hG := elemP_sound m (hnd.mono (Nat.le_succ m)) _ hmatch
    set η := T.etaF m m with hηdef
    set t := T.ts m with ht
    have hw : t′ = aeval t (C η) := by rw [aeval_C]; exact T.ht m
    have hS : GPoly.toPoly M hr.s ≠ 0 := hsq.ne_zero
    have hinjt : Function.Injective (aeval (R := T.F m) t) :=
      transcendental_iff_injective.mp htr
    have hst : aeval t (GPoly.toPoly M hr.s) ≠ 0 := fun h0 ↦
      hS (hinjt (h0.trans (map_zero _).symm))
    -- the logarithmic part
    have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M (wP ηs m)) (GPoly.toPoly M hr.s))
        (GPoly.toPoly M hr.s) := by
      rw [T.toPoly_wP]
      letI : Differential (T.F m)[X] := polynomialOfDeriv (C η)
      exact isCoprime_deriv_of_squarefree hsq (fun p hp _ ↦ T.normal hη p hp)
    have hrs := GPoly.residuePoly_spec M (wP ηs m) qr.2 hr.s hS hcop
    rw [T.toPoly_wP, implicitDeriv_C_eq] at hrs
    have hT := (GPoly.residueCheck_iff M (wP ηs m) qr.2 hr.s hS).mp hres
    have hlog : HasElementaryIntegralIn
        (aeval t (GPoly.toPoly M qr.2) / aeval t (GPoly.toPoly M hr.s)) :=
      hasElementaryIntegralIn_of_residueTest (F := T.F m) t η 0
        (by rw [map_zero, zero_mul, add_zero]; exact T.deriv_ts_F m) 1 one_ne_zero
        (by rw [logDeriv_one, map_zero]) _ _ _ (PerfectField.separable_iff_squarefree.mpr hsq)
        hst hdeg hrs hT
    -- the polynomial part
    have hsolve : ∀ G W r, limIntP ηs m G W = some r → r.1.length = W.length ∧
        (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
          M.sem G := by
      intro G W r hr
      obtain ⟨h1, h2⟩ := T.limIntP_sound m (hnd.mono (Nat.le_succ m)) G W r.1 r.2 hr
      refine ⟨h1, Subtype.ext ?_⟩
      rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
      exact h2
    have hinit : implicitDeriv (C (M.sem (lift m (eta ηs m))))
        (X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M ((opsP ηs m).zero :: [])) =
        X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M (qr.1.drop (qr.1.length - 1 + 1)) +
          C (((qr.1.length - 1 : ℕ) + 1 : T.F m) * M.sem (opsP ηs m).zero *
            M.sem (lift m (eta ηs m))) * X ^ (qr.1.length - 1) := by
      rw [List.drop_eq_nil_of_le (by omega)]
      simp [M.sem_zero]
    have hpoly := polyDown_sound M (lift m (eta ηs m)) (eta ηs m) (fun w ↦ M.sem (lift m w))
      (limIntP ηs m) (constC (m + 1)) hsolve rfl (T.sem_constC m hm) T.deriv_ratCast qr.1
      (qr.1.length - 1) (opsP ηs m).zero [] Q Ys hinit hpd
    rw [T.sem_lift_eta] at hpoly
    have hqP : GPoly.toPoly M qr.1 = implicitDeriv (C η) (X * GPoly.toPoly M (Q :: Ys)) +
        C (M.sem ((opsP ηs m).add (qr.1.getD 0 (opsP ηs m).zero)
          ((opsP ηs m).neg ((opsP ηs m).mul Q (lift m (eta ηs m)))))) := by
      have h0 := toPoly_drop M qr.1 0
      rw [List.drop_zero] at h0
      rw [hpoly, M.sem_add, M.sem_neg, M.sem_mul, T.sem_lift_eta]
      conv_lhs => rw [h0]
      simp only [C_add, C_neg, C_mul, zero_add]
      ring
    have hq : HasElementaryIntegralIn (aeval t (GPoly.toPoly M qr.1)) := by
      rw [hqP, map_add, ← deriv_aeval_eq_implicitDeriv t (C η) hw, aeval_C]
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

/-! ### Completeness -/

lemma coe_logDeriv_F {m : ℕ} (y : T.F m) : ((logDeriv y : T.F m) : E) = logDeriv (y : E) := by
  unfold logDeriv
  rw [IntermediateField.coe_div, coe_deriv]

/-- A Liouville form at level `m`, up to an element of `Kc(x)`. -/
def LiouSol (m : ℕ) (h : T.Tr m) (A : Code (m + 1)) : Prop :=
  ∃ K0 ∈ T.F 0, LiouvilleIn (T.F m) ((((T.MP m h).sem A : T.F m) : E) - K0)

/-- **Completeness of `elemP`**: a Liouville form forces a positive answer. -/
theorem elemP_complete : ∀ (m : ℕ) (hnd : T.ND m) (A : Code (m + 1)),
    T.LiouSol m (T.tr_of_ND hnd) A → elemP ηs m A = true
  | 0, _, _, _ => rfl
  | m + 1, hnd, A, hsol => by
    classical
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
    set hm := T.tr_of_ND (hnd.mono (Nat.le_succ m)) with hhm
    set M := T.MP m hm with hM
    set M' := T.MP (m + 1) (T.tr_of_ND hnd) with hM'
    have htr : Transcendental (T.F m) (T.ts m) := T.tr_of_ND hnd m (Nat.lt_succ_self m)
    have hη : ∀ y : T.F m, y′ ≠ T.etaF m m := hnd m (Nat.lt_succ_self m)
    have hsem : ∀ q : Code (m + 2),
        M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
    obtain ⟨K0, hK0, ι, s, c, u, v, hdata, hv, heq⟩ := hsol
    simp only [elemP, Bool.or_eq_true, Bool.and_eq_true]
    by_cases hz : GPoly.isZero (opsP ηs m) A.2 = true
    · exact Or.inl hz
    right
    have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr hη A.1 A.2 hA2
    generalize GPoly.hermite (opsP ηs m) (wP ηs m) A.1 A.2 = hr at hval hsq ⊢
    have hdm := GPoly.divMod_spec M hr.b hr.s
    have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
    generalize GPoly.divMod (opsP ηs m) hr.b hr.s = qr at hdm hdeg ⊢
    set η := T.etaF m m with hηdef
    set t := T.ts m with ht
    have hw : t′ = aeval t (C η) := by rw [aeval_C]; exact T.ht m
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
    have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M (wP ηs m)) (GPoly.toPoly M hr.s))
        (GPoly.toPoly M hr.s) := by
      rw [T.toPoly_wP]
      letI : Differential (T.F m)[X] := polynomialOfDeriv (C η)
      exact isCoprime_deriv_of_squarefree hsq (fun p hp _ ↦ T.normal hη p hp)
    have hrs := GPoly.residuePoly_spec M (wP ηs m) qr.2 hr.s hS hcop
    rw [T.toPoly_wP] at hrs
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
        (GPoly.residuePoly (opsP ηs m) (wP ηs m) qr.2 hr.s)) (GPoly.toPoly M hr.s) := by
      refine residueTest_step_primitive (F := T.F m) t htr η (T.deriv_ts_F m) hconst s c' u
        (fun i hi ↦ ⟨(T.mem_F_succ).mp (hdata i hi).2.1, (hdata i hi).2.2⟩) hc'd (v - (g : E))
        hvg _ _ _ hsq ?_ hbv
      have : GPoly.toPoly M (GPoly.residuePoly (opsP ηs m) (wP ηs m) qr.2 hr.s) *
          (mapCoeffs (GPoly.toPoly M hr.s) + C η * derivative (GPoly.toPoly M hr.s)) -
          ((GPoly.toPoly M qr.1 - C K0') * GPoly.toPoly M hr.s + GPoly.toPoly M qr.2) =
          (GPoly.toPoly M (GPoly.residuePoly (opsP ηs m) (wP ηs m) qr.2 hr.s) *
            implicitDeriv (C η) (GPoly.toPoly M hr.s) - GPoly.toPoly M qr.2) -
          (GPoly.toPoly M qr.1 - C K0') * GPoly.toPoly M hr.s := by
        simp [implicitDeriv]
        ring
      rw [this]
      exact dvd_sub hrs (dvd_mul_left _ _)
    refine ⟨(GPoly.residueCheck_iff M (wP ηs m) qr.2 hr.s hS).mpr hT, ?_⟩
    -- the fraction field `F m (tₘ)` and the polynomial part of the Liouville form
    let _ := algebraAdjoinSimple (F := T.F m) t
    let _ : Differential (T.F m)[X] := polynomialOfDeriv (C η)
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
    have hcoeffD : ∀ k, (Pv.coeff k)′ + η * (Pv.coeff (k + 1) * (k + 1)) =
        (GPoly.toPoly M qr.1 - C K0' - C SL).coeff k := fun k ↦ by
      rw [← coeff_implicitDeriv_C, hPv]
    have hP : ∀ k, 1 ≤ k → (Pv.coeff k)′ + ((k : T.F m) + 1) * Pv.coeff (k + 1) *
        M.sem (lift m (eta ηs m)) = M.sem (qr.1.getD k (opsP ηs m).zero) := by
      intro k hk
      have := hcoeffD k
      simp only [coeff_sub, coeff_C, if_neg (show k ≠ 0 by omega), sub_zero,
        coeff_toPoly_getD] at this
      rw [T.sem_lift_eta]
      linear_combination this
    have hconstP : ∀ Q : (T.F m)[X], implicitDeriv (C η) Q = 0 → ∃ e : T.F m, Q = C e :=
      fun Q hQ ↦ const_of_implicitDeriv_eq_zero η hη hQ
    have hdegP : Pv.natDegree ≤ qr.1.length - 1 + 1 := by
      refine natDegree_le_succ_of_natDegree_deriv_le η hconstP ?_
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
    have hsolve : ∀ G W r, limIntP ηs m G W = some r → r.1.length = W.length ∧
        (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
          M.sem G := by
      intro G W r hr
      obtain ⟨h1, h2⟩ := T.limIntP_sound m (hnd.mono (Nat.le_succ m)) G W r.1 r.2 hr
      refine ⟨h1, Subtype.ext ?_⟩
      rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
      exact h2
    have hcomp : ∀ G W (y : T.F m) (c : List Kc), c.length = W.length →
        y′ + (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F m) c * M.sem (lift m w)) c
          W).sum = M.sem G → limIntP ηs m G W ≠ none := by
      intro G W y c hl hy
      refine T.limIntP_complete m (hnd.mono (Nat.le_succ m)) G W ⟨y, y.2, c, hl, ?_⟩
      have := congrArg Subtype.val hy
      rw [IntermediateField.coe_add, T.coe_zipWithK_sum] at this
      exact this
    obtain ⟨Q', Ys', hpd, κ, hκ⟩ := polyDown_complete M (lift m (eta ηs m)) (eta ηs m)
      (fun w ↦ M.sem (lift m w)) (limIntP ηs m) (constC (m + 1)) hsolve hcomp rfl
      (by rw [T.sem_lift_eta]; exact hη) T.const_F T.deriv_algebraMap_Kc T.deriv_ratCast qr.1 Pv
      hP (qr.1.length - 1) (opsP ηs m).zero [] ⟨-κ₀, by rw [M.sem_zero, hκ₀, map_neg]; ring⟩
    rw [hpd]
    simp only
    -- the `t⁰` coefficient has a Liouville form over `F m`, up to `Kc(x)`
    refine elemP_complete m (hnd.mono (Nat.le_succ m)) _ ⟨K0 - algebraMap Kc E κ * (η : E), ?_,
      ι, s, c, fun i ↦ (e i : E), (Pv.coeff 0 : E), fun i hi ↦ ⟨(hdata i hi).1, (e i).2,
        fun h0 ↦ he i hi (Subtype.ext h0)⟩, (Pv.coeff 0).2, ?_⟩
    · exact sub_mem hK0 (mul_mem ((T.F 0).algebraMap_mem κ) (T.evx_mem _))
    · have h0 := hcoeffD 0
      rw [coeff_sub, coeff_sub, coeff_C_zero, coeff_C_zero, coeff_toPoly_getD] at h0
      have hF : M.sem ((opsP ηs m).add (qr.1.getD 0 (opsP ηs m).zero)
          ((opsP ηs m).neg ((opsP ηs m).mul Q' (lift m (eta ηs m))))) -
          (K0' - algebraMap Kc (T.F m) κ * η) = SL + (Pv.coeff 0)′ := by
        rw [M.sem_add, M.sem_neg, M.sem_mul, hκ, T.sem_lift_eta]
        push_cast at h0
        linear_combination -h0
      have hsumE : ((SL : T.F m) : E) = ∑ i ∈ s, c i * logDeriv ((e i : T.F m) : E) := by
        rw [hSL, AddSubmonoidClass.coe_finset_sum]
        exact Finset.sum_congr rfl fun i hi ↦ by
          rw [IntermediateField.coe_mul, hc'E i hi, T.coe_logDeriv_F]
      calc _ = (((M.sem ((opsP ηs m).add (qr.1.getD 0 (opsP ηs m).zero)
            ((opsP ηs m).neg ((opsP ηs m).mul Q' (lift m (eta ηs m))))) -
            (K0' - algebraMap Kc (T.F m) κ * η) : T.F m)) : E) := rfl
        _ = ((SL + (Pv.coeff 0)′ : T.F m) : E) := congrArg Subtype.val hF
        _ = _ := by rw [IntermediateField.coe_add, hsumE, coe_deriv]

end Tower.PrimN.PrimTower
