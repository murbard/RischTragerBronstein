import RischTragerBronstein.Computable.NestMConsys
import RischTragerBronstein.Computable.NestPBasics
import RischTragerBronstein.Computable.MixNBasics

/-!
# Mixed towers with nested data: basic facts

Ported from `NestPBasics` and `MixNBasics`: rational and `Kc` constants, the constants of every
level, the rational decomposition at the base, no new constants (`const_poly`), normality of the
primes (every prime at a primitive level, every prime other than `t` at an exponential level) and
Hermite reduction as an identity of values.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

lemma coe_ratCast {m : ℕ} (c : ℚ) : ((c : T.F m) : E) = (c : E) := by simp

include T in
lemma deriv_ratCast_E (c : ℚ) : (c : E)′ = 0 := by
  rw [← map_ratCast (algebraMap Kc E) c, deriv_algebraMap, T.hC, map_zero]

lemma deriv_ratCast {m : ℕ} (c : ℚ) : (c : T.F m)′ = 0 :=
  Subtype.ext (by rw [coe_deriv, coe_ratCast, T.deriv_ratCast_E]; rfl)

lemma deriv_algebraMap_Kc {m : ℕ} (κ : Kc) : (algebraMap Kc (T.F m) κ)′ = 0 :=
  Subtype.ext (by
    rw [coe_deriv]
    change (algebraMap Kc E κ)′ = 0
    rw [deriv_algebraMap, T.hC, map_zero])

lemma const_F {m : ℕ} (y : T.F m) (hy : y′ = 0) : ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := by
  obtain ⟨κ, hκ⟩ := T.hCall (y : E) (by rw [← coe_deriv, hy]; rfl)
  exact ⟨κ, Subtype.ext hκ.symm⟩

lemma sem_cstN : ∀ (m : ℕ) (h : T.Tr m) (c : ℚ), (T.MP m h).sem (cstN m c) = (c : T.F m)
  | 0, h, c => by
    apply Subtype.ext
    change ((T.phi0 _ / T.phi0 _ : T.F 0) : E) = _
    rw [IntermediateField.coe_div, coe_phi0, coe_phi0, toPoly_ofHom', toPoly_ofHom']
    simp [cstN, constC, oneC, CPoly.toPoly]
  | m + 1, h, c => by
    rw [sem_MP_succ]
    change T.phi m (GPoly.toPoly _ [cstN m c]) / T.phi m (GPoly.toPoly _ [oneC (m + 1)]) = _
    rw [oneC_succM ks m]
    simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one,
      sem_cstN m, map_one, div_one]
    rw [phi, coe_eval₂RingHom, eval₂_C]
    exact map_ratCast _ c

lemma phi0_map_injective :
    Function.Injective (T.phi0.comp (mapRingHom (algebraMap ℚ Kc))) :=
  T.phi0_injective.comp (Polynomial.map_injective _ (algebraMap ℚ Kc).injective)

/-- **The rational decomposition** `q = L′ + r / s` at the base. -/
lemma ratInt_spec (q : GFrac ℚ) :
    T.model0.sem q = (T.model0.sem (ratPart (ratInt q)))′ +
      T.phi0 ((CPoly.toPoly (ratInt q).r).map (algebraMap ℚ Kc)) /
        T.phi0 ((CPoly.toPoly (ratInt q).s).map (algebraMap ℚ Kc)) ∧
    Squarefree ((CPoly.toPoly (ratInt q).s).map (algebraMap ℚ Kc)) ∧
    ((CPoly.toPoly (ratInt q).r).map (algebraMap ℚ Kc)).degree <
      ((CPoly.toPoly (ratInt q).s).map (algebraMap ℚ Kc)).degree := by
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  obtain ⟨h1, h2, h3⟩ := CPoly.rationalCheck_sound_map (K := T.F 0) (algebraMap ℚ Kc) hD _ _
    (ratInt q) (CPoly.rationalCheck_integrateRational _ _ (CPoly.normCoeff_den_ne_zero q))
  refine ⟨?_, h2, h3⟩
  have hn := CPoly.normCoeff_spec _ T.phi0_map_injective q
  simp only [RingHom.comp_apply, coe_mapRingHom] at hn
  rw [T.model0_sem_eq, ← hn]
  simp only [phi0] at h1 ⊢
  rw [h1]
  congr 2
  symm
  change T.model0.sem ((opsM ks 0).add _ _) = _
  refine (T.model0.sem_add _ _).trans ?_
  rw [T.model0_sem_eq, T.model0_sem_eq]
  simp [CPoly.toPoly, phi0]

/-- No new constants at level `m + 1`: `(P(t) / t ^ n)′ = 0` forces `P = e X ^ n`. -/
lemma const_poly (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (P : (T.F m)[X]) (n : ℕ)
    (hP : implicitDeriv (T.wPoly m) P * X ^ n = P * implicitDeriv (T.wPoly m) (X ^ n)) :
    ∃ e : T.F m, P = C e * X ^ n := by
  set t := T.ts m with htd
  have hinjt : Function.Injective (aeval (R := T.F m) t) := transcendental_iff_injective.mp htr
  have ht0 : t ≠ 0 := fun h0 ↦ by
    have : aeval t (X : (T.F m)[X]) = aeval t (0 : (T.F m)[X]) := by rw [aeval_X, map_zero, h0]
    exact X_ne_zero (hinjt this)
  have hder : ∀ Q : (T.F m)[X], (aeval t Q)′ = aeval t (implicitDeriv (T.wPoly m) Q) :=
    deriv_aeval_eq_implicitDeriv t (T.wPoly m) (T.deriv_ts_aeval m)
  have htn : (t ^ n : E) ≠ 0 := pow_ne_zero n ht0
  have hz : (aeval t P / t ^ n)′ = 0 := by
    rw [Derivation.leibniz_div, show (t ^ n : E) = aeval (R := T.F m) t (X ^ n) by simp, hder, hder]
    have := congrArg (aeval t) hP
    simp only [map_mul, map_pow, aeval_X] at this
    simp only [map_pow, aeval_X, smul_eq_mul]
    rw [mul_comm (t ^ n) _, this]
    simp
  obtain ⟨κ, hκ⟩ := T.hCall _ hz
  refine ⟨algebraMap Kc (T.F m) κ, hinjt ?_⟩
  rw [map_mul, map_pow, aeval_X, aeval_C]
  change aeval t P = algebraMap Kc E κ * t ^ n
  rw [hκ]
  field_simp

/-- At a primitive level every irreducible polynomial is normal. -/
lemma normal_prim (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) {η : Code (m + 1)}
    (hk : ks m = .prim η) (p : (T.F m)[X]) (hp : Irreducible p) :
    ¬p ∣ implicitDeriv (T.wPoly m) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (C (T.valN m η))
  have hw : T.wPoly m = C (T.valN m η) := T.wPoly_prim hk
  rw [hw]
  exact not_dvd_deriv_of_irreducible_primitive (T.valN m η) (fun _ ↦ rfl)
    (fun P hP ↦ by
      obtain ⟨e, he⟩ := T.const_poly m htr P 0 (by
        rw [hw]; change P′ * X ^ 0 = P * implicitDeriv (C (T.valN m η)) (X ^ 0)
        simp [hP])
      exact ⟨e, by simpa using he⟩) hp

/-- At an exponential level every irreducible polynomial other than `X` is normal. -/
lemma normal_exp (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) {a : Code (m + 1)}
    (hk : ks m = .exp a) (p : (T.F m)[X]) (hp : Irreducible p) (hX : ¬X ∣ p) :
    ¬p ∣ implicitDeriv (T.wPoly m) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  have hw : T.wPoly m = C (T.valN m a)′ * X := T.wPoly_exp hk
  intro hsp
  refine hX (dvd_X_of_irreducible_special (T.valN m a)′
    (fun P ↦ by change implicitDeriv (T.wPoly m) P = _; rw [hw]) (fun P n hP ↦ T.const_poly m htr P n hP)
    hp hsp)

/-- **Hermite reduction at level `m + 1`**, as an identity of values, when the primes of the
denominator are normal. -/
lemma hermite_value (m : ℕ) (hm : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    (A D : GPoly (Code (m + 1))) (hD : GPoly.toPoly (T.MP m hm) D ≠ 0)
    (hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m hm) D →
      ¬p ∣ implicitDeriv (T.wPoly m) p) :
    T.phi m (GPoly.toPoly (T.MP m hm) A) / T.phi m (GPoly.toPoly (T.MP m hm) D) =
      (T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) A D).gn) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) A D).gd))′ +
      T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) A D).b) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) A D).s) ∧
    Squarefree (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) A D).s) := by
  set M := T.MP m hm
  have hnormal' : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M (wK (opsM ks m) (ks m))) p := fun p hp hpD ↦ by
    rw [T.toPoly_wK]
    exact hnormal p hp hpD
  have hc := GPoly.hermiteCheck_hermite M (wK (opsM ks m) (ks m)) A D hnormal' hD
  obtain ⟨hD0, hgd0, hs0, hid, hsq⟩ := (GPoly.hermiteCheck_iff M _ _ _ _).mp hc
  rw [T.toPoly_wK] at hid
  refine ⟨?_, GPoly.squarefreeCheck_sound M hsq⟩
  have hinj := T.phi_injective htr
  have h1 : T.phi m (GPoly.toPoly M D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have h2 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) A D).gd) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hgd0
  have h3 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) A D).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hs0
  have hidL := congrArg (T.phi m) hid
  simp only [map_mul, map_add, map_sub] at hidL
  rw [Derivation.leibniz_div, T.deriv_phi, T.deriv_phi]
  simp only [smul_eq_mul]
  field_simp
  linear_combination hidL

end NestMTower

end Tower.NestM
