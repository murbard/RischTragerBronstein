import RischTragerBronstein.Computable.NestPConsys
import RischTragerBronstein.Computable.MixNBasics
import RischTragerBronstein.Liouville.ProperFractionSum

/-!
# Towers with nested primitives: basic facts

Ported from `MixNBasics` / `MixNComplete2`: rational and `Kc` constants, the constants of every
level, the rational decomposition at the base, no new constants and normality of every prime at a
primitive level, and Hermite reduction as an identity of values.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestP

open Tower.PrimN

namespace NestTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : (m : ℕ) → Code (m + 1)}
variable (T : NestTower Kc E ηs)

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
    rw [oneC_succQ ηs m]
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
  change T.model0.sem ((opsQ ηs 0).add _ _) = _
  refine (T.model0.sem_add _ _).trans ?_
  rw [T.model0_sem_eq, T.model0_sem_eq]
  simp [CPoly.toPoly, phi0]

/-- No new constants at level `m + 1`: `P(t)′ = 0` forces `P` constant. -/
lemma const_poly (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (P : (T.F m)[X])
    (hP : implicitDeriv (T.wPoly m) P = 0) : ∃ e : T.F m, P = C e := by
  set t := T.ts m with htd
  have hinjt : Function.Injective (aeval (R := T.F m) t) := transcendental_iff_injective.mp htr
  have hder : ∀ Q : (T.F m)[X], (aeval t Q)′ = aeval t (implicitDeriv (T.wPoly m) Q) :=
    deriv_aeval_eq_implicitDeriv t (T.wPoly m) (T.deriv_ts_aeval m)
  have hz : (aeval t P)′ = 0 := by rw [hder, hP, map_zero]
  obtain ⟨κ, hκ⟩ := T.hCall _ hz
  refine ⟨algebraMap Kc (T.F m) κ, hinjt ?_⟩
  rw [aeval_C]
  change aeval t P = algebraMap Kc E κ
  rw [hκ]

/-- Every irreducible polynomial over `F m` is normal for `t′ = ηₘ`. -/
lemma normal (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (p : (T.F m)[X])
    (hp : Irreducible p) : ¬p ∣ implicitDeriv (T.wPoly m) p := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  exact not_dvd_deriv_of_irreducible_primitive (T.valN m (ηs m)) (fun _ ↦ rfl)
    (fun P hP ↦ T.const_poly m htr P hP) hp

/-- **Hermite reduction at level `m + 1`**, as an identity of values. -/
lemma hermite_value (m : ℕ) (hm : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    (A D : GPoly (Code (m + 1))) (hD : GPoly.toPoly (T.MP m hm) D ≠ 0) :
    T.phi m (GPoly.toPoly (T.MP m hm) A) / T.phi m (GPoly.toPoly (T.MP m hm) D) =
      (T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsQ ηs m) [ηs m] A D).gn) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsQ ηs m) [ηs m] A D).gd))′ +
      T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsQ ηs m) [ηs m] A D).b) /
        T.phi m (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsQ ηs m) [ηs m] A D).s) ∧
    Squarefree (GPoly.toPoly (T.MP m hm) (GPoly.hermite (opsQ ηs m) [ηs m] A D).s) := by
  set M := T.MP m hm
  have hnormal' : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M [ηs m]) p := fun p hp _ ↦ by
    rw [T.toPoly_wK]
    exact T.normal m htr p hp
  have hc := GPoly.hermiteCheck_hermite M [ηs m] A D hnormal' hD
  obtain ⟨hD0, hgd0, hs0, hid, hsq⟩ := (GPoly.hermiteCheck_iff M _ _ _ _).mp hc
  rw [T.toPoly_wK] at hid
  refine ⟨?_, GPoly.squarefreeCheck_sound M hsq⟩
  have hinj := T.phi_injective htr
  have h1 : T.phi m (GPoly.toPoly M D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have h2 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsQ ηs m) [ηs m] A D).gd) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hgd0
  have h3 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsQ ηs m) [ηs m] A D).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hs0
  have hidL := congrArg (T.phi m) hid
  simp only [map_mul, map_add, map_sub] at hidL
  rw [Derivation.leibniz_div, T.deriv_phi, T.deriv_phi]
  simp only [smul_eq_mul]
  field_simp
  linear_combination hidL

end NestTower

end Tower.NestP
