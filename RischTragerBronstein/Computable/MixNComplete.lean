import RischTragerBronstein.Computable.MixNSound
import RischTragerBronstein.Computable.RDEPrimTop
import RischTragerBronstein.Computable.RDEExp
import RischTragerBronstein.RDE.ExponentialDenominator
import RischTragerBronstein.RDE.PrimitiveDenominator
import RischTragerBronstein.Liouville.MonicPrimes

/-!
# Mixed towers: completeness of the Risch equation solver

`rdeM_complete`: if `y′ + f y = A` has a solution in `F m` and `f` is not a `ℚ`-combination of
the exponents below `m`, then `rdeM ks m f A` does not fail.

The solution is `Y / D` (`rde_denom`: no new poles; at an exponential level the pole at `t` is
controlled by `rde_regularAt_X`, since `f - r bₘ` has no homogeneous solution), and the top-degree
recursion finds `Y` coefficient by coefficient (`rdeAux_complete`), each coefficient being the
unique solution of a Risch equation one level down.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.MixN

open Tower.PrimN

namespace MixTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : List Kind} (T : MixTower Kc E ks)

/-- **No new poles**: a solution of `y′ + f y = A₁ / D` in `F (m + 1)` is `Y / D`. -/
lemma rde_denom (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (hnh : T.NoHom m)
    (f : Code 1) (hder : T.Adm f) (hf : T.NotSpan (expsBelow ks (m + 1)) f)
    (hbd : ∀ b, kind ks m = .exp b → T.Adm b) (A₁ D : (T.F m)[X]) (hD0 : D ≠ 0)
    (y : E) (hy : y ∈ T.F (m + 1))
    (h : y′ + (T.ratF m f : E) * y = aeval (T.ts m) A₁ / aeval (T.ts m) D) :
    ∃ Y : (T.F m)[X], y * aeval (T.ts m) D = aeval (T.ts m) Y ∧
      D * implicitDeriv (T.wPoly m) Y + (C (T.ratF m f) * D - implicitDeriv (T.wPoly m) D) * Y =
        A₁ * D := by
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) (T.ts m)
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮T.ts m⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple (T.ts m) _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮T.ts m⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮T.ts m⟯ :=
    differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ P : (T.F m)⟮T.ts m⟯) : E) =
      aeval (T.ts m) P := algebraMap_adjoinSimple _
  have hinj : Function.Injective (algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯) :=
    IsFractionRing.injective _ _
  set φ := algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ with hφ
  set yK : (T.F m)⟮T.ts m⟯ := ⟨y, (T.mem_F_succ).mp hy⟩ with hyK
  have hK : yK′ + φ (C (T.ratF m f)) * yK = φ A₁ / φ D := Subtype.ext (by
    rw [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_div, hcoe,
      hcoe, hcoe, aeval_C]
    exact h)
  have hreg : ∀ (p : (T.F m)[X]) (hm : p.Monic) (hp : Irreducible p),
      yK * φ D ∈ regularAt (T.F m)⟮T.ts m⟯ p hp.prime := by
    intro p hm hp
    have hnorm : ¬X ∣ p → ¬p ∣ p′ := fun hX ↦ by
      change ¬p ∣ implicitDeriv (T.wPoly m) p
      cases hk : kind ks m with
      | prim η => exact T.normal_prim m htr hk p hp
      | exp b => exact T.normal_exp m htr hk p hp hX
    by_cases hX : X ∣ p
    · -- `p = X`, necessarily at an exponential level
      have hpX : p = X := eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hX) hX)
      subst hpX
      cases hk : kind ks m with
      | prim η =>
        exact rde_regularAt_of_normal X hp (by
          change ¬X ∣ implicitDeriv (T.wPoly m) X
          exact T.normal_prim m htr hk X hp) _ (algebraMap_mem_regularAt _ _) A₁ D hD0 yK hK
      | exp b =>
        have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ratF m b) * X) P := fun P ↦ by
          change implicitDeriv (T.wPoly m) P = _
          simp only [wPoly, hk]
        obtain ⟨j, D₁, hD₁, rfl⟩ := exists_pow_mul_not_dvd (prime_X (R := T.F m)) hD0
        have hg : ∀ r : ℕ, 0 < r → ∀ e : T.F m, e ≠ 0 →
            e′ + (T.ratF m f - r * T.ratF m b) * e ≠ 0 := fun r _ e he he' ↦ by
          rw [expsBelow_exp hk] at hf
          refine he (hnh _ (hder.shift (hbd b hk) (-(r : ℤ))) (hf.shift (-(r : ℤ))) e ?_)
          rw [T.ratF_shift]
          push_cast
          linear_combination he'
        have hX' := rde_regularAt_X (K := (T.F m)⟮T.ts m⟯) (T.ratF m b) hD (T.ratF m f) hg A₁ D₁
          j hD₁ yK (by rw [hK, map_mul, map_pow])
        rw [map_mul, map_pow, ← mul_assoc]
        exact mul_mem hX' (algebraMap_mem_regularAt _ _)
    · exact rde_regularAt_of_normal p hp (hnorm hX) _ (algebraMap_mem_regularAt _ _) A₁ D hD0 yK hK
  obtain ⟨Y, hY⟩ := exists_polynomial_of_regularAt (yK * φ D) hreg
  refine ⟨Y, ?_, ?_⟩
  · have := congrArg Subtype.val hY
    rw [IntermediateField.coe_mul, hcoe, hcoe] at this
    exact this
  · have := rde_poly_of_rde (K := (T.F m)⟮T.ts m⟯) (C (T.ratF m f)) A₁ D Y hD0 yK hY hK
    exact this

lemma rdeAux_isSome_of_zero {α : Type} (O : COps α) (w : GPoly α) (kd : Kind) (f : Code 1)
    (rde : Code 1 → α → Option α) (D P₀ : GPoly α) (fuel : ℕ) (Ap acc : GPoly α)
    (hz : GPoly.isZero O Ap = true) : (rdeAux O w kd f rde D P₀ fuel Ap acc).isSome = true := by
  cases fuel <;> simp [rdeAux, hz]

/-- **Completeness of the top-degree recursion.** -/
theorem rdeAux_complete (m : ℕ) (hm : T.Tr m) (hnh : T.NoHom m)
    (ihc : ∀ (f' : Code 1), T.Adm f' → T.NotSpan (expsBelow ks m) f' →
      ∀ (A' : Code (m + 1)) (y : T.F m),
      y′ + T.ratF m f' * y = (T.MP m hm).sem A' → rdeM ks m f' A' ≠ none)
    (f : Code 1) (hder : T.Adm f) (hf : T.NotSpan (expsBelow ks (m + 1)) f)
    (hbd : ∀ b, kind ks m = .exp b → T.Adm b)
    (D P₀ : GPoly (Code (m + 1))) (hD0 : GPoly.toPoly (T.MP m hm) D ≠ 0)
    (hP₀ : GPoly.toPoly (T.MP m hm) P₀ = C (T.ratF m f) * GPoly.toPoly (T.MP m hm) D -
      implicitDeriv (T.wPoly m) (GPoly.toPoly (T.MP m hm) D)) :
    ∀ (fuel : ℕ) (Ap acc : GPoly (Code (m + 1))) (Y : (T.F m)[X]),
    GPoly.toPoly (T.MP m hm) D * implicitDeriv (T.wPoly m) Y + GPoly.toPoly (T.MP m hm) P₀ * Y =
      GPoly.toPoly (T.MP m hm) Ap → Y.natDegree < fuel →
    (rdeAux (opsM ks m) (wK ks m) (kind ks m) f (rdeM ks m) D P₀ fuel Ap acc).isSome = true := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro Ap acc Y hY hfuel
    simp only [rdeAux]
    by_cases hz : GPoly.isZero (opsM ks m) Ap = true
    · rw [if_pos hz]; rfl
    rw [if_neg hz]
    have hAp0 : GPoly.toPoly (T.MP m hm) Ap ≠ 0 := fun h ↦ hz ((GPoly.isZero_iff (T.MP m hm) Ap).mpr h)
    have hY0 : Y ≠ 0 := fun h ↦ hAp0 (by rw [← hY, h]; simp)
    rw [hP₀] at hY
    change GPoly.toPoly (T.MP m hm) D * Y′ + (C (T.ratF m f) * GPoly.toPoly (T.MP m hm) D -
      (GPoly.toPoly (T.MP m hm) D)′) * Y = GPoly.toPoly (T.MP m hm) Ap at hY
    have hAne : GPoly.trim (opsM ks m) Ap ≠ [] := fun h ↦ hAp0 ((GPoly.trim_eq_nil_iff (T.MP m hm) Ap).mp h)
    have hDne : GPoly.trim (opsM ks m) D ≠ [] := fun h ↦ hD0 ((GPoly.trim_eq_nil_iff (T.MP m hm) D).mp h)
    obtain ⟨hdA, hlA, -⟩ := GPoly.natDegree_toPoly_of_trim_ne_nil (T.MP m hm) hAne
    obtain ⟨hd₁, hlD, -⟩ := GPoly.natDegree_toPoly_of_trim_ne_nil (T.MP m hm) hDne
    -- the top coefficient, for either kind
    obtain ⟨fk, hfkd, hfk, hdeg, hcoeff, hmatch⟩ : ∃ fk : Code 1, T.Adm fk ∧
        T.NotSpan (expsBelow ks m) fk ∧
        (GPoly.toPoly (T.MP m hm) D * Y′ + (C (T.ratF m f) * GPoly.toPoly (T.MP m hm) D - (GPoly.toPoly (T.MP m hm) D)′) *
          Y).natDegree = (GPoly.toPoly (T.MP m hm) D).natDegree + Y.natDegree ∧
        (GPoly.toPoly (T.MP m hm) D * Y′ + (C (T.ratF m f) * GPoly.toPoly (T.MP m hm) D - (GPoly.toPoly (T.MP m hm) D)′) *
          Y).coeff ((GPoly.toPoly (T.MP m hm) D).natDegree + Y.natDegree) =
          (GPoly.toPoly (T.MP m hm) D).leadingCoeff ^ 2 *
            ((Y.leadingCoeff / (GPoly.toPoly (T.MP m hm) D).leadingCoeff)′ +
              T.ratF m fk * (Y.leadingCoeff / (GPoly.toPoly (T.MP m hm) D).leadingCoeff)) ∧
        fkOf (kind ks m) f ((GPoly.trim (opsM ks m) Ap).length - 1)
          ((GPoly.trim (opsM ks m) D).length - 1) = fk := by
      cases hk : kind ks m with
      | prim η =>
        have hD₂ : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ratF m η)) P := fun P ↦ by
          change implicitDeriv (T.wPoly m) P = _
          simp only [wPoly, hk]
        rw [expsBelow_prim hk] at hf
        have hgnl : ∀ e : T.F m, e ≠ 0 → e′ + T.ratF m f * e ≠ 0 := fun e he he' ↦
          he (hnh f hder hf e he')
        obtain ⟨h1, h2, -⟩ := rde_poly_top (T.ratF m η) (T.ratF m f) hD₂ hgnl _ Y hD0 hY0
        exact ⟨f, hder, hf, h1, h2, by simp only [fkOf]⟩
      | exp b =>
        have hD₂ : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ratF m b) * X) P := fun P ↦ by
          change implicitDeriv (T.wPoly m) P = _
          simp only [wPoly, hk]
        rw [expsBelow_exp hk] at hf
        set c : ℤ := (Y.natDegree : ℤ) - (GPoly.toPoly (T.MP m hm) D).natDegree with hc
        have hval : T.ratF m (shiftF f b c) =
            T.ratF m f + ((Y.natDegree : T.F m) - (GPoly.toPoly (T.MP m hm) D).natDegree) * T.ratF m b := by
          rw [T.ratF_shift, hc]
          push_cast
          ring
        have hgnl : ∀ e : T.F m, e ≠ 0 → e′ + (T.ratF m f + ((Y.natDegree : T.F m) -
            (GPoly.toPoly (T.MP m hm) D).natDegree) * T.ratF m b) * e ≠ 0 := fun e he he' ↦
          he (hnh _ (hder.shift (hbd b hk) c) (hf.shift c) e (by rw [hval]; exact he'))
        obtain ⟨h1, h2, -⟩ := rde_poly_top_exp (T.ratF m b) (T.ratF m f) hD₂ _ Y hD0 hY0 hgnl
        refine ⟨shiftF f b c, hder.shift (hbd b hk) c, hf.shift c, h1, by rw [h2, hval], ?_⟩
        have e1 : (GPoly.trim (opsM ks m) Ap).length - 1 =
            (GPoly.toPoly (T.MP m hm) D).natDegree + Y.natDegree := by rw [← hdA, ← hY, h1]
        have e2 : (GPoly.trim (opsM ks m) D).length - 1 = (GPoly.toPoly (T.MP m hm) D).natDegree :=
          hd₁.symm
        simp only [fkOf]
        rw [e1, e2, hc]
        congr 1
        push_cast
        ring
    rw [hY] at hdeg hcoeff
    have hlt : ¬((GPoly.trim (opsM ks m) Ap).length - 1 < (GPoly.trim (opsM ks m) D).length - 1) := by
      rw [← hdA, ← hd₁, hdeg]; omega
    rw [if_neg hlt, hmatch]
    -- the lower Risch equation for the top coefficient
    obtain ⟨L, hL⟩ : ∃ L, L = (T.MP m hm).sem (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) D)) :=
      ⟨_, rfl⟩
    obtain ⟨top, htop⟩ : ∃ t,
        t = (T.MP m hm).sem (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) Ap)) := ⟨_, rfl⟩
    have hLlc : (GPoly.toPoly (T.MP m hm) D).leadingCoeff = L := by
      rw [leadingCoeff, hd₁, hlD, hL]
    have hL0 : L ≠ 0 := by rw [← hLlc]; exact leadingCoeff_ne_zero.mpr hD0
    have htoplc : top = L ^ 2 * ((Y.leadingCoeff / L)′ + T.ratF m fk * (Y.leadingCoeff / L)) := by
      rw [htop, ← hlA, ← hLlc, ← hcoeff, ← hdeg, hdA]
    obtain ⟨z, hz'⟩ : ∃ z, z = Y.leadingCoeff / L := ⟨_, rfl⟩
    rw [← hz'] at htoplc
    have hzsol : z′ + T.ratF m fk * z =
        (T.MP m hm).sem ((opsM ks m).mul (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) Ap)) ((opsM ks m).inv ((opsM ks m).mul (GPoly.lead (opsM ks m)
          (GPoly.trim (opsM ks m) D)) (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) D))))) := by
      rw [(T.MP m hm).sem_mul, (T.MP m hm).sem_inv, (T.MP m hm).sem_mul, ← hL, ← htop, htoplc]
      field_simp
    obtain ⟨z', hz''⟩ := Option.ne_none_iff_exists'.mp (ihc fk hfkd hfk _ z hzsol)
    rw [hz'']
    simp only
    have hzz : (T.MP m hm).sem z' = z := by
      have hs := T.rdeM_sound m hm fk _ z' hz''
      have hdiff : ((T.MP m hm).sem z' - z)′ + T.ratF m fk * ((T.MP m hm).sem z' - z) = 0 := by
        rw [map_sub]; linear_combination hs - hzsol
      exact sub_eq_zero.mp (hnh fk hfkd hfk _ hdiff)
    have hyd : (T.MP m hm).sem ((opsM ks m).mul (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) D)) z') = Y.leadingCoeff := by
      rw [(T.MP m hm).sem_mul, ← hL, hzz, hz']
      field_simp
    -- recurse with `Y - lc Y * X ^ d`
    have hdY : (GPoly.trim (opsM ks m) Ap).length - 1 - ((GPoly.trim (opsM ks m) D).length - 1) = Y.natDegree := by
      rw [← hdA, ← hd₁, hdeg]; omega
    rw [hdY]
    have hYd : GPoly.toPoly (T.MP m hm) (GPoly.monomial (opsM ks m) Y.natDegree
        ((opsM ks m).mul (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) D)) z')) = C Y.leadingCoeff * X ^ Y.natDegree := by
      rw [GPoly.toPoly_monomial, hyd]
    have hY'sol : GPoly.toPoly (T.MP m hm) D * (Y.eraseLead)′ +
        GPoly.toPoly (T.MP m hm) P₀ * Y.eraseLead =
        GPoly.toPoly (T.MP m hm) (GPoly.sub (opsM ks m) Ap (GPoly.add (opsM ks m)
          (GPoly.mul (opsM ks m) D (GPoly.derivT (opsM ks m) (wK ks m)
            (GPoly.monomial (opsM ks m) Y.natDegree ((opsM ks m).mul (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) D)) z'))))
          (GPoly.mul (opsM ks m) P₀ (GPoly.monomial (opsM ks m) Y.natDegree
            ((opsM ks m).mul (GPoly.lead (opsM ks m) (GPoly.trim (opsM ks m) D)) z'))))) := by
      have hprime : ∀ P : (T.F m)[X], P′ = implicitDeriv (T.wPoly m) P := fun _ ↦ rfl
      simp only [GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_derivT]
      rw [T.toPoly_wK, hYd, ← hY, hP₀, ← Y.self_sub_C_mul_X_pow]
      simp only [hprime, map_sub]
      ring
    rcases Y.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt' | hz0
    · exact ih _ _ Y.eraseLead hY'sol (by omega)
    · rw [hz0] at hY'sol
      simp only [map_zero, mul_zero, add_zero] at hY'sol
      apply rdeAux_isSome_of_zero
      exact (GPoly.isZero_iff (T.MP m hm) _).mpr hY'sol.symm

/-- The degree of `D Y′ + (f D - D′) Y` (no cancellation of the top coefficient). -/
lemma rde_natDegree (m : ℕ) (hnh : T.NoHom m) (f : Code 1) (hder : T.Adm f)
    (hf : T.NotSpan (expsBelow ks (m + 1)) f) (hbd : ∀ b, kind ks m = .exp b → T.Adm b)
    (D Y : (T.F m)[X]) (hD0 : D ≠ 0) (hY0 : Y ≠ 0) :
    (D * implicitDeriv (T.wPoly m) Y + (C (T.ratF m f) * D - implicitDeriv (T.wPoly m) D) *
      Y).natDegree = D.natDegree + Y.natDegree := by
  letI : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  cases hk : kind ks m with
  | prim η =>
    have hD₂ : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ratF m η)) P := fun P ↦ by
      change implicitDeriv (T.wPoly m) P = _
      simp only [wPoly, hk]
    rw [expsBelow_prim hk] at hf
    exact (rde_poly_top (T.ratF m η) (T.ratF m f) hD₂ (fun e he he' ↦ he (hnh f hder hf e he'))
      D Y hD0 hY0).1
  | exp b =>
    have hD₂ : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ratF m b) * X) P := fun P ↦ by
      change implicitDeriv (T.wPoly m) P = _
      simp only [wPoly, hk]
    rw [expsBelow_exp hk] at hf
    set c : ℤ := (Y.natDegree : ℤ) - D.natDegree with hc
    refine (rde_poly_top_exp (T.ratF m b) (T.ratF m f) hD₂ D Y hD0 hY0 fun e he he' ↦
      he (hnh _ (hder.shift (hbd b hk) c) (hf.shift c) e ?_)).1
    rw [T.ratF_shift, hc]
    push_cast
    linear_combination he'

/-- **Completeness of `rdeM`.** -/
theorem rdeM_complete : ∀ (m : ℕ) (hnd : T.ND m) (f : Code 1), T.Adm f →
    T.NotSpan (expsBelow ks m) f → ∀ (A : Code (m + 1)) (y : T.F m),
      y′ + T.ratF m f * y = (T.MP m (T.tr_noHom_of_ND m hnd).1).sem A → rdeM ks m f A ≠ none
  | 0, hnd, f, hder, hf, A, y, hy => by
    letI : Differential Kc[X] := polynomialOfDeriv 1
    haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
    have hDK : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
    intro hnone
    set g := CPoly.normCoeff (R := ℚ) (f : GFrac ℚ) with hg
    have hn := CPoly.normCoeff_spec _ T.phi0_map_injective (A : GFrac ℚ)
    have hnf := CPoly.normCoeff_spec _ T.phi0_map_injective (f : GFrac ℚ)
    simp only [RingHom.comp_apply, coe_mapRingHom] at hn hnf
    have hfv : T.ratF 0 f = algebraMap Kc[X] (T.F 0) ((CPoly.toPoly g.1).map (algebraMap ℚ Kc)) /
        algebraMap Kc[X] (T.F 0) ((CPoly.toPoly g.2).map (algebraMap ℚ Kc)) := by
      rw [T.ratF_zero_eq, show T.model0.sem f = _ from T.model0_sem_eq f, ← hnf]
      rfl
    have hGd0 : CPoly.toPoly g.2 ≠ 0 := CPoly.normCoeff_den_ne_zero (R := ℚ) _
    have hGn0 : CPoly.toPoly g.1 ≠ 0 := fun h0 ↦ hf.ne_zero (by
      rw [hfv, h0, Polynomial.map_zero, map_zero, zero_div])
    obtain ⟨⟨hS0, -⟩, -⟩ := CPoly.simplePart_props_map (algebraMap ℚ Kc) g.2 hGd0
    obtain ⟨hμ0, hμ⟩ := CPoly.muCheck_spec (CPoly.muCheck_findMu _ _ hS0)
    refine CPoly.rdeRationalW_complete (K := T.F 0) (algebraMap ℚ Kc) hDK
      (CPoly.normCoeff_den_ne_zero (R := ℚ) A) hGn0 hGd0 (CPoly.normCoeff_coprime _) hμ0 hμ
      (fun y' hy' ↦ (T.tr_noHom_of_ND 0 hnd).2 f hder hf y' (by rw [hfv]; exact hy')) hnone y ?_
    change y′ + T.ratF 0 f * y = T.model0.sem A at hy
    rw [show T.model0.sem A = _ from T.model0_sem_eq A, ← hn, hfv] at hy
    simp only [phi0] at hy
    exact hy
  | m + 1, hnd, f, hder, hf, A, y, hy => by
    obtain ⟨hm, hnh⟩ := T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))
    have htr : Transcendental (T.F m) (T.ts m) := (T.tr_noHom_of_ND (m + 1) hnd).1 m (by omega)
    simp only [rdeM]
    split_ifs with hz
    · simp
    have hA2 : GPoly.toPoly (T.MP m hm) A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff _ _).mpr h0)
    -- the solution is `Y / D`
    have hbd : ∀ b, kind ks m = .exp b → T.Adm b := fun b hk ↦ T.adm_of_kind hk
    have hyE : (y : E)′ + (T.ratF m f : E) * y =
        aeval (T.ts m) (GPoly.toPoly (T.MP m hm) A.1) / aeval (T.ts m) (GPoly.toPoly (T.MP m hm) A.2) := by
      have := congrArg Subtype.val hy
      rw [IntermediateField.coe_add, IntermediateField.coe_mul, coe_deriv] at this
      rw [show ((T.ratF m f : T.F m) : E) = ((T.ratF (m + 1) f : T.F (m + 1)) : E) from rfl, this]
      change ((T.phi m _ / T.phi m _ : T.F (m + 1)) : E) = _
      rw [IntermediateField.coe_div, coe_phi, coe_phi]
      rfl
    obtain ⟨Y, -, hYid⟩ := T.rde_denom m htr hnh f hder hf hbd _ _ hA2 (y : E) y.2 hyE
    have hP₀ : GPoly.toPoly (T.MP m hm) (GPoly.sub (opsM ks m)
        (GPoly.smul (opsM ks m) (lift m f) A.2) (GPoly.derivT (opsM ks m) (wK ks m) A.2)) =
        C (T.ratF m f) * GPoly.toPoly (T.MP m hm) A.2 -
          implicitDeriv (T.wPoly m) (GPoly.toPoly (T.MP m hm) A.2) := by
      rw [GPoly.toPoly_sub, GPoly.toPoly_smul, GPoly.toPoly_derivT, T.toPoly_wK, T.sem_lift_F m hm f]
    have hfuel : Y.natDegree < (GPoly.mul (opsM ks m) A.1 A.2).length + 1 := by
      by_cases hY0 : Y = 0
      · rw [hY0, natDegree_zero]; omega
      have h1 := T.rde_natDegree m hnh f hder hf hbd _ Y hA2 hY0
      rw [hYid] at h1
      have h2 := natDegree_toPoly_le (T.MP m hm) (GPoly.mul (opsM ks m) A.1 A.2)
      rw [GPoly.toPoly_mul] at h2
      omega
    have := T.rdeAux_complete m hm hnh
      (fun f' hd' hf' A' y' hy' ↦ rdeM_complete m (hnd.mono (Nat.le_succ m)) f' hd' hf' A' y' hy')
      f hder hf hbd A.2 _ hA2 hP₀ _ (GPoly.mul (opsM ks m) A.1 A.2) [] Y
      (by rw [hP₀, GPoly.toPoly_mul]; exact hYid) hfuel
    intro hnone
    have h0 := Option.map_eq_none_iff.mp hnone
    rw [h0] at this
    exact absurd this (by simp)

end MixTower

end Tower.MixN
