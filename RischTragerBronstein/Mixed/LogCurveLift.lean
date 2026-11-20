import RischTragerBronstein.Mixed.LogCurveDecide

/-!
# The lift for a logarithm over a curve

Let `S` be a curve over `ℚ` in a differential field `K` whose constants lie in `Kc`, `F₀ = Kc(x, y)`
its function field, and `t ∈ K` with `t′ = η` (`η` a curve code, e.g. `u′ / u`) transcendental
over `F₀`. **`curve_primLift`**: in every extension `E ⊇ K` with constants `Cc`, the field
`F₁ = Cc(x, y)`

* contains `F₀`, is closed under the derivation, and `t` stays transcendental over it: a solution
  of `y′ = η` in `F₁` would give, by completeness of the Risch solver over `Cc`
  (`curveRde_complete`), one returned by the solver, hence (soundness over `Kc`) one in `F₀`, so
  `t ∈ F₀`;
* every solution in `F₁` of the recurrence `pᵢ′ + (i + 1) η pᵢ₊₁ = aᵢ` (`1 ≤ i ≤ d`, `p_{d+1}`
  constant) makes the chain `primChain` succeed, with `p₁ − Q₁` constant (`primChain_complete`).
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Lift

universe u

variable {Kc K : Type u} [Field Kc] [Field K] [Algebra Kc K] [Differential Kc] [Differential K]
variable [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc K) (hx : S.x′ = 1)
  (hconstK : ∀ z : K, z′ = 0 → z ∈ Set.range (algebraMap Kc K))
  (Fc : BPoly ℚ) (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))
  (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)

set_option maxHeartbeats 2000000 in
include hconstK hmon hdeg in
/-- **The lift for a primitive over the curve.** -/
theorem curve_primLift (ηc : GPoly (GFrac ℚ)) (t : K)
    (ht : t′ = (cM hC S hx Fc hSF).sem ηc) (htr0 : Transcendental (cF S) t)
    (E : Type u) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E] :
    ∃ F₁ : IntermediateField (constants E) E, DerivClosed F₁ ∧
      (∀ f ∈ cF S, algebraMap K E f ∈ F₁) ∧ Transcendental F₁ (algebraMap K E t) ∧
      ∀ (Λ : GPoly (GPoly (GFrac ℚ))) (d : ℕ) (p : ℕ → E), (∀ i, p i ∈ F₁) →
        (∀ i, 1 ≤ i → i ≤ d → (p i)′ + ((i + 1 : ℕ) : E) *
          algebraMap K E ((cM hC S hx Fc hSF).sem ηc) * p (i + 1) =
            algebraMap K E ((cM hC S hx Fc hSF).sem (Λ.getD i (curveOps Fc).zero))) →
        (p (d + 1))′ = 0 →
        ∃ R, primChain Fc ηc Λ d (curveOps Fc).zero = some R ∧
          ∃ κ : E, κ′ = 0 ∧ p 1 = algebraMap K E ((cM hC S hx Fc hSF).sem R) + κ := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨φ, SL, hxL, hSLx, hSLy, hSLF, hφ, hmem⟩ := curve_over_constants hC S hx hconstK E
  letI : Differential (constants E) := ⟨0⟩
  haveI hDAc : DifferentialAlgebra (constants E) E := ⟨fun c ↦ c.2⟩
  have hCc : ∀ c : (constants E), c′ = 0 := fun _ ↦ rfl
  haveI hcharC : CharZero (constants E) := ⟨fun a b h ↦ by
    have := congrArg (fun z : (constants E) ↦ (z : E)) h
    simpa using this⟩
  have hSFL : SL.F = (toB Fc).map (mapRingHom (algebraMap ℚ (constants E))) := by
    rw [hSLF, hSF, Polynomial.map_map, mapRingHom_comp]
    congr 2
    exact RingHom.ext_rat _ _
  set ψ := algebraMap K E with hψ
  set M := cM hC S hx Fc hSF with hM
  set ML := cM hCc SL hxL Fc hSFL with hML
  have hsem : ∀ a, ML.sem a = ψ (M.sem a) := fun a ↦
    sem_cM_map hC S hx Fc hSF hCc SL hxL hSFL ψ hSLx hSLy a
  set F₁ : IntermediateField (constants E) E :=
    ((constants E)⟮SL.x⟯⟮SL.y⟯).restrictScalars (constants E) with hF₁
  have hcl : DerivClosed F₁ := fun z hz ↦ SL.derivClosedXY hCc hxL z hz
  have hψd : ∀ z : K, (ψ z)′ = ψ z′ := fun z ↦ deriv_algebraMap z
  have hmemL : ∀ (L : List (List ℚ × GPoly (GFrac ℚ))) (l : ℕ), l < L.length →
      L.getD l ([], []) ∈ L := fun L l hl ↦ by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  -- `η` is not a derivative in `F₁`
  have hnex0 : ∀ y ∈ F₁, y′ ≠ ψ (M.sem ηc) := by
    intro y hy hy'
    set sols := curveRde Fc (curveOps Fc).zero [ηc] with hsols
    obtain ⟨β, hβ1, -⟩ := curveRde_complete hCc SL hxL Fc hSFL hmon hdeg (curveOps Fc).zero [ηc]
      [1] y hy (by
        simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton,
          List.getD_cons_zero, map_one, one_mul]
        rw [ML.sem_zero, Derivation.map_zero, zero_mul, add_zero, hsem, hy'])
    have h1 := hβ1 0 (by simp)
    simp only [List.getD_cons_zero] at h1
    have hex : ∃ l ∈ Finset.range sols.length, (sols.getD l ([], [])).1.getD 0 0 ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_eq_zero fun l hl ↦ by rw [hall l hl, map_zero, mul_zero]] at h1
      exact one_ne_zero h1
    obtain ⟨l, hl, hr0⟩ := hex
    set r : ℚ := (sols.getD l ([], [])).1.getD 0 0 with hrdef
    set z0 := M.sem (sols.getD l ([], [])).2 with hz0def
    have hzs := curveRde_sound hC S hx Fc hSF (curveOps Fc).zero [ηc]
      _ (hmemL sols l (Finset.mem_range.mp hl))
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton,
      List.getD_cons_zero] at hzs
    rw [← hz0def, ← hrdef, M.sem_zero, Derivation.map_zero, zero_mul, add_zero] at hzs
    have hrK : (r : K) ≠ 0 := by exact_mod_cast hr0
    have hq : (t - z0 / r)′ = 0 := by
      rw [Derivation.map_sub, Derivation.leibniz_div, deriv_ratCast' hC, ht, hzs]
      simp only [smul_eq_mul, mul_zero, sub_zero]
      field_simp
      ring
    obtain ⟨c, hc⟩ := hconstK _ hq
    have htmem : t ∈ cF S := by
      have h2 : t = algebraMap Kc K c + z0 / r := by rw [hc]; ring
      rw [h2]
      exact add_mem ((cF S).algebraMap_mem c)
        (div_mem (sem_mem_cF hC S hx Fc hSF _) (ratCast_mem S r))
    apply htr0
    exact isAlgebraic_algebraMap (R := cF S) (⟨t, htmem⟩ : cF S)
  -- transcendence over `F₁`
  have htrE : Transcendental F₁ (ψ t) := by
    letI : Differential F₁ := differentialOfDerivClosed hcl
    have hDA1 : DifferentialAlgebra F₁ E := differentialAlgebra_of_derivClosed hcl
    have hηF : ψ (M.sem ηc) ∈ F₁ := hmem _ (sem_mem hC S hx Fc hSF ηc)
    refine transcendental_primitive (F := F₁) ⟨_, hηF⟩ (by rw [hψd, ht]; rfl) fun b hb ↦
      hnex0 b b.2 ?_
    have := congrArg (fun z : F₁ ↦ (z : E)) hb
    exact this
  refine ⟨F₁, hcl, fun f hf ↦ hmem f hf, htrE, ?_⟩
  intro Λ d p hp hrec htop
  have hconstL : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap (constants E) E) :=
    fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩
  have hnexL : ∀ y ∈ (constants E)⟮SL.x⟯⟮SL.y⟯, ∀ κ : constants E,
      y′ = algebraMap (constants E) E κ * ML.sem ηc → κ = 0 := by
    intro y hy κ hyκ
    by_contra hκ0
    have hκE : (κ : E) ≠ 0 := fun h ↦ hκ0 (Subtype.ext h)
    refine hnex0 (y / κ) (div_mem hy (F₁.algebraMap_mem κ)) ?_
    rw [Derivation.leibniz_div, show (κ : E)′ = 0 from κ.2, hyκ, hsem]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    rw [show algebraMap (constants E) E κ = (κ : E) from rfl]
    field_simp
  obtain ⟨R, hR, κ, hκ⟩ := primChain_complete hCc SL hxL Fc hSFL hmon hdeg hconstL ηc Λ hnexL p hp
    d (fun i h1 h2 ↦ by rw [hsem, hsem]; exact hrec i h1 h2) (curveOps Fc).zero
    ⟨⟨p (d + 1), htop⟩, by rw [ML.sem_zero, zero_add]; rfl⟩
  exact ⟨R, hR, (κ : E), κ.2, by rw [hκ, hsem]; rfl⟩

end Lift

end Curves
