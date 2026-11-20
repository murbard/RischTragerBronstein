import RischTragerBronstein.Mixed.CurveModelMap
import RischTragerBronstein.Mixed.CurveOverConst
import RischTragerBronstein.Mixed.ExpGen

/-!
# The lift property for an exponential over a curve

Let `S` be a curve over `ℚ` in a differential field `K` whose constants lie in `Kc`, `F₀ = Kc(x, y)`
its function field, and `t = exp a` (`a` given by a curve code) transcendental over `F₀`.
**`curve_expLift`**: `F₀` has the lift property `ExpLift` for the right-hand sides given by curve
codes. In an elementary extension `E ⊇ K` with constants `Cc`, `F₁ = Cc(x, y)`:

* contains `F₀` (`curve_over_constants`) and is closed under the derivation;
* `t` stays transcendental over `F₁`. A non-zero solution of `b′ = n a′ b` in `F₁` would give,
  by completeness of the Risch solver over `Cc` (`curveRde_complete`), a non-zero solution
  returned by the solver, hence (soundness over `Kc`) one in `F₀`, so `tⁿ ∈ Kc F₀`;
* solutions of `y′ + m a′ y = f` in `F₁` descend to `F₀` in the same way.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Codes

/-- The code of the integer `m`. -/
def intCode (Fc : BPoly ℚ) (m : ℤ) : GPoly (GFrac ℚ) :=
  if 0 ≤ m then (curveOps Fc).natCast m.toNat else (curveOps Fc).neg ((curveOps Fc).natCast (-m).toNat)

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

lemma sem_intCode (m : ℤ) : (cM hC S hx Fc hSF).sem (intCode Fc m) = (m : E) := by
  unfold intCode
  split_ifs with hm
  · rw [CField.sem_natCast]
    exact_mod_cast Int.toNat_of_nonneg hm
  · rw [CField.sem_neg, CField.sem_natCast]
    have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    have h2 : (((-m).toNat : ℕ) : E) = ((-m : ℤ) : E) := by exact_mod_cast this
    rw [h2]; push_cast; ring

/-- The code of `m · a`. -/
def mulCode (Fc : BPoly ℚ) (m : ℤ) (a : GPoly (GFrac ℚ)) : GPoly (GFrac ℚ) :=
  (curveOps Fc).mul (intCode Fc m) a

lemma sem_mulCode (m : ℤ) (a : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (mulCode Fc m a) = (m : E) * (cM hC S hx Fc hSF).sem a := by
  rw [mulCode, CField.sem_mul, sem_intCode]

end Codes

section Lift

universe u

variable {Kc K : Type u} [Field Kc] [Field K] [Algebra Kc K] [Differential Kc] [Differential K]
variable [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc K) (hx : S.x′ = 1)
  (hconstK : ∀ z : K, z′ = 0 → z ∈ Set.range (algebraMap Kc K))
  (Fc : BPoly ℚ) (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))
  (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)

/-- The function field of the curve, over `Kc`. -/
noncomputable abbrev cF : IntermediateField Kc K := (Kc⟮S.x⟯⟮S.y⟯).restrictScalars Kc

include hC hx in
lemma cF_derivClosed : DerivClosed (cF S) := fun z hz ↦ S.derivClosedXY hC hx z hz

lemma sem_mem_cF (a : GPoly (GFrac ℚ)) : (cM hC S hx Fc hSF).sem a ∈ cF S :=
  sem_mem hC S hx Fc hSF a

lemma deriv_sem_mem_cF (a : GPoly (GFrac ℚ)) : ((cM hC S hx Fc hSF).sem a)′ ∈ cF S :=
  cF_derivClosed hC S hx _ (sem_mem_cF hC S hx Fc hSF a)

/-- The potential `a′` as an element of the function field. -/
noncomputable def etaF (a : GPoly (GFrac ℚ)) : cF S :=
  ⟨((cM hC S hx Fc hSF).sem a)′, deriv_sem_mem_cF hC S hx Fc hSF a⟩

/-- The right-hand sides with codes. -/
def CodeP (f : cF S) : Prop := ∃ q : GPoly (GFrac ℚ), (f : K) = (cM hC S hx Fc hSF).sem q

set_option maxHeartbeats 2000000 in
include hconstK hmon hdeg in
/-- **The lift property for an exponential over the curve.** -/
theorem curve_expLift (acode : GPoly (GFrac ℚ)) (t : K) (ht0 : t ≠ 0)
    (ht : t′ = ((cM hC S hx Fc hSF).sem acode)′ * t) (htr0 : Transcendental (cF S) t) :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    ExpLift (cF S) t (etaF hC S hx Fc hSF acode) (CodeP hC S hx Fc hSF) := by
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  intro E _ _ _ _ hE
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
  have hsem : ∀ a, (cM hCc SL hxL Fc hSFL).sem a = ψ (M.sem a) := fun a ↦
    sem_cM_map hC S hx Fc hSF hCc SL hxL hSFL ψ hSLx hSLy a
  set F₁ : IntermediateField (constants E) E := ((constants E)⟮SL.x⟯⟮SL.y⟯).restrictScalars (constants E) with hF₁
  have hcl : DerivClosed F₁ := fun z hz ↦ SL.derivClosedXY hCc hxL z hz
  have hψd : ∀ z : K, (ψ z)′ = ψ z′ := fun z ↦ deriv_algebraMap z
  -- the transferred equation
  have hsol : ∀ (m : ℤ) (ws : List (GPoly (GFrac ℚ))) (c : List (constants E)) (yE : E), yE ∈ F₁ →
      yE′ + ((m : E) * ψ (M.sem acode))′ * yE = ∑ j ∈ Finset.range ws.length,
        algebraMap (constants E) E (c.getD j 0) * ψ (M.sem (ws.getD j [])) →
      ∃ β : List (constants E),
        (∀ j < ws.length, c.getD j 0 = ∑ l ∈ Finset.range (curveRde Fc (mulCode Fc m acode) ws).length,
          β.getD l 0 * algebraMap ℚ (constants E)
            (((curveRde Fc (mulCode Fc m acode) ws).getD l ([], [])).1.getD j 0)) ∧
        yE = ∑ l ∈ Finset.range (curveRde Fc (mulCode Fc m acode) ws).length,
          algebraMap (constants E) E (β.getD l 0) *
            ψ (M.sem ((curveRde Fc (mulCode Fc m acode) ws).getD l ([], [])).2) := by
    intro m ws c yE hyF hyE
    obtain ⟨β, hβ1, hβ2⟩ := curveRde_complete hCc SL hxL Fc hSFL hmon hdeg (mulCode Fc m acode) ws c
      yE hyF (by
        simp only [hsem]
        rw [sem_mulCode, map_mul, map_intCast]
        exact hyE)
    exact ⟨β, hβ1, by rw [hβ2]; simp only [hsem]⟩
  have hmemL : ∀ (L : List (List ℚ × GPoly (GFrac ℚ))) (l : ℕ), l < L.length →
      L.getD l ([], []) ∈ L := fun L l hl ↦ by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  have hderivm : ∀ (m : ℤ) (z : K), ((m : K) * z)′ = (m : K) * z′ := fun m z ↦ by
    rw [Derivation.leibniz, Derivation.map_intCast]; simp
  have hderivmE : ∀ (m : ℤ) (z : E), ((m : E) * z)′ = (m : E) * z′ := fun m z ↦ by
    rw [Derivation.leibniz, Derivation.map_intCast]; simp
  refine ⟨F₁, hcl, fun f ↦ hmem f f.2, ?_, ?_⟩
  · -- transcendence of `t` over `F₁`
    letI : Differential F₁ := differentialOfDerivClosed hcl
    have hDA1 : DifferentialAlgebra F₁ E := differentialAlgebra_of_derivClosed hcl
    have hηF : ψ (M.sem acode)′ ∈ F₁ := hmem _ (deriv_sem_mem_cF hC S hx Fc hSF acode)
    refine transcendental_exponential (F := F₁) ⟨ψ (M.sem acode)′, hηF⟩
      ((map_ne_zero ψ).mpr ht0) (by rw [hψd, ht, map_mul]; rfl) fun n hn b hb ↦ ?_
    by_contra hb0
    have hbE : (b : E)′ = (n : E) * ψ (M.sem acode)′ * b := by
      have := congrArg (fun z : F₁ ↦ (z : E)) hb
      exact this.trans (by simp)
    set sols := curveRde Fc (mulCode Fc (-(n : ℤ)) acode) []
    obtain ⟨β, -, hβ⟩ := hsol (-(n : ℤ)) [] [] b b.2 (by
      simp only [List.length_nil, Finset.range_zero, Finset.sum_empty]
      rw [hderivmE, hψd, hbE]
      push_cast; ring)
    -- some returned solution is non-zero
    have hex : ∃ l ∈ Finset.range sols.length, M.sem (sols.getD l ([], [])).2 ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hb0
      apply Subtype.ext
      rw [hβ]
      exact Finset.sum_eq_zero fun l hl ↦ by rw [hall l hl, map_zero, mul_zero]
    obtain ⟨l, hl, hz0⟩ := hex
    set z0 := M.sem (sols.getD l ([], [])).2 with hz0def
    have hzs := curveRde_sound hC S hx Fc hSF (mulCode Fc (-(n : ℤ)) acode) []
      _ (hmemL sols l (Finset.mem_range.mp hl))
    simp only [List.length_nil, Finset.range_zero, Finset.sum_empty] at hzs
    rw [← hz0def, sem_mulCode, hderivm] at hzs
    -- `tⁿ / z0` is a constant
    have hq : (t ^ n / z0)′ = 0 := by
      rw [Derivation.leibniz_div, Derivation.leibniz_pow, ht]
      have : z0′ = (n : K) * (M.sem acode)′ * z0 := by push_cast at hzs; linear_combination hzs
      rw [this]
      simp only [smul_eq_mul]
      have hn1 : t ^ n = t ^ (n - 1) * t := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
      rw [hn1]
      field_simp
      ring
    obtain ⟨c, hc⟩ := hconstK _ hq
    have htn : t ^ n = algebraMap Kc K c * z0 := by
      rw [hc]; field_simp
    apply htr0
    have hw : algebraMap Kc K c * z0 ∈ cF S :=
      mul_mem ((cF S).algebraMap_mem c) (sem_mem_cF hC S hx Fc hSF _)
    refine ⟨X ^ n - Polynomial.C ⟨_, hw⟩, fun h0 ↦ ?_, ?_⟩
    · have := congrArg (fun P ↦ P.natDegree) h0
      simp only [natDegree_zero] at this
      rw [natDegree_sub_C, natDegree_X_pow] at this
      exact hn this
    · rw [map_sub, map_pow, aeval_X, aeval_C]
      change t ^ n - algebraMap Kc K c * z0 = 0
      rw [htn, sub_self]
  · -- the Risch equations descend
    intro m hm f ⟨q, hq⟩ ⟨yE, hyF, hyE⟩
    set sols := curveRde Fc (mulCode Fc m acode) [q]
    obtain ⟨β, hβ1, -⟩ := hsol m [q] [1] yE hyF (by
      simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
        map_one, one_mul]
      rw [hderivmE, hψd, ← hq]
      exact hyE)
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
    have hzs := curveRde_sound hC S hx Fc hSF (mulCode Fc m acode) [q]
      _ (hmemL sols l (Finset.mem_range.mp hl))
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton,
      List.getD_cons_zero] at hzs
    rw [← hz0def, ← hrdef, sem_mulCode, hderivm, ← hq] at hzs
    have hrK : (r : K) ≠ 0 := by exact_mod_cast hr0
    have hrmem : (r : K) ∈ cF S := by
      have := (cF S).algebraMap_mem (r : Kc)
      simpa using this
    refine ⟨⟨z0 / r, div_mem (sem_mem_cF hC S hx Fc hSF _) hrmem⟩, ?_⟩
    apply Subtype.ext
    change (z0 / r)′ + (m : K) * (M.sem acode)′ * (z0 / r) = (f : K)
    rw [Derivation.leibniz_div, show ((r : K))′ = 0 by
      rw [show (r : K) = algebraMap Kc K (r : Kc) by simp, deriv_algebraMap, hC, map_zero]]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp
    linear_combination hzs

end Lift

end Curves
