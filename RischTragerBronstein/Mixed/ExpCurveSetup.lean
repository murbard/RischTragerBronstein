import RischTragerBronstein.Mixed.ExpCurveLift
import RischTragerBronstein.Mixed.CurveRosenlicht

/-!
# Setup for one exponential over a curve

* `CField.restrictTo`: a model valued in `L` whose values lie in a derivation-closed intermediate
  field `K'` is a model of `K'`;
* `curveIn`: the curve `S ⊆ K` seen inside its function field `cF S` (a differential field of its
  own), which it generates (`curveIn_gen`), so the decision on curves applies to it;
* `isElementaryExtension_exp`: `K = F₀(t)` with `t = exp a`, `a ∈ F₀`, is elementary over `F₀`.
-/

open Polynomial Differential IntermediateField

namespace CField

variable {α F L : Type*} [Field F] [Field L] [Algebra F L] [Differential L] {O : COps α}

/-- **A model valued in a derivation-closed subfield.** -/
noncomputable def restrictTo (M : CField α L O) (K' : IntermediateField F L) (hcl : DerivClosed K')
    (hmem : ∀ a, M.sem a ∈ K') :
    @CField α K' _ (differentialOfDerivClosed hcl) O :=
  letI := differentialOfDerivClosed hcl
  { sem := fun a ↦ ⟨M.sem a, hmem a⟩
    sem_zero := Subtype.ext M.sem_zero
    sem_one := Subtype.ext M.sem_one
    sem_add := fun a b ↦ Subtype.ext (M.sem_add a b)
    sem_neg := fun a ↦ Subtype.ext (M.sem_neg a)
    sem_mul := fun a b ↦ Subtype.ext (M.sem_mul a b)
    sem_inv := fun a ↦ Subtype.ext (M.sem_inv a)
    sem_deriv := fun a ↦ Subtype.ext (M.sem_deriv a)
    sem_natCast := fun n ↦ Subtype.ext (M.sem_natCast n)
    isZero_iff := fun a ↦ by
      rw [M.isZero_iff]
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩ }

lemma coe_sem_restrictTo (M : CField α L O) (K' : IntermediateField F L) (hcl : DerivClosed K')
    (hmem : ∀ a, M.sem a ∈ K') (a : α) :
    letI := differentialOfDerivClosed hcl
    (((M.restrictTo K' hcl hmem).sem a : K') : L) = M.sem a := rfl

end CField

section Elem

variable {F₀ K : Type*} [Field F₀] [Field K] [Algebra F₀ K] [Differential F₀] [Differential K]

/-- **An exponential generates an elementary extension.** -/
lemma isElementaryExtension_exp (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht0 : t ≠ 0) (a : K) (ha : a ∈ Set.range (algebraMap F₀ K)) (hlog : logDeriv t = a′) :
    IsElementaryExtension F₀ K := by
  have h := IsElementaryTower.adjoin (⊥ : IntermediateField F₀ K) t IsElementaryTower.base
    (Or.inr (Or.inr ⟨ht0, a, by obtain ⟨f, rfl⟩ := ha; exact IntermediateField.algebraMap_mem _ f,
      hlog⟩))
  unfold IsElementaryExtension
  rwa [hgen, bot_sup_eq] at h

end Elem

namespace Curves

open CPoly Sup

section Setup

universe u

variable {Kc K : Type u} [Field Kc] [Field K] [Algebra Kc K] [Differential Kc] [Differential K]
variable [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc K) (hx : S.x′ = 1)

/-- The generators inside the function field. -/
noncomputable def xIn : cF S :=
  ⟨S.x, (Kc⟮S.x⟯⟮S.y⟯).algebraMap_mem ⟨S.x, mem_adjoin_simple_self Kc S.x⟩⟩

noncomputable def yIn : cF S := ⟨S.y, mem_adjoin_simple_self _ S.y⟩

omit [Differential Kc] [Differential K] [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K] in
/-- Evaluation commutes with the inclusion of the function field. -/
lemma coe_evalIn (G : Kc[X][X]) :
    (((G.map (aeval (xIn S)).toRingHom).eval (yIn S) : cF S) : K) = S.evXY G := by
  have h1 : (cF S).val.toRingHom.comp (aeval (R := Kc) (xIn S)).toRingHom =
      (aeval (R := Kc) S.x).toRingHom := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp
    · simp [xIn]
  change (cF S).val.toRingHom _ = _
  rw [eval_map, Polynomial.hom_eval₂]
  erw [h1]
  rw [CurveData.evXY, eval_map]
  rfl

/-- The curve inside its function field. -/
noncomputable def curveIn : CurveData Kc (cF S) where
  x := xIn S
  y := yIn S
  F := S.F
  htr := fun ⟨p, hp0, hp⟩ ↦ S.htr ⟨p, hp0, by
    have := congrArg (cF S).val hp
    rwa [← Polynomial.aeval_algHom_apply, map_zero] at this⟩
  monic := S.monic
  irr := fun G hG hG0 ↦ S.irr G hG (by
    have := congrArg (fun z : cF S ↦ (z : K)) hG0
    rwa [coe_evalIn, ZeroMemClass.coe_zero] at this)
  root := Subtype.ext (by rw [coe_evalIn, ZeroMemClass.coe_zero]; exact S.root)

lemma curveIn_x : (curveIn S).x = xIn S := rfl
lemma curveIn_y : (curveIn S).y = yIn S := rfl
lemma curveIn_F : (curveIn S).F = S.F := rfl

omit [Differential Kc] [Differential K] [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K] in
/-- **The curve generates its function field.** -/
lemma curveIn_gen (z : cF S) : z ∈ Kc⟮(curveIn S).x⟯⟮(curveIn S).y⟯ := by
  have hz := z.2
  change (z : K) ∈ Kc⟮S.x⟯⟮S.y⟯ at hz
  rw [← IntermediateField.mem_restrictScalars Kc, adjoin_simple_adjoin_simple] at hz ⊢
  have hmap : (Kc⟮(curveIn S).x, (curveIn S).y⟯).map (cF S).val = Kc⟮S.x, S.y⟯ := by
    rw [IntermediateField.adjoin_map]
    congr 1
    ext w
    simp [curveIn, xIn, yIn, Set.image_insert_eq]
  rw [← hmap] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rwa [show w = z from Subtype.ext hwz] at hw

lemma curveIn_hx :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    (curveIn S).x′ = 1 := Subtype.ext hx

lemma cF_diffAlg :
    letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
    DifferentialAlgebra Kc (cF S) :=
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  ⟨fun c ↦ Subtype.ext (deriv_algebraMap c)⟩

end Setup

section Ascend

universe u

variable {Kc K : Type u} [Field Kc] [Field K] [Algebra Kc K] [Differential Kc] [Differential K]
variable [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K] [IsAlgClosed Kc]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc K) (hx : S.x′ = 1)
  (Fc : BPoly ℚ) (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

set_option maxHeartbeats 1000000 in
/-- **Ascent of the constant term**: an element of the function field with an elementary integral
over `K = F₀(t)` (`t = exp a`) is an explicit Liouville form over `F₀`, hence has an elementary
integral over every extension of `K`. -/
theorem ascend_const (acode : GPoly (GFrac ℚ)) (t : K) (ht0 : t ≠ 0)
    (ht : t′ = ((cM hC S hx Fc hSF).sem acode)′ * t)
    (hgen : adjoin (cF S) {t} = (⊤ : IntermediateField (cF S) K))
    (P0 : CurveProb ℚ) (hS0 : P0.shapeOK = true) (hFc : P0.Fc = Fc)
    (Λ : K) (hΛ : Λ = S.evXY ((toB P0.A).map (mapRingHom (algebraMap ℚ Kc))) /
      aeval S.x ((toPoly P0.D).map (algebraMap ℚ Kc)))
    (hΛel : HasElementaryIntegral Λ) : HasElementaryIntegralIn Λ := by
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  haveI hDA : DifferentialAlgebra (cF S) K := differentialAlgebra_of_derivClosed _
  haveI hDAc : DifferentialAlgebra Kc (cF S) := cF_diffAlg hC S hx
  haveI : CharZero (cF S) := ⟨fun m n h ↦ by
    have := congrArg (fun z : cF S ↦ (z : K)) h
    simpa using this⟩
  have hSF0 : (curveIn S).F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc)) := by
    rw [curveIn_F, hSF, hFc]
  set M := cM hC S hx Fc hSF
  -- the constant term inside the function field
  have hmemΛ : Λ ∈ cF S := by
    rw [hΛ]; exact div_mem (S.evXY_mem _) (S.aeval_mem _)
  set Λ0 : cF S := ⟨Λ, hmemΛ⟩
  have hΛ0 : ((((curveIn S).fE P0 (algebraMap ℚ Kc) : Kc⟮(curveIn S).x⟯⟮(curveIn S).y⟯)) : cF S)
      = Λ0 := by
    apply Subtype.ext
    change ((CurveData.evXY (curveIn S) _ / aeval (curveIn S).x _ : cF S) : K) = Λ
    rw [IntermediateField.coe_div, CurveData.evXY, curveIn_x, curveIn_y, coe_evalIn, hΛ]
    congr 1
    change (cF S).val (aeval (xIn S) _) = _
    rw [← Polynomial.aeval_algHom_apply]
    rfl
  -- descent to the function field
  have hE := isElementaryExtension_exp (F₀ := cF S) t hgen ht0 (M.sem acode)
    ⟨⟨_, sem_mem_cF hC S hx Fc hSF acode⟩, rfl⟩ (by rw [logDeriv, ht, mul_div_assoc, div_self ht0,
      mul_one])
  have h0 : HasElementaryIntegral Λ0 := HasElementaryIntegral.of_extension hE hΛel
  rw [← hΛ0] at h0
  have hL := curve_liouvilleForm hC (curveIn S) (curveIn_hx hC S hx) (curveIn_gen S) P0 hS0 hSF0 h0
  rw [hΛ0] at hL
  exact (hL.map (algebraMap (cF S) K) fun z ↦ deriv_algebraMap z).hasElementaryIntegralIn

end Ascend

end Curves
