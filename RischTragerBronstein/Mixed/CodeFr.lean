import RischTragerBronstein.Mixed.CurveRdeSem
import RischTragerBronstein.Mixed.EllCompute2

/-!
# Level-0 codes as executable fractions (step 2)

A level-0 code `a = ∑ qᵢ Yⁱ` (`GPoly (GFrac ℚ)`) has value `∑ qᵢ(x) yⁱ` (`sem_cM`). Given an
executable fraction `yF` for `y` (for a linear base curve `y` is a polynomial in `x`), `codeFr yF a`
is an executable fraction over `ℚ(X)` whose image under `ψ : ℚ(X) → E`, `X ↦ x`, is the value of
the code (`codeFr_spec`). This turns the decider's codes into inputs of the height certificate.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup FFHeight

section CodeFr

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

/-- The evaluation `ℚ[X] → E`, `X ↦ x`. -/
noncomputable def evx : ℚ[X] →+* E :=
  (aeval (R := Kc) S.x).toRingHom.comp (mapRingHom (algebraMap ℚ Kc))

lemma evx_injective : Function.Injective (evx S) := by
  intro p q h
  by_contra hne
  have h0 : p - q ≠ 0 := sub_ne_zero.mpr hne
  apply S.htr
  refine ⟨(p - q).map (algebraMap ℚ Kc), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr h0
  · have : evx S (p - q) = 0 := by rw [map_sub, h, sub_self]
    simpa [evx] using this

/-- **`ψ : ℚ(X) → E`**, `X ↦ x`. -/
noncomputable def psiX : RatFunc ℚ →+* E :=
  RatFunc.liftRingHom (evx S) (fun p hp ↦ by
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    have := nonZeroDivisors.ne_zero hp
    exact (map_ne_zero_iff _ (evx_injective S)).mpr this)

lemma psiX_val (f : Fr ℚ) (hf : Fr.ok f) :
    psiX S (Fr.val f) = evx S (CPoly.toPoly f.1) / evx S (CPoly.toPoly f.2) := by
  rw [Fr.val, psiX, RatFunc.liftRingHom_apply_div]

/-- The executable fraction of a code (Horner in `y`). -/
def codeFr (yF : Fr ℚ) : GPoly (GFrac ℚ) → Fr ℚ
  | [] => Fr.ofPoly []
  | q :: a => Fr.add (q.1, q.2) (Fr.mul yF (codeFr yF a))

lemma codeFr_ok (yF : Fr ℚ) (hy : Fr.ok yF) :
    ∀ a : GPoly (GFrac ℚ), (∀ q ∈ a, CPoly.toPoly q.2 ≠ 0) → Fr.ok (codeFr yF a)
  | [], _ => Fr.ok_ofPoly _
  | q :: a, h => Fr.ok_add (h q List.mem_cons_self)
      (Fr.ok_mul hy (codeFr_ok yF hy a fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq')))

/-- **The executable fraction has the value of the code.** -/
theorem codeFr_spec (yF : Fr ℚ) (hyok : Fr.ok yF) (hy : psiX S (Fr.val yF) = S.y) :
    ∀ a : GPoly (GFrac ℚ), (∀ q ∈ a, CPoly.toPoly q.2 ≠ 0) →
      psiX S (Fr.val (codeFr yF a)) = (cM hC S hx Fc hSF).sem a
  | [], _ => by
    rw [sem_cM]; simp [codeFr, Fr.val_ofPoly, CPoly.toPoly]
  | q :: a, h => by
    have hq : CPoly.toPoly q.2 ≠ 0 := h q List.mem_cons_self
    have ha : ∀ q' ∈ a, CPoly.toPoly q'.2 ≠ 0 := fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq')
    have ih := codeFr_spec yF hyok hy a ha
    have hok := codeFr_ok yF hyok a ha
    rw [sem_cM] at ih ⊢
    rw [codeFr, Fr.val_add hq (Fr.ok_mul hyok hok), Fr.val_mul hyok hok, map_add, map_mul, ih, hy,
      GPoly.toPoly_cons, eval_add, eval_C, eval_mul, eval_X, psiX_val S (q.1, q.2) hq]
    rw [sem_xModel]
    simp only [evx, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, coe_mapRingHom]

include hSF in
/-- **`y` on a linear base curve** `Fc = [c₀, [1]]` (`y + c₀(x) = 0`). -/
theorem y_linear (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) :
    psiX S (Fr.val (CPoly.neg c0, [1])) = S.y := by
  have hroot := S.root
  rw [hSF, hFc] at hroot
  simp only [toB_cons, toB_nil, mul_zero, add_zero, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, eval_add, eval_C, eval_mul, eval_X] at hroot
  rw [psiX_val S _ (by simp [Fr.ok, CPoly.toPoly])]
  simp only [CPoly.toPoly_neg, CPoly.toPoly_cons, CPoly.toPoly_nil, mul_zero, add_zero, map_one,
    div_one, map_neg, evx, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, coe_mapRingHom] at hroot ⊢
  linear_combination -hroot

end CodeFr

end Curves
