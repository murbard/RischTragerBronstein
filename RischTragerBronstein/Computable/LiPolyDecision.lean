import RischTragerBronstein.Computable.LiBaseFull

/-!
# Non-elementary nested primitives (`li x`-type): polynomials in `t₂` — decided

`integrateLiPoly`: the loop `prim2LoopW`, then the level-0 remainder `A₀ - W Q₁` goes to
`integrateLiBase`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- The integrator for `∑ₖ Aₖ t₂ ^ k`, `t₂′ = W`. -/
def integrateLiPoly (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (W : GFrac (GFrac R))
    (A : ℕ → GFrac (GFrac R)) (d₂ : ℕ) : Bool :=
  match prim2LoopW En₁ Ed₁ Iη₁ W A d₂ ([], [(ops₁g R).one]) with
  | none => false
  | some L =>
    let G := gCodeW En₁ Ed₁ W 0 (A 0) (lastGen ([], [(ops₁g R).one]) L)
    integrateLiBase En₁ Ed₁ Iη₁ W G

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **Non-elementary nested primitive, polynomial part: decided**, both directions. -/
theorem integrateLiPoly_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hrW : GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 = false)
    (hWnd : isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 = false)
    (hresW : GPoly.residueCheck (ops₁g R) [(En₁, Ed₁)]
      (GPoly.divMod (ops₁g R) (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
        (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s = false)
    (d₂ : ℕ) (A : ℕ → GFrac (GFrac R)) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valG x₀ t₁ (A k)) * t ^ k) ↔
      integrateLiPoly En₁ Ed₁ Iη₁ W A d₂ = true := by
  unfold integrateLiPoly
  cases hL : prim2LoopW En₁ Ed₁ Iη₁ W A d₂ ([], [(ops₁g R).one]) with
  | none =>
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨E, _, _, _, _, hE, g, hg⟩
    exact not_elementary_prim2PolyW hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ W t hgen ht Iη₁ hcη₁ hη₁0
      hW0 hrW hWnd d₂ A hL E hE g hg
  | some L =>
    simp only
    have hanti := prim2LoopW_antiderivative (K := K) hR x₀ t₁ hx₀ ht₁ W t ht hcη₁ hη₁0 A d₂ _ hL
    have hQ0 : valG x₀ t₁ (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by
      simp [valG, valP]
    rw [hQ0, map_zero, map_zero, zero_mul, zero_add] at hanti
    obtain ⟨hden, hval⟩ := valG_gCodeW_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hη₁0 W 0 (A 0)
      (lastGen ([], [(ops₁g R).one]) L)
    rw [hanti, hasElementaryIntegral_deriv_add_iff,
      ← integrateLiBase_decides (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ W t hgen ht Iη₁
        hcη₁ hη₁0 hW0 hWnd hresW _ hden, hval]
    simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]

end Tower
