import RischTragerBronstein.Computable.PrimExpPolyDecision
import RischTragerBronstein.Computable.LiExpBaseFull

/-!
# Non-elementary primitive over an exponential: polynomials in `t₂` with coefficients in
`R(x)(exp a₁)`

`integrateLiExpPoly` runs the loop `primExpLoopW` and hands the level-0 remainder
`A₀ - W Q₁ ∈ R(x)(exp a₁)` to `integrateLiExpBase`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly


section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- The integrator for `∑ₖ Aₖ t₂ ^ k`, `t₂′ = W ∈ R(x)(exp a)` non-elementary. -/
def integrateLiExpPoly (a : CPoly R) (W : GFrac (GFrac R))
    (A : ℕ → GFrac (GFrac R)) (d₂ : ℕ) : Bool :=
  match primExpLoopW a W A d₂ ([], [(ops₁g R).one]) with
  | none => false
  | some L =>
    integrateLiExpBase a W (gCodeE a W 0 (A 0) (lastGen ([], [(ops₁g R).one]) L))

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **Non-elementary primitive over an exponential, polynomial part: decided**, both directions. -/
theorem integrateLiExpPoly_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivExp a₁ W.1 W.2 = false)
    (hresW : GPoly.residueCheck (ops₁g R) (expW a₁) (expReduce a₁ W.1 W.2).r
      (expReduce a₁ W.1 W.2).s = false)
    (d₂ : ℕ) (A : ℕ → GFrac (GFrac R)) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valG x₀ t₁ (A k)) * t ^ k) ↔
      integrateLiExpPoly a₁ W A d₂ = true := by
  unfold integrateLiExpPoly
  cases hL : primExpLoopW a₁ W A d₂ ([], [(ops₁g R).one]) with
  | none =>
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨E, _, _, _, _, hE, g, hg⟩
    exact not_elementary_primExpPolyW hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ W t hgen ht
      hW0 hWnd d₂ A hL E hE g hg
  | some L =>
    simp only
    have hanti := primExpLoopW_antiderivative (K := K) hR x₀ t₁ hx₀ ha₁ ht₁0 ht₁ W t ht A d₂ _ hL
    have hQ0 : valG x₀ t₁ (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by
      simp [valG, valP]
    rw [hQ0, map_zero, map_zero, zero_mul, zero_add] at hanti
    obtain ⟨hden, hval⟩ := valG_gCodeE_F₀ hR x₀ t₁ hx₀ ha₁ ht₁0 ht₁ W 0 (A 0)
      (lastGen ([], [(ops₁g R).one]) L)
    rw [hanti, hasElementaryIntegral_deriv_add_iff,
      ← integrateLiExpBase_decides (K := K) hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ W t hgen ht
        hW0 hWnd hresW _ hden, hval]
    simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]

end Tower
