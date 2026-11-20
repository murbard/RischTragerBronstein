import RischTragerBronstein.Computable.PrimHexpPolyDecision
import RischTragerBronstein.Computable.LiHexpBaseFull

/-!
# Non-elementary primitive over a general hyperexponential: polynomials in `t₂` with coefficients in
`R(x)(t₁)`

`integrateLiHexpPoly` runs the loop `primExpLoopW` and hands the level-0 remainder
`A₀ - W Q₁ ∈ R(x)(t₁)` to `integrateLiHexpBase`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly


section Decide

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- The integrator for `∑ₖ Aₖ t₂ ^ k`, `t₂′ = W ∈ R(x)(t₁)` non-elementary. -/
def integrateLiHexpPoly (Hn Hd μ : CPoly R) (W : GFrac (GFrac R))
    (A : ℕ → GFrac (GFrac R)) (d₂ : ℕ) : Bool :=
  match primHexpLoopW Hn Hd μ W A d₂ ([], [(ops₁g R).one]) with
  | none => false
  | some L =>
    integrateLiHexpBase Hn Hd μ W (gCodeH Hn Hd W 0 (A 0) (lastGen ([], [(ops₁g R).one]) L))

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]
variable [CPoly.HasRatRoots R] [HasNatTest R]

/-- **Non-elementary primitive over a general hyperexponential, polynomial part: decided**, both directions. -/
theorem integrateLiHexpPoly_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivHexp Hn Hd μ W.1 W.2 = false)
    (hresW : GPoly.residueCheck (ops₁g R) (hexpW Hn Hd) (hexpReduce Hn Hd W.1 W.2).r
      (hexpReduce Hn Hd W.1 W.2).s = false)
    (d₂ : ℕ) (A : ℕ → GFrac (GFrac R)) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valG x₀ t₁ (A k)) * t ^ k) ↔
      integrateLiHexpPoly Hn Hd μ W A d₂ = true := by
  unfold integrateLiHexpPoly
  cases hL : primHexpLoopW Hn Hd μ W A d₂ ([], [(ops₁g R).one]) with
  | none =>
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨E, _, _, _, _, hE, g, hg⟩
    exact not_elementary_primHexpPolyW hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ hgen₀ W t hgen ht
      hW0 hWnd d₂ A hL E hE g hg
  | some L =>
    simp only
    have hanti := primHexpLoopW_antiderivative (K := K) hR x₀ t₁ hx₀ hHn0 hHd0 hcop hcert ht₁0 ht₁ W t ht A d₂ _ hL
    have hQ0 : valG x₀ t₁ (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by
      simp [valG, valP]
    rw [hQ0, map_zero, map_zero, zero_mul, zero_add] at hanti
    obtain ⟨hden, hval⟩ := valG_gCodeH_F₀ hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ W 0 (A 0)
      (lastGen ([], [(ops₁g R).one]) L)
    rw [hanti, hasElementaryIntegral_deriv_add_iff,
      ← integrateLiHexpBase_decides (K := K) hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ hgen₀ W t hgen ht
        hW0 hWnd hresW _ hden, hval]
    simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]

end Tower
