import RischTragerBronstein.Computable.PrimHexpResidueW
import RischTragerBronstein.Computable.PrimHexpPolyDecision

/-!
# Log-type primitive over an exponential `t₂ = log U`, `U ∈ R(x)(exp a₁)`: the combined decision

`K = R(x)(t₁)(t₂)`, `t₁ = exp a₁`. For an integrand in Hermite-reduced form at the top step,

  `f = g′ + ∑_{k ≤ d₂} Aₖ(x, t₁) t₂ ^ k + b(t₂) / sd(t₂)`,

`Aₖ ∈ R(x)(t₁)` arbitrary (fraction codes), `sd ∈ R(x)(t₁)[t₂]` squarefree, `deg b < deg sd`:

`f` has an elementary integral **iff** the residue test passes and `integratePrimHexpPoly` succeeds.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]
variable [CPoly.HasRatRoots R] [HasNatTest R]

theorem primHexpFull_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W U : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (Tower.valG x₀ t₁ W))
    (hW0 : GPoly.isZero (Tower.ops₁g R) W.2 = false)
    (hWnd : Tower.isDerivHexp Hn Hd μ W.1 W.2 = false)
    (hU0 : (Tower.ops₂h Hn Hd).isZero U = false)
    (hlog : (Tower.ops₂h Hn Hd).isZero ((Tower.ops₂h Hn Hd).add ((Tower.ops₂h Hn Hd).mul W U)
      ((Tower.ops₂h Hn Hd).neg ((Tower.ops₂h Hn Hd).deriv U))) = true)
    (g : K) (d₂ : ℕ) (A : ℕ → GFrac (GFrac R))
    (b sd r : F₀[X]) (hsd : Squarefree sd) (hdeg : b.degree < sd.degree)
    (hst : aeval t sd ≠ 0)
    (hr : sd ∣ r * (mapCoeffs sd +
      C (Tower.valG x₀ t₁ W) * derivative sd) - b) :
    HasElementaryIntegral (g′ + ∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (Tower.valG x₀ t₁ (A k)) * t ^ k + aeval t b / aeval t sd) ↔
      sd ∣ residueTest r sd ∧ Tower.integratePrimHexpPoly Hn Hd μ W A d₂ = true := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  set Asum : K := ∑ k ∈ Finset.range (d₂ + 1), algebraMap F₀ K (Tower.valG x₀ t₁ (A k)) * t ^ k
    with hAsum
  set Ap : F₀[X] := ∑ k ∈ Finset.range (d₂ + 1), C (Tower.valG x₀ t₁ (A k)) * X ^ k with hAp
  have hApv : aeval t Ap = Asum := by
    simp only [hAp, hAsum, map_sum, map_mul, map_pow, aeval_C, aeval_X]
  set η₀ : F₀ := Tower.valG x₀ t₁ W with hη₀
  have hlogIn : sd ∣ residueTest r sd → HasElementaryIntegralIn (aeval t b / aeval t sd) :=
    fun hT ↦ hasElementaryIntegralIn_of_residueTest t η₀ 0
      (by rw [ht, map_zero, zero_mul, add_zero]) 1 one_ne_zero (by rw [logDeriv_one, map_zero])
      sd b r (PerfectField.separable_iff_squarefree.mpr hsd) hst hdeg
      (by rwa [C_0, zero_mul, add_zero]) hT
  have hpoly := Tower.integratePrimHexpPoly_decides (K := K) hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ hgen₀ W U
    t hgen ht hW0 hWnd hU0 hlog d₂ A
  constructor
  · intro hf
    have h1 : HasElementaryIntegral (Asum + aeval t b / aeval t sd) := by
      have := hf.sub_in (hasElementaryIntegralIn_deriv g)
      have heq : g′ + Asum + aeval t b / aeval t sd - g′ = Asum + aeval t b / aeval t sd := by
        ring
      rwa [heq] at this
    have hT : sd ∣ residueTest r sd := by
      by_contra hT
      have hr' : sd ∣ r * (mapCoeffs sd + C η₀ * derivative sd) - (Ap * sd + b) := by
        have : r * (mapCoeffs sd + C η₀ * derivative sd) - (Ap * sd + b) =
            (r * (mapCoeffs sd + C η₀ * derivative sd) - b) - Ap * sd := by ring
        rw [this]
        exact dvd_sub hr (dvd_mul_left sd Ap)
      have h1' : HasElementaryIntegral (aeval t (Ap * sd + b) / aeval t sd) := by
        rw [map_add, map_mul, add_div, mul_div_assoc, div_self hst, mul_one, hApv]
        exact h1
      obtain ⟨E, _, _, _, _, hE, g', hg'⟩ := h1'
      exact not_elementary_primHexpResidueW hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ hgen₀ W t hgen ht
        hW0 hWnd (Ap * sd + b) sd r hsd hr' hT E hE g' hg'
    refine ⟨hT, hpoly.mp ?_⟩
    have := h1.sub_in (hlogIn hT)
    rwa [add_sub_cancel_right] at this
  · rintro ⟨hT, hsome⟩
    have hA' : HasElementaryIntegral Asum := hpoly.mpr hsome
    have := ((hA'.add_in (hlogIn hT)).add_in (hasElementaryIntegralIn_deriv g))
    have heq : g′ + Asum + aeval t b / aeval t sd = Asum + aeval t b / aeval t sd + g′ := by
      ring
    rwa [heq]

end CPoly
