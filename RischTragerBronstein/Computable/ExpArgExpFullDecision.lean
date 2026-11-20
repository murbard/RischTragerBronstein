import RischTragerBronstein.Computable.ExpArgExpResidue
import RischTragerBronstein.Computable.ExpArgExpBaseFull
import RischTragerBronstein.Computable.ExpArgExpLaurentPositive
import RischTragerBronstein.Computable.ExpExpFullDecision

/-!
# Two exponentials: the combined decision

`K = R(x)(t₁)(t₂)`, `t₂ = exp a(x)`. For an integrand in Hermite-reduced form at `t₂`,

  `f = g′ + (A₀ + ∑_{j ≠ n} Aⱼ t₂^j / t₂^n) + b(t₂) / sd(t₂)`,

`Aⱼ ∈ R(x)(t₁)` (fraction codes), `sd` squarefree and prime to `t₂`, `deg b < deg sd`:
`f` has an elementary integral **iff** the residue test passes, every Risch differential equation
`y′ + (j - n) a′ y = Aⱼ` is solvable in `R(x)(t₁)` (`rdeNCExp`), and `integrateExp` accepts `A₀`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [HasNatTest R]
variable [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

set_option maxHeartbeats 1600000 in
theorem expArgExpFull_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (a : GPoly (GFrac R))
    (hηc : 2 ≤ (GPoly.trim (Tower.ops₁g R) (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)).length)
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K
      (Tower.valP x₀ t₁ (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)) * t)
    (g : K) (N n : ℕ) (A : ℕ → GFrac (GFrac R))
    (hD0 : ∀ j < N, GPoly.isZero (Tower.ops₁g R) (A j).2 = false)
    (A₀ : GFrac (GFrac R)) (hA₀ : GPoly.isZero (Tower.ops₁g R) A₀.2 = false)
    (b sd r : F₀[X]) (hsd : Squarefree sd) (hX : ¬X ∣ sd) (hdeg : b.degree < sd.degree)
    (hst : aeval t sd ≠ 0)
    (hr : sd ∣ r * (mapCoeffs sd +
      C (Tower.valP x₀ t₁ (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)) * X * derivative sd) - b) :
    HasElementaryIntegral (g′ +
        (algebraMap F₀ K (Tower.valG x₀ t₁ A₀) + ∑ j ∈ (Finset.range N).erase n,
          algebraMap F₀ K (Tower.valG x₀ t₁ (A j)) * t ^ j / t ^ n) +
        aeval t b / aeval t sd) ↔
      sd ∣ residueTest r sd ∧ (∀ j < N, j ≠ n →
        (Tower.rdeNCExpB a₁ (GPoly.smul (Tower.ops₁g R) (Tower.constZ ((j : ℤ) - n)) (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)) (A j).1 (A j).2).isSome = true) ∧
        Tower.integrateExp a₁ A₀.1 A₀.2 = true := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  set Lsum : K := algebraMap F₀ K (Tower.valG x₀ t₁ A₀) + ∑ j ∈ (Finset.range N).erase n,
    algebraMap F₀ K (Tower.valG x₀ t₁ (A j)) * t ^ j / t ^ n with hLsum
  set Λ : F₀[X] := C (Tower.valG x₀ t₁ A₀) * X ^ n +
    ∑ j ∈ (Finset.range N).erase n, C (Tower.valG x₀ t₁ (A j)) * X ^ j with hΛ
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht0
  have hΛv : aeval t Λ / t ^ n = Lsum := by
    simp only [hΛ, hLsum, map_add, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    rw [add_div, Finset.sum_div, mul_div_assoc, div_self htn, mul_one]
  set η₀ : F₀ := Tower.valP x₀ t₁ (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a) with hη₀
  have hlogIn : sd ∣ residueTest r sd → HasElementaryIntegralIn (aeval t b / aeval t sd) :=
    fun hT ↦ hasElementaryIntegralIn_of_residueTest t 0 η₀
      (by rw [ht, map_zero, zero_add]) t ht0
      (by rw [logDeriv, ht, mul_div_assoc, div_self ht0, mul_one])
      sd b r (PerfectField.separable_iff_squarefree.mpr hsd) hst hdeg
      (by rwa [C_0, zero_add]) hT
  have hbase := expArgExpBaseGen_decides (K := K) hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ a hηc t ht0
    hgen ht A₀.1 A₀.2 hA₀
  rw [Prod.mk.eta] at hbase
  constructor
  · intro hf
    have h1 : HasElementaryIntegral (Lsum + aeval t b / aeval t sd) := by
      have := hf.sub_in (hasElementaryIntegralIn_deriv g)
      have heq : g′ + Lsum + aeval t b / aeval t sd - g′ = Lsum + aeval t b / aeval t sd := by
        ring
      rwa [heq] at this
    have hT : sd ∣ residueTest r sd := by
      by_contra hT
      obtain ⟨E, _, _, _, _, hE, g', hg'⟩ := h1
      refine not_elementary_expArgExpResidue hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ a hηc t ht0 hgen
        ht (Λ * sd + b * X ^ n) b sd r n hsd hX ⟨Λ, by ring⟩ hr hT E hE g' ?_
      have : aeval t (Λ * sd + b * X ^ n) / (aeval t sd * t ^ n) =
          aeval t Λ / t ^ n + aeval t b / aeval t sd := by
        rw [map_add, map_mul, map_mul, map_pow, aeval_X]
        field_simp
      rw [this, hΛv]
      exact hg'
    have h2 : HasElementaryIntegral Lsum := by
      have := h1.sub_in (hlogIn hT)
      rwa [add_sub_cancel_right] at this
    refine ⟨hT, fun j hj hjn ↦ ?_, ?_⟩
    · by_contra hnone
      rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
      obtain ⟨E, _, _, _, _, hE, g', hg'⟩ := h2
      exact not_elementary_expArgExpLaurent hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a) hηc t ht0 hgen
        ht N n A _ hD0 j hj hjn hnone E hE g' hg'
    · -- the level-0 part: subtract the Laurent part, which is a derivative
      have hYG : ∀ j, ∃ Y : GPoly (GFrac R), j < N → j ≠ n →
          Tower.rdeNCExpB a₁ (GPoly.smul (Tower.ops₁g R) (Tower.constZ ((j : ℤ) - n)) (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)) (A j).1 (A j).2 =
              some Y := fun j ↦ by
        by_cases h : j < N ∧ j ≠ n
        · by_cases hs : (Tower.rdeNCExpB a₁ (GPoly.smul (Tower.ops₁g R) (Tower.constZ ((j : ℤ) - n)) (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)) (A j).1 (A j).2).isSome
          · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
            exact ⟨p, fun _ _ ↦ hp⟩
          · exfalso
            rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hs
            obtain ⟨E, _, _, _, _, hE, g', hg'⟩ := h2
            exact not_elementary_expArgExpLaurent hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a) hηc t ht0
              hgen ht N n A _ hD0 j h.1 h.2 hs E hE g' hg'
        · exact ⟨[], fun h1 h2 ↦ absurd ⟨h1, h2⟩ h⟩
      choose Y hYG using hYG
      have hW := Tower.expArgExpLaurent_antiderivative hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a) t ht0 ht N n A Y
        hD0 hYG
      rw [← hbase]
      have := h2.sub_in (hasElementaryIntegralIn_deriv (∑ j ∈ (Finset.range N).erase n,
        algebraMap F₀ K (Tower.valP x₀ t₁ (Y j) / (t₁ ^ Tower.specialBound a₁ (Tower.normFrac
          (GPoly.coeffAt (Tower.ops₁g R) (GPoly.smul (Tower.ops₁g R) (Tower.constZ ((j : ℤ) - n))
            (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)) 0))
          (GPoly.splitX (Tower.ops₁g R) (A j).2).1 *
          Tower.valP x₀ t₁ (GPoly.splitX (Tower.ops₁g R) (A j).2).2)) * t ^ j / t ^ n))
      rw [hW, hLsum, add_sub_cancel_right] at this
      exact this
  · rintro ⟨hT, hsome, hbase'⟩
    have hYG : ∀ j, ∃ Y : GPoly (GFrac R), j < N → j ≠ n →
        Tower.rdeNCExpB a₁ (GPoly.smul (Tower.ops₁g R) (Tower.constZ ((j : ℤ) - n)) (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a)) (A j).1 (A j).2 =
            some Y := fun j ↦ by
      by_cases h : j < N ∧ j ≠ n
      · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hsome j h.1 h.2)
        exact ⟨p, fun _ _ ↦ hp⟩
      · exact ⟨[], fun h1 h2 ↦ absurd ⟨h1, h2⟩ h⟩
    choose Y hYG using hYG
    have hW := Tower.expArgExpLaurent_antiderivative hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ (GPoly.derivT (Tower.ops₁g R) (Tower.expW a₁) a) t ht0 ht N n A Y
      hD0 hYG
    have hL : HasElementaryIntegral Lsum := by
      rw [hLsum, ← hW]
      exact (hbase.mpr hbase').add_in (hasElementaryIntegralIn_deriv _)
    have := ((hL.add_in (hlogIn hT)).add_in (hasElementaryIntegralIn_deriv g))
    have heq : g′ + Lsum + aeval t b / aeval t sd = Lsum + aeval t b / aeval t sd + g′ := by
      ring
    rwa [heq]

end CPoly
