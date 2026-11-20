import RischTragerBronstein.Computable.ExpExpLaurentStrong
import RischTragerBronstein.Computable.ExpPrimLaurentPositive

/-!
# Two exponentials: the Laurent part is integrated by `rdeExp`
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

/-- `valP` of a code with its powers of `t₁` split off. -/
theorem valP_splitX (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0) (x₀ t₁ : F₀) (hx₀ : x₀′ = 1)
    (D : GPoly (GFrac R)) :
    valP x₀ t₁ D = t₁ ^ (GPoly.splitX (ops₁g R) D).1 * valP x₀ t₁ (GPoly.splitX (ops₁g R) D).2 := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- level one: `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDA' : DifferentialAlgebra R⟮x₀⟯ F₀ :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hchar1 : CharZero R⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap R R⟮x₀⟯).injective
  have hD : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have := congrArg (fun P : (R⟮x₀⟯)[X] ↦ ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ P : (R⟮x₀⟯)⟮t₁⟯) : F₀))
    (GPoly.toPoly_splitX (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) D)
  simp only [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hvalP] at this
  rw [this, algebraMap_adjoinSimple, aeval_X]

/-- The `t₁`-free part of a non-zero denominator is non-zero. -/
theorem isZero_splitX_false (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0) (x₀ : F₀) (hx₀ : x₀′ = 1)
    (D : GPoly (GFrac R)) (hDz : GPoly.isZero (ops₁g R) D = false) :
    GPoly.isZero (ops₁g R) (GPoly.splitX (ops₁g R) D).2 = false := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- level one: `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDA' : DifferentialAlgebra R⟮x₀⟯ F₀ :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hchar1 : CharZero R⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap R R⟮x₀⟯).injective
  have hD : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set M₁ := M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD with hM₁
  have hD' : GPoly.toPoly M₁ D ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff M₁ D).mpr hz] at hDz
    exact Bool.noConfusion hDz
  refine Bool.eq_false_iff.mpr fun hz ↦ hD' ?_
  rw [GPoly.toPoly_splitX M₁ D, (GPoly.isZero_iff M₁ _).mp hz, mul_zero]

variable {K : Type*} [Field K] [Algebra F₀ K] [Differential K] [DifferentialAlgebra F₀ K]

/-- **The Laurent part is integrated** (two exponentials). -/
theorem expExpLaurent_antiderivative (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (a : CPoly R) (t : K) (ht0 : t ≠ 0)
    (ht : t′ = algebraMap F₀ K (aeval x₀ (derivative (toPoly a))) * t)
    (N n : ℕ) (A : ℕ → GFrac (GFrac R)) (Y : ℕ → GPoly (GFrac R))
    (hD0 : ∀ j < N, GPoly.isZero (ops₁g R) (A j).2 = false)
    (hsome : ∀ j < N, j ≠ n → rdeExp a₁ (expCoeffZ a ((j : ℤ) - n)) (A j).1
      (GPoly.splitX (ops₁g R) (A j).2).2 (GPoly.splitX (ops₁g R) (A j).2).1 = some (Y j)) :
    (∑ j ∈ (Finset.range N).erase n,
        algebraMap F₀ K (valP x₀ t₁ (Y j) / valP x₀ t₁ (A j).2) * t ^ j / t ^ n)′ =
      ∑ j ∈ (Finset.range N).erase n, algebraMap F₀ K (valG x₀ t₁ (A j)) * t ^ j / t ^ n := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap F₀ K).injective
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  obtain ⟨hjn, hjN⟩ := Finset.mem_erase.mp hj
  have hjN' := Finset.mem_range.mp hjN
  have hsp0 : GPoly.isZero (ops₁g R) (GPoly.splitX (ops₁g R) (A j).2).2 = false :=
    isZero_splitX_false hR x₀ hx₀ _ (hD0 j hjN')
  have hsol := rdeExp_sound_F₀ hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ _ _ _ _ hsp0 (hsome j hjN' hjn)
  rw [← valP_splitX hR x₀ t₁ hx₀ (A j).2] at hsol
  have hg : aeval x₀ (toPoly (expCoeffZ a ((j : ℤ) - n))) =
      ((j : F₀) - n) * aeval x₀ (derivative (toPoly a)) := by
    rw [expCoeffZ, toPoly_smul, toPoly_deriv, map_mul, aeval_C]
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
  rw [hg] at hsol
  rw [deriv_mul_pow_div_pow _ t _ ht0 ht, valG, ← map_natCast (algebraMap F₀ K) j,
    ← map_natCast (algebraMap F₀ K) n, ← map_sub, ← map_mul, deriv_algebraMap, ← map_mul,
    ← map_add, hsol]

end Tower
