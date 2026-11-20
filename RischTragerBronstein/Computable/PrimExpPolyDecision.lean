import RischTragerBronstein.Computable.PrimExpLoopWPositive
import RischTragerBronstein.Computable.PrimExpBaseFull

/-!
# Log-type primitive over an exponential: polynomials in `t₂` with coefficients in `R(x)(exp a₁)`

`integratePrimExpPoly` runs the loop `primExpLoopW` (one limited integration problem with
parameter function `W = U′ / U` per power of `t₂`) and hands the level-0 remainder
`A₀ - W Q₁ ∈ R(x)(exp a₁)` to the height-two integrator `integrateExp`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section F0

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem valG_gCodeE_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {a : CPoly R} (ha : trim (deriv a) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a)) * t₁)
    (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GPoly.isZero (ops₁g R) (gCodeE a W k Ak Q).2 = false ∧
    valG x₀ t₁ (gCodeE a W k Ak Q) = valG x₀ t₁ Ak -
      ((k + 1 : ℕ) : F₀) * valG x₀ t₁ W * valG x₀ t₁ Q := by
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
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (derivative (toPoly a)) with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (derivative (toPoly a)) := hcoe _
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have hA'0 : derivative (toPoly a) ≠ 0 := fun h' ↦ ha ((trim_eq_nil_iff _).mpr (by
    rw [toPoly_deriv, h']))
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := R⟮x₀⟯) hD (-(C (n : R) * derivative (toPoly a)))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap R[X] R⟮x₀⟯ (C (n : R)) = (n : R⟮x₀⟯) := by
          rw [show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hηa : ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a = η₁' := by
    rw [ηa, Polynomial.map_id]
  have hD₂ : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (C (ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hM : ModelEW (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) a :=
    ModelEW.of (RingHom.id R) hD ha hD₂
  -- values of codes in `F₀`
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hsemG : ∀ q : GFrac (GFrac R),
      (((hM.cf (RingHom.id R) h0).sem q : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valG x₀ t₁ q := fun q ↦ by
    rw [ModelEW.cf, sem_M₂E, IntermediateField.coe_div, hvalP, hvalP, valG]
  obtain ⟨hden, hsem⟩ := sem_gCodeE (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hM W k Ak Q
  refine ⟨Bool.eq_false_iff.mpr fun hz ↦ hden ((GPoly.isZero_iff _ _).mp hz), ?_⟩
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsem
  have hnat : (((k + 1 : ℕ) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = ((k + 1 : ℕ) : F₀) := by
    rw [← map_natCast (algebraMap (R⟮x₀⟯)⟮t₁⟯ F₀)]; rfl
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsemG, hnat] at this
  exact this

end F0

section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- The integrator for `∑ₖ Aₖ t₂ ^ k`, `t₂′ = W ∈ R(x)(exp a)`. -/
def integratePrimExpPoly (a : CPoly R) (W : GFrac (GFrac R))
    (A : ℕ → GFrac (GFrac R)) (d₂ : ℕ) : Bool :=
  match primExpLoopW a W A d₂ ([], [(ops₁g R).one]) with
  | none => false
  | some L =>
    let G := gCodeE a W 0 (A 0) (lastGen ([], [(ops₁g R).one]) L)
    integrateExp a G.1 G.2

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **Log-type primitive over an exponential, polynomial part: decided**, both directions. -/
theorem integratePrimExpPoly_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W U : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivExp a₁ W.1 W.2 = false)
    (hU0 : (ops₂e a₁).isZero U = false)
    (hlog : (ops₂e a₁).isZero ((ops₂e a₁).add ((ops₂e a₁).mul W U)
      ((ops₂e a₁).neg ((ops₂e a₁).deriv U))) = true)
    (d₂ : ℕ) (A : ℕ → GFrac (GFrac R)) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valG x₀ t₁ (A k)) * t ^ k) ↔
      integratePrimExpPoly a₁ W A d₂ = true := by
  unfold integratePrimExpPoly
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
      ← primExpBaseGen_decides (K := K) hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ W U t hgen ht
        hW0 hWnd hU0 hlog _ _ hden, Prod.mk.eta, hval]
    simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]

end Tower
